"""Finite Enum and scalar Struct owners with guarded atomic transitions."""

import ast
from dataclasses import dataclass
import hashlib
import json

from ..errors import ElaborationError
from ..registry import ComponentDefinition


class FSM:
    """Base marker for source declarations, never a Python state machine."""

    def __new__(cls, *args, **kwargs):
        raise TypeError('FSM is a hardware source construct; use arch_primitives.elaborate')


class FSMError(ElaborationError):
    """Invalid graph or unsupported state-machine source use."""


class Pattern:
    """Compile-time partial state predicate, consumed by the elaborator."""

    def __new__(cls, *args, **kwargs):
        raise TypeError('FSM definitions are hardware source constructs; use arch_primitives.elaborate')


class Edge(Pattern):
    """Compile-time state relation with an explicit write permission set."""


class Next(Pattern):
    """Partial next-state update; omitted fields hold their current value."""


def fail(node, message):
    raise FSMError(f"line {getattr(node, 'lineno', '?')}: {message}")


@dataclass(frozen=True)
class FSMConfiguration:
    declaration: str
    state_type: str
    width: int
    states: tuple
    initial: str
    edges: tuple

    @property
    def name(self):
        digest = hashlib.sha256(json.dumps(self.__dict__, sort_keys=True).encode()).hexdigest()[:10]
        return 'FSM_' + self.declaration + '_' + digest

    def manifest(self):
        reached = {self.initial}
        while True:
            expanded = reached | {target for source, target in self.edges if source in reached}
            if expanded == reached:
                break
            reached = expanded
        return {**self.__dict__, 'specialization': self.name,
                'unreachable': [name for name, _ in self.states if name not in reached],
                'terminal': [name for name, _ in self.states
                             if not any(source == name for source, _ in self.edges)],
                'state_observation': 'Module-scope committed snapshot', 'calls': []}


def enum_members(node):
    encoding = [item for item in node.decorator_list if isinstance(item, ast.Call)
                and isinstance(item.func, ast.Attribute) and isinstance(item.func.value, ast.Name)
                and item.func.value.id == 'ac' and item.func.attr == 'encoding']
    if len(encoding) != 1 or encoding[0].args or len(encoding[0].keywords) != 1:
        fail(node, 'FSM state Enum requires @ac.encoding(width=literal)')
    keyword = encoding[0].keywords[0]
    if (keyword.arg != 'width' or not isinstance(keyword.value, ast.Constant)
            or type(keyword.value.value) is not int or keyword.value.value < 1):
        fail(node, 'FSM encoding width must be a positive integer literal')
    width, members = keyword.value.value, []
    for statement in node.body:
        if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Constant) and isinstance(statement.value.value, str):
            continue
        if (not isinstance(statement, ast.Assign) or len(statement.targets) != 1
                or not isinstance(statement.targets[0], ast.Name)
                or not isinstance(statement.value, ast.Constant) or type(statement.value.value) is not int):
            fail(statement, 'FSM state Enum requires explicit integer members')
        name, value = statement.targets[0].id, statement.value.value
        if name.startswith('_') or not 0 <= value < (1 << width):
            fail(statement, 'FSM state encoding is outside its declared width')
        if name in {item[0] for item in members} or value in {item[1] for item in members}:
            fail(statement, 'FSM state names and encodings must be unique')
        members.append((name, value))
    if not members:
        fail(node, 'FSM state Enum must not be empty')
    return width, tuple(members)


def prepare_fsm(markers, body, *, helpers=None):
    enums = {node.name: node for node in body if isinstance(node, ast.ClassDef)
             and any(isinstance(base, ast.Name) and base.id == 'Enum' for base in node.bases)}
    definitions, remaining = {}, []
    for node in body:
        if not (isinstance(node, ast.ClassDef) and any(isinstance(base, ast.Name) and base.id in markers
                                                     for base in node.bases)):
            remaining.append(node)
            continue
        if len(node.bases) != 1 or node.decorator_list or node.keywords or node.name in definitions:
            fail(node, 'FSM declarations require one FSM base and no decorators or class options')
        fields = {}
        for statement in node.body:
            if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Constant) and isinstance(statement.value.value, str):
                continue
            if (not isinstance(statement, ast.Assign) or len(statement.targets) != 1
                    or not isinstance(statement.targets[0], ast.Name)):
                fail(statement, 'FSM declarations contain only state_type, initial and edges')
            key = statement.targets[0].id
            if key in fields:
                fail(statement, 'invalid or duplicate FSM declaration member: ' + key)
            fields[key] = statement.value
        if not {'state_type', 'initial', 'edges'} <= fields.keys():
            fail(node, 'FSM requires state_type, initial and edges')
        state_type = fields['state_type']
        if isinstance(state_type, ast.Name) and state_type.id not in enums:
            from .fsm_composite import prepare_composite
            definitions[node.name] = prepare_composite(node, body, enums, helpers or {})
            continue
        if set(fields) != {'state_type', 'initial', 'edges'}:
            fail(node, 'invalid FSM declaration member')
        if not isinstance(state_type, ast.Name) or state_type.id not in enums:
            fail(state_type, 'FSM state_type must name a local explicitly encoded Enum')
        width, members = enum_members(enums[state_type.id])

        def member(value):
            if (not isinstance(value, ast.Attribute) or not isinstance(value.value, ast.Name)
                    or value.value.id != state_type.id or value.attr not in dict(members)):
                fail(value, 'FSM initial and edge endpoints must be members of ' + state_type.id)
            return value.attr

        initial = member(fields['initial'])
        edge_nodes = fields['edges']
        if not isinstance(edge_nodes, (ast.Tuple, ast.List)):
            fail(edge_nodes, 'FSM edges must be a static sequence of (source, target) pairs')
        edges = []
        for edge in edge_nodes.elts:
            if not isinstance(edge, (ast.Tuple, ast.List)) or len(edge.elts) != 2:
                fail(edge, 'FSM edge requires exactly one source and one target')
            pair = tuple(member(value) for value in edge.elts)
            if pair in edges:
                fail(edge, 'duplicate FSM edge: ' + ' -> '.join(pair))
            edges.append(pair)
        definitions[node.name] = FSMConfiguration(node.name, state_type.id, width, members, initial, tuple(edges))
    if not definitions:
        raise FSMError('FSM import requires at least one class declaration derived from FSM')
    return remaining, {'definitions': definitions, 'helpers': helpers or {}}


def fsm_definition(config):
    from .fsm_composite import CompositeConfiguration, composite_definition
    if isinstance(config, CompositeConfiguration):
        return composite_definition(config)
    state_type = config.state_type
    lines = ['@ac.module', f'def {config.name}():',
             f'    phase: {state_type} = {state_type}.{config.initial}',
             '    snapshot = phase']
    for target, _ in config.states:
        sources = [source for source, destination in config.edges if destination == target]
        condition = ' or '.join(f'snapshot == {state_type}.{source}' for source in sources) or 'False'
        lines += ['', f'    @ac.method(guard=lambda: {condition})',
                  f'    def to_{target}() -> None:', f'        phase = {state_type}.{target}']
    lines += ['', '    @ac.method', f'    def state() -> {state_type}:',
              '        return snapshot']
    return ast.parse('\n'.join(lines) + '\n').body


class FSMLowerer(ast.NodeTransformer):
    def __init__(self, markers, specializations, instances, statements, *, definitions, helpers=None):
        self.markers, self.specializations, self.instances = markers, specializations, instances
        self.definitions = definitions
        self.helpers = helpers or {}
        self.statements = statements
        self.module_statements = {id(node) for node in statements}
        self.bindings, self.records = {}, {}
        self.callable = []
        self.query_preludes = []
        self.used_names = {node.id for statement in statements for node in ast.walk(statement)
                            if isinstance(node, ast.Name)}
        self.used_names.update(node.arg for statement in statements for node in ast.walk(statement)
                                if isinstance(node, ast.arg))
        self.used_names.update(node.name for statement in statements for node in ast.walk(statement)
                                if isinstance(node, (ast.FunctionDef, ast.ClassDef)))
        self.statement_call = False

    def construction(self, node):
        return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in self.definitions

    def visit_Assign(self, node):
        if self.construction(node.value):
            if (id(node) not in self.module_statements or len(node.targets) != 1
                    or not isinstance(node.targets[0], ast.Name) or node.value.args or node.value.keywords):
                fail(node, 'FSM instance requires a direct, no-argument Module-body assignment')
            name = node.targets[0].id
            if name in self.bindings:
                fail(node, 'FSM instances cannot be rebound')
            config = self.definitions[node.value.func.id]
            self.bindings[name] = config
            self.specializations.setdefault(config, fsm_definition(config))
            record = {'instance': name, 'line': node.lineno, **config.manifest()}
            self.instances.append(record)
            self.records[name] = record
            node.value = ast.copy_location(ast.Call(func=ast.Name(id=config.name, ctx=ast.Load()), args=[], keywords=[]), node.value)
            return node
        return self.generic_visit(node)

    def visit_Name(self, node):
        if node.id in self.bindings:
            fail(node, 'FSM instance cannot escape, be aliased, rebound or used as raw state; call state()')
        return node

    def visit_arg(self, node):
        if node.arg in self.bindings:
            fail(node, 'FSM instance cannot be shadowed by a parameter')
        return node

    def visit_FunctionDef(self, node):
        for value in [*node.decorator_list, *node.args.defaults, *node.args.kw_defaults]:
            if value is not None and any(isinstance(item, ast.Name) and item.id in self.bindings
                                         for item in ast.walk(value)):
                fail(value, 'FSM access in decorators or default arguments is not supported')
        for argument in [*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs]:
            self.visit_arg(argument)
        for argument in (node.args.vararg, node.args.kwarg):
            if argument is not None:
                self.visit_arg(argument)
        self.callable.append(node.name)
        self.query_preludes.append([])
        node.body = [self.visit(statement) for statement in node.body]
        node.body = self.query_preludes.pop() + node.body
        self.callable.pop()
        return node

    def visit_Expr(self, node):
        previous = self.statement_call
        self.statement_call = True
        node.value = self.visit(node.value)
        self.statement_call = previous
        return node

    def visit_Attribute(self, node):
        if isinstance(node.value, ast.Name) and node.value.id in self.bindings:
            fail(node, 'FSM exposes only calls to transition(target_state) and state()')
        return self.generic_visit(node)

    def visit_Call(self, node):
        if self.construction(node) or isinstance(node.func, ast.Name) and node.func.id in self.markers:
            fail(node, 'FSM construction requires a declared class and a Module-body assignment')
        if not (isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name)
                and node.func.value.id in self.bindings):
            previous = self.statement_call
            self.statement_call = False
            result = self.generic_visit(node)
            self.statement_call = previous
            return result
        name, method = node.func.value.id, node.func.attr
        config = self.bindings[name]
        if not self.callable:
            fail(node, 'FSM methods must be used inside a Rule or Method')
        if method == 'state' and not node.args and not node.keywords:
            self.records[name]['calls'].append({'method': 'state', 'line': node.lineno, 'caller': self.callable[-1]})
            return node
        from .fsm_composite import CompositeConfiguration, lower_composite_call
        if isinstance(config, CompositeConfiguration):
            return lower_composite_call(self, node, name, method, config)
        if method != 'transition' or len(node.args) != 1 or node.keywords:
            fail(node, 'FSM provides state() and transition(target_state) only')
        if not self.statement_call:
            fail(node, 'FSM transition returns None and must be a standalone statement')
        target = node.args[0]
        if (not isinstance(target, ast.Attribute) or not isinstance(target.value, ast.Name)
                or target.value.id != config.state_type or target.attr not in dict(config.states)):
            fail(target, 'FSM target must be a static member of ' + config.state_type)
        self.records[name]['calls'].append({'method': 'transition', 'target': target.attr,
                                           'line': node.lineno, 'caller': self.callable[-1]})
        return ast.copy_location(ast.Call(func=ast.Attribute(value=ast.Name(id=name, ctx=ast.Load()),
                                                             attr='to_' + target.attr, ctx=ast.Load()), args=[], keywords=[]), node)

    def finalize(self):
        functions = {}
        for statement in self.statements:
            for node in ast.walk(statement):
                if isinstance(node, ast.FunctionDef):
                    if node.name in functions:
                        fail(node, 'FSM call analysis requires distinct local callable names')
                    functions[node.name] = node
        cache, active = {}, set()

        def add(left, right):
            return {key: left.get(key, 0) + right.get(key, 0) for key in left.keys() | right.keys()}

        def expression(node):
            result = {}
            if isinstance(node, ast.Call):
                if (isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name)
                        and node.func.value.id in self.bindings and node.func.attr.startswith('to_')):
                    result[node.func.value.id] = 1
                elif isinstance(node.func, ast.Name) and node.func.id in functions:
                    result = summarize(node.func.id)
            for child in ast.iter_child_nodes(node):
                result = add(result, expression(child))
            return result

        def block(statements):
            result = {}
            for node in statements:
                if isinstance(node, ast.FunctionDef):
                    continue
                if isinstance(node, ast.If):
                    left, right = block(node.body), block(node.orelse)
                    counts = add(expression(node.test), {key: max(left.get(key, 0), right.get(key, 0))
                                                        for key in left.keys() | right.keys()})
                elif isinstance(node, (ast.For, ast.While, ast.Try, ast.With, ast.Match)):
                    counts = expression(node)
                    if counts:
                        fail(node, 'FSM transitions in loops, try, with or match are not supported')
                else:
                    counts = expression(node)
                result = add(result, counts)
                if any(count > 1 for count in result.values()):
                    fail(node, 'at most one FSM transition per instance on each Rule/Method path, including helper calls')
            return result

        def summarize(name):
            if name in active:
                fail(functions[name], 'recursive FSM callable graph is not supported')
            if name not in cache:
                active.add(name)
                cache[name] = block(functions[name].body)
                active.remove(name)
            return cache[name]

        for name in functions:
            summarize(name)
        for node in ast.walk(ast.Module(body=self.statements, type_ignores=[])):
            if isinstance(node, ast.FunctionDef):
                for value in [*node.decorator_list, *node.args.defaults, *node.args.kw_defaults]:
                    if value is not None and expression(value):
                        fail(value, 'FSM-effect helpers cannot be used in decorators or default arguments')
            for child in ast.iter_child_nodes(node):
                if (isinstance(child, ast.Name) and child.id in cache and cache[child.id]
                        and not (isinstance(node, ast.Call) and child is node.func)):
                    fail(child, 'FSM-effect helpers must be called directly, without aliases or escaping')
            if isinstance(node, (ast.Lambda, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)) and expression(node):
                fail(node, 'FSM-effect helpers in lambdas or comprehensions are not supported')


FSM_COMPONENT = ComponentDefinition(name='FSM', module=__name__, lowerer=FSMLowerer,
                                    prepare=prepare_fsm, helpers=('Pattern', 'Edge', 'Next'))
