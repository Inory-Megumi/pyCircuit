"""Finite scalar Struct FSMs lowered to guarded native methods.

Predicates are parsed without executing author code. No scheduling certificate,
priority, or concurrency workaround is inserted by this pass.
"""

import ast
import copy
from dataclasses import dataclass
import hashlib
import json

from .fsm import enum_members, fail


def expression(text):
    return ast.parse(text, mode='eval').body


def conjunction(nodes):
    return ast.BoolOp(op=ast.And(), values=nodes) if len(nodes) > 1 else nodes[0] if nodes else ast.Constant(True)


def fold_static_guard(node, enums):
    """Fold closed Enum comparisons and dominating Boolean constants only.

    Do not infer runtime knownness (x == x need not be true), fold untyped
    integer arithmetic, or remove identity operands that could change Z to X.
    """
    def member(item):
        if isinstance(item, ast.Attribute) and isinstance(item.value, ast.Name):
            owner = item.value.id
            if owner in enums and item.attr in dict(enums[owner][1]):
                return owner, dict(enums[owner][1])[item.attr]
        return None

    class Fold(ast.NodeTransformer):
        def visit_Compare(self, item):
            item = self.generic_visit(item)
            if len(item.ops) == 1 and isinstance(item.ops[0], (ast.Eq, ast.NotEq)):
                left, right = member(item.left), member(item.comparators[0])
                if left is not None and right is not None and left[0] == right[0]:
                    equal = left[1] == right[1]
                    return ast.Constant(equal if isinstance(item.ops[0], ast.Eq) else not equal)
            return item

        def visit_BoolOp(self, item):
            item = self.generic_visit(item)
            constants = [part.value for part in item.values
                         if isinstance(part, ast.Constant) and type(part.value) is bool]
            dominant = isinstance(item.op, ast.Or)
            if dominant in constants:
                return ast.Constant(dominant)
            if len(constants) == len(item.values):
                return ast.Constant(not dominant)
            return item

    return Fold().visit(copy.deepcopy(node))


def keywords(node):
    values = {}
    for item in node.keywords:
        if item.arg is None or item.arg in values:
            fail(item, 'explicit, unique FSM keyword names are required')
        values[item.arg] = item.value
    return values


def validate_predicate(node, parameters, fields, enums):
    allowed = (ast.Expression, ast.BoolOp, ast.BinOp, ast.UnaryOp, ast.Compare, ast.IfExp,
                ast.Constant, ast.Attribute, ast.Name, ast.Load, ast.operator, ast.unaryop,
                ast.boolop, ast.cmpop)
    for item in ast.walk(node):
        if not isinstance(item, allowed):
            fail(item, 'FSM predicates support pure scalar expressions without calls or indexing')
        if isinstance(item, ast.Constant) and type(item.value) not in (int, bool):
            fail(item, 'FSM predicate constants must be integers or Boolean')
        if isinstance(item, ast.Attribute):
            if not isinstance(item.value, ast.Name):
                fail(item, 'FSM predicate fields must be direct scalar fields')
            owner = item.value.id
            if owner in parameters:
                if item.attr not in fields:
                    fail(item, 'unknown FSM predicate field: ' + item.attr)
            elif owner not in enums or item.attr not in dict(enums[owner][1]):
                fail(item, 'unknown FSM predicate Enum member')
        if isinstance(item, ast.Name) and item.id not in parameters and item.id not in enums:
            fail(item, 'FSM predicate cannot capture external names: ' + item.id)
    for parent in ast.walk(node):
        for child in ast.iter_child_nodes(parent):
            if isinstance(child, ast.Name) and not (isinstance(parent, ast.Attribute) and parent.value is child):
                fail(child, 'FSM predicates must reference a field or an Enum member')


def lambda_body(node, arity, fields, enums, canonical):
    if (not isinstance(node, ast.Lambda) or len(node.args.args) != arity or node.args.posonlyargs
            or node.args.kwonlyargs or node.args.defaults or node.args.vararg or node.args.kwarg):
        fail(node, 'FSM relation requires a pure lambda with ' + str(arity) + ' positional parameters')
    names = [item.arg for item in node.args.args]
    if len(set(names)) != arity or any(name in enums for name in names):
        fail(node, 'FSM lambda parameters must be distinct and not shadow Enum types')
    validate_predicate(node.body, names, fields, enums)
    return substitute(node.body, {name: {field: expression(f'{new}.{field}') for field in fields}
                                    for name, new in zip(names, canonical)})


def substitute(node, records):
    class Replace(ast.NodeTransformer):
        def visit_Attribute(self, item):
            if isinstance(item.value, ast.Name) and item.value.id in records:
                return copy.deepcopy(records[item.value.id][item.attr])
            return self.generic_visit(item)
    return Replace().visit(copy.deepcopy(node))


def literal(node, field, enums, *, required):
    name, annotation, width, enum = field
    if enum:
        if (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name)
                and node.value.id == enum and node.attr in dict(enums[enum][1])):
            return True
        if required or isinstance(node, ast.Constant) or (isinstance(node, ast.Attribute)
                and isinstance(node.value, ast.Name) and node.value.id in enums):
            fail(node, 'field ' + name + ' requires a member of ' + enum)
        return False
    if isinstance(node, ast.Constant) and type(node.value) in (int, bool):
        if not 0 <= int(node.value) < 2 ** width:
            fail(node, 'FSM literal is outside field width: ' + name)
        return True
    if required:
        fail(node, 'FSM initial/pattern fields require static typed literals')
    return False


@dataclass(frozen=True)
class CompositeConfiguration:
    declaration: str
    state_type: str
    fields: tuple
    initial: tuple
    patterns: tuple
    edges: tuple
    enums: tuple

    @property
    def name(self):
        digest = hashlib.sha256(json.dumps(self.__dict__, sort_keys=True).encode()).hexdigest()[:10]
        return 'FSM_' + self.declaration + '_' + digest

    def manifest(self):
        patterns = []
        for name, parent, predicate in self.patterns:
            reads = sorted({item.attr for item in ast.walk(expression(predicate)) if isinstance(item, ast.Attribute)
                            and isinstance(item.value, ast.Name) and item.value.id == 'q'})
            patterns.append({'name': name, 'parent': parent, 'predicate': predicate, 'read_fields': reads})
        return {'declaration': self.declaration, 'specialization': self.name, 'state_type': self.state_type,
                'kind': 'scalar-struct', 'fields': [dict(zip(('name', 'type', 'width', 'enum'), field))
                                                    for field in self.fields],
                'initial': dict(self.initial), 'patterns': patterns,
                'edges': [{'source': s, 'target': t, 'writes': list(w), 'guard': g} for s, t, w, g in self.edges],
                'state_observation': 'Module-scope committed field snapshots',
                'storage': 'one Struct state owner; every transition writes a complete candidate',
                'calls': [], 'analysis': 'native guards and write conflict checks; no compound graph proof'}


def prepare_composite(declaration, body, enum_nodes, helpers):
    definitions = {}
    for item in declaration.body:
        if isinstance(item, ast.Expr) and isinstance(item.value, ast.Constant) and isinstance(item.value.value, str):
            continue
        if not isinstance(item, ast.Assign) or len(item.targets) != 1 or not isinstance(item.targets[0], ast.Name):
            fail(item, 'Struct FSM declarations contain assignments only')
        name = item.targets[0].id
        if name in definitions:
            fail(item, 'duplicate FSM declaration member: ' + name)
        definitions[name] = item.value
    if not {'state_type', 'initial', 'edges'} <= definitions.keys():
        fail(declaration, 'FSM requires state_type, initial and edges')
    state_name = definitions['state_type'].id
    structs = {item.name: item for item in body if isinstance(item, ast.ClassDef) and any(
        ast.unparse(decorator) == 'ac.struct' for decorator in item.decorator_list)}
    if state_name not in structs:
        fail(definitions['state_type'], 'FSM state_type must name a local encoded Enum or scalar ac.struct')
    enums = {name: enum_members(node) for name, node in enum_nodes.items()}
    fields = []
    struct = structs[state_name]
    if struct.bases or struct.keywords:
        fail(struct, 'FSM state Struct cannot inherit or have class keywords')
    for item in struct.body:
        if isinstance(item, ast.Expr) and isinstance(item.value, ast.Constant) and isinstance(item.value.value, str):
            continue
        if not isinstance(item, ast.AnnAssign) or not isinstance(item.target, ast.Name) or item.value is not None:
            fail(item, 'FSM state Struct requires scalar annotated fields without defaults')
        field, annotation, enum, width = item.target.id, ast.unparse(item.annotation), '', 0
        if isinstance(item.annotation, ast.Name) and item.annotation.id in enums:
            enum = item.annotation.id
            width = enums[enum][0]
        elif (isinstance(item.annotation, ast.Attribute) and isinstance(item.annotation.value, ast.Name)
                and item.annotation.value.id == 'ac' and item.annotation.attr.startswith('u')
                and item.annotation.attr[1:].isdigit()):
            width = int(item.annotation.attr[1:])
        elif (isinstance(item.annotation, ast.Subscript) and ast.unparse(item.annotation.value) == 'ac.bits'
                and isinstance(item.annotation.slice, ast.Constant) and type(item.annotation.slice.value) is int):
            width = item.annotation.slice.value
        if not 1 <= width <= 64 or field.startswith('_') or field in {row[0] for row in fields}:
            fail(item, 'FSM fields must be unique 1..64-bit unsigned scalars or encoded Enums')
        fields.append((field, annotation, width, enum))
    if not fields:
        fail(struct, 'FSM state Struct cannot be empty')
    field_map = {row[0]: row for row in fields}
    initial = definitions['initial']
    if not isinstance(initial, ast.Call) or not isinstance(initial.func, ast.Name) or initial.func.id != state_name or initial.args:
        fail(initial, 'FSM initial requires a full state constructor with keyword literals')
    initial_values = keywords(initial)
    if initial_values.keys() != field_map.keys():
        fail(initial, 'FSM initial must specify every state field exactly once')
    for name, node in initial_values.items():
        literal(node, field_map[name], enums, required=True)
    patterns, pattern_map, equalities = [], {}, {}
    for name, node in definitions.items():
        if name in ('state_type', 'initial', 'edges'):
            continue
        if not isinstance(node, ast.Call) or node.args or name.startswith('_'):
            fail(node, 'FSM patterns require Pattern(...) or previous_pattern.child(...)')
        parent = None
        if isinstance(node.func, ast.Name) and helpers.get(node.func.id) == 'Pattern':
            pass
        elif (isinstance(node.func, ast.Attribute) and node.func.attr == 'child'
                and isinstance(node.func.value, ast.Name) and node.func.value.id in pattern_map):
            parent = node.func.value.id
        else:
            fail(node, 'pattern parent must be declared earlier; import Pattern explicitly')
        constraints = dict(equalities.get(parent, {}))
        conditions = [expression(pattern_map[parent])] if parent else []
        for field, value in keywords(node).items():
            if field == 'where':
                conditions.append(lambda_body(value, 1, field_map, enums, ('q',)))
                continue
            if field not in field_map:
                fail(value, 'unknown pattern field: ' + field)
            literal(value, field_map[field], enums, required=True)
            encoded = ast.unparse(value)
            if field in constraints and constraints[field] != encoded:
                fail(value, 'child pattern contradicts inherited field: ' + field)
            constraints[field] = encoded
            conditions.append(ast.Compare(left=expression('q.' + field), ops=[ast.Eq()], comparators=[value]))
        predicate = ast.unparse(conjunction(conditions))
        patterns.append((name, parent, predicate))
        pattern_map[name], equalities[name] = predicate, constraints
    if not patterns:
        fail(declaration, 'Struct FSM requires named patterns')
    edges_node = definitions['edges']
    if not isinstance(edges_node, (ast.Tuple, ast.List)):
        fail(edges_node, 'FSM edges must be a static sequence')
    edges = []
    for node in edges_node.elts:
        if (not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name)
                or helpers.get(node.func.id) != 'Edge' or len(node.args) != 2):
            fail(node, 'Struct FSM edges require Edge(source, target, writes=...)')
        if any(not isinstance(arg, ast.Name) or arg.id not in pattern_map for arg in node.args):
            fail(node, 'FSM edge endpoints must name declared patterns')
        options = keywords(node)
        if 'writes' not in options or options.keys() - {'writes', 'guard'}:
            fail(node, 'FSM Edge requires writes and optionally guard')
        writes_node = options['writes']
        if not isinstance(writes_node, (ast.Tuple, ast.List)):
            fail(writes_node, 'FSM writes must be a static field sequence')
        writes = []
        for item in writes_node.elts:
            if (not isinstance(item, ast.Constant) or type(item.value) is not str
                    or item.value not in field_map or item.value in writes):
                fail(item, 'FSM writes must contain unique declared field names')
            writes.append(item.value)
        guard = lambda_body(options['guard'], 2, field_map, enums, ('old', 'new')) if 'guard' in options else ast.Constant(True)
        edge = (node.args[0].id, node.args[1].id, tuple(writes), ast.unparse(guard))
        if edge in edges:
            fail(node, 'duplicate composite FSM edge')
        edges.append(edge)
    return CompositeConfiguration(declaration.name, state_name, tuple(fields),
                                    tuple((name, ast.unparse(initial_values[name])) for name in field_map),
                                    tuple(patterns), tuple(edges), tuple(enums.items()))


def composite_definition(config):
    lines = ['@ac.module', f'def {config.name}():']
    initial = dict(config.initial)
    initial_values = ', '.join(f'{name}={initial[name]}' for name, *_ in config.fields)
    lines += [f'    storage: {config.state_type} = {config.state_type}({initial_values})',
                '    snapshot = storage']
    for name, annotation, _, _ in config.fields:
        lines += [f'    snapshot_{name} = snapshot.{name}']
    values = ', '.join(f'{name}=snapshot_{name}' for name, *_ in config.fields)
    lines += ['', '    @ac.method', f'    def state() -> {config.state_type}:',
                f'        return {config.state_type}({values})']
    snapshots = {name: expression('snapshot_' + name) for name, *_ in config.fields}
    for name, _, predicate in config.patterns:
        value = ast.unparse(substitute(expression(predicate), {'q': snapshots}))
        lines += ['', '    @ac.method', f'    def match_{name}() -> ac.u1:', f'        return {value}']
    return ast.parse('\n'.join(lines) + '\n').body


def lower_composite_call(lowerer, node, instance, method, config):
    if method == 'matches' and len(node.args) == 1 and not node.keywords:
        target = node.args[0]
        names = {name for name, _, _ in config.patterns}
        if (not isinstance(target, ast.Attribute) or not isinstance(target.value, ast.Name)
                or target.value.id != config.declaration or target.attr not in names):
            fail(target, 'matches requires a static pattern from this FSM definition')
        lowerer.records[instance]['calls'].append({'method': method, 'pattern': target.attr,
                                                    'line': node.lineno, 'caller': lowerer.callable[-1]})
        query = ast.Call(func=ast.Attribute(value=ast.Name(id=instance, ctx=ast.Load()),
                                            attr='match_' + target.attr, ctx=ast.Load()), args=[], keywords=[])
        index = 0
        while f'_fsm_match_{index}' in lowerer.used_names:
            index += 1
        binding = f'_fsm_match_{index}'
        lowerer.used_names.add(binding)
        # Native methods cannot appear in branch tests. This method has no
        # admission guard or effect and reads the same committed snapshot on
        # every path, so its value can be bound at callable entry.
        lowerer.query_preludes[-1].append(ast.copy_location(ast.Assign(
            targets=[ast.Name(id=binding, ctx=ast.Store())], value=query), node))
        return ast.copy_location(ast.Name(id=binding, ctx=ast.Load()), node)
    if method != 'transition' or len(node.args) != 1 or node.keywords or not lowerer.statement_call:
        fail(node, 'Struct FSM exposes state(), matches(pattern), and standalone transition(Next(...))')
    target = node.args[0]
    if (not isinstance(target, ast.Call) or not isinstance(target.func, ast.Name)
            or lowerer.helpers.get(target.func.id) != 'Next' or target.args):
        fail(target, 'Struct FSM transition target must be Next with explicit keyword fields')
    updates = keywords(target)
    fields = {row[0]: row for row in config.fields}
    if not updates or updates.keys() - fields.keys():
        fail(target, 'Next must specify nonempty declared state fields')
    permitted = [edge for edge in config.edges if updates.keys() <= set(edge[2])]
    if not permitted:
        fail(target, 'Next write fields are not permitted by any FSM edge')
    old = {name: expression('snapshot_' + name) for name in fields}
    new = dict(old)
    constants, arguments, parameters = {}, [], []
    for name in fields:
        if name not in updates:
            continue
        value = updates[name]
        is_literal = literal(value, fields[name], dict(config.enums), required=False)
        # Keep Enum destinations specialized. Numeric literals must cross a
        # typed argument boundary before they enter old/new expressions: raw
        # literal-vs-literal comparisons otherwise lose the state field width.
        if is_literal and fields[name][3]:
            constants[name] = ast.unparse(value)
            new[name] = copy.deepcopy(value)
        else:
            argument = 'value_' + name
            new[name] = expression(argument)
            parameters.append((argument, fields[name][1]))
            previous = lowerer.statement_call
            lowerer.statement_call = False
            arguments.append(lowerer.visit(value))
            lowerer.statement_call = previous
    key = json.dumps([sorted(updates), constants], sort_keys=True)
    name = 'to_update_' + hashlib.sha256(key.encode()).hexdigest()[:10]
    definition = lowerer.specializations[config][0]
    if not any(isinstance(item, ast.FunctionDef) and item.name == name for item in definition.body):
        patterns = {key: expression(value) for key, _, value in config.patterns}
        conditions = [conjunction([substitute(patterns[source], {'q': old}),
                                    substitute(patterns[target_name], {'q': new}),
                                    substitute(expression(guard), {'old': old, 'new': new})])
                        for source, target_name, _, guard in permitted]
        combined = ast.BoolOp(op=ast.Or(), values=conditions) if len(conditions) > 1 else conditions[0]
        condition = ast.unparse(fold_static_guard(combined, dict(config.enums)))
        params = ', '.join(arg + ': ' + annotation for arg, annotation in parameters)
        lambda_params = ', '.join(arg for arg, _ in parameters)
        lines = [f'@ac.method(guard=lambda {lambda_params}: {condition})', f'def {name}({params}) -> None:']
        # The FSM owns one state object. Disjoint physical field writes cannot
        # independently certify two transitions: their joint candidate may be
        # outside the graph even when each individual transition is legal.
        # Submit the complete candidate as one write, holding omitted fields.
        values = ', '.join(f'{field}={ast.unparse(new[field])}' for field in fields)
        lines += [f'    storage = {config.state_type}({values})']
        definition.body.extend(ast.parse('\n'.join(lines) + '\n').body)
    lowerer.records[instance]['calls'].append({'method': method, 'writes': sorted(updates), 'native_method': name,
                                                'line': node.lineno, 'caller': lowerer.callable[-1]})
    return ast.copy_location(ast.Call(func=ast.Attribute(value=ast.Name(id=instance, ctx=ast.Load()),
                                                        attr=name, ctx=ast.Load()), args=arguments, keywords=[]), node)
