"""Register Table source marker and four-method static elaboration."""

import ast
import copy
from dataclasses import dataclass
import hashlib
import json

from ..errors import ElaborationError
from ..registry import ComponentDefinition


class Table:
    """Hardware source construct; not a Python runtime container."""

    def __class_getitem__(cls, payload_type):
        return cls

    def __new__(cls, *args, **kwargs):
        raise TypeError('Table is a hardware source construct; use arch_primitives.elaborate')


class TableError(ElaborationError):
    """Unsupported Table source configuration or operation."""


@dataclass(frozen=True)
class TableConfiguration:
    payload: str
    depth: int
    init: str

    @property
    def name(self):
        digest = hashlib.sha256(json.dumps(self.__dict__, sort_keys=True).encode()).hexdigest()[:10]
        return 'Table_' + digest

    @property
    def index_type(self):
        return f'ac.bits[{max(1, (self.depth - 1).bit_length())}]'

    @property
    def bounded(self):
        return self.depth == 1 or self.depth & (self.depth - 1) != 0


def table_definition(config):
    guard_read = f'@ac.method(guard=lambda index: index < {config.depth})' if config.bounded else '@ac.method'
    guard_write = f'@ac.method(guard=lambda index, value: index < {config.depth})' if config.bounded else '@ac.method'
    lines = ['@ac.module', f'def {config.name}():',
             f'    saved = ac.table[{config.depth}, {config.payload}](init={config.init})', '',
             '    ' + guard_read, f'    def read(index: {config.index_type}) -> {config.payload}:']
    if config.bounded:
        lines += [f'        result: {config.payload} = 0', f'        for row in range({config.depth}):',
                  '            if index == row:', '                result = saved[row]', '        return result']
    else:
        lines += ['        return saved[index]']
    lines += ['', '    ' + guard_write,
              f'    def write(index: {config.index_type}, value: {config.payload}) -> None:']
    if config.bounded:
        lines += [f'        for row in range({config.depth}):', '            if index == row:',
                  '                saved[row] = value']
    else:
        lines += ['        saved[index] = value']
    lines += ['', '    @ac.method',
              f'    def snapshot_rows() -> ac.table[{config.depth}, {config.payload}]:',
              '        return saved']
    return ast.parse('\n'.join(lines) + '\n').body


class ReplaceRow(ast.NodeTransformer):
    def __init__(self, parameter, replacement):
        self.parameter, self.replacement = parameter, replacement

    def visit_Name(self, node):
        if node.id == self.parameter:
            return ast.copy_location(ast.Name(id=self.replacement, ctx=ast.Load()), node)
        return node


class TableLowerer(ast.NodeTransformer):
    def __init__(self, markers, specializations, instances, statements):
        self.markers, self.specializations, self.instances = markers, specializations, instances
        self.bindings = {}
        self.module_statements = {id(node) for node in statements}
        self.used = {node.id for statement in statements for node in ast.walk(statement)
                     if isinstance(node, ast.Name)}
        self.serial = 0
        self.in_callable = False

    def visit_FunctionDef(self, node):
        previous = self.in_callable
        self.in_callable = any(isinstance(item, (ast.Attribute, ast.Call)) and
                               isinstance(item.func if isinstance(item, ast.Call) else item, ast.Attribute) and
                               (item.func if isinstance(item, ast.Call) else item).attr in {'rule', 'method'}
                               for item in node.decorator_list)
        result = self.generic_visit(node)
        self.in_callable = previous
        return result

    def error(self, node, message):
        raise TableError(f"line {getattr(node, 'lineno', '?')}: {message}")

    def fresh(self, purpose):
        while True:
            self.serial += 1
            name = f'__table_{purpose}_{self.serial}'
            if name not in self.used:
                self.used.add(name)
                return name

    def construction(self, node):
        return (isinstance(node, ast.Call) and isinstance(node.func, ast.Subscript)
                and isinstance(node.func.value, ast.Name) and node.func.value.id in self.markers)

    def receiver(self, call):
        if (isinstance(call, ast.Call) and isinstance(call.func, ast.Attribute)
                and isinstance(call.func.value, ast.Name)):
            return self.bindings.get(call.func.value.id)
        return None

    def pure(self, node):
        if any(isinstance(item, (ast.Call, ast.Lambda, ast.NamedExpr, ast.ListComp, ast.SetComp,
                                 ast.DictComp, ast.GeneratorExp, ast.Await, ast.Yield))
               for item in ast.walk(node)):
            self.error(node, 'Table expression must be pure; stage method calls into locals first')

    def visit_Assign(self, node):
        if self.construction(node.value):
            if (id(node) not in self.module_statements or len(node.targets) != 1
                    or not isinstance(node.targets[0], ast.Name)):
                self.error(node, 'Table must be assigned to one name directly in a Module body')
            name, call = node.targets[0].id, node.value
            if name in self.bindings:
                self.error(node, 'Table instances cannot be rebound')
            options = {kw.arg: kw.value for kw in call.keywords}
            if (call.args or None in options or len(options) != len(call.keywords)
                    or set(options) != {'depth', 'init'}):
                self.error(call, 'Table requires explicit depth and init keywords only')
            depth = options['depth']
            if not isinstance(depth, ast.Constant) or type(depth.value) is not int or not 1 <= depth.value <= 64:
                self.error(call, 'depth must be a static integer in [1, 64]')
            payload = call.func.slice
            if not isinstance(payload, (ast.Name, ast.Attribute, ast.Subscript)):
                self.error(call, 'T must name a concrete hardware type')
            config = TableConfiguration(ast.unparse(payload), depth.value, ast.unparse(options['init']))
            self.bindings[name] = config
            self.specializations.setdefault(config, table_definition(config))
            self.instances.append({'instance': name, 'line': node.lineno,
                                   'specialization': config.name, **config.__dict__})
            node.value = ast.copy_location(ast.Call(func=ast.Name(id=config.name, ctx=ast.Load()),
                                                    args=[], keywords=[]), call)
            return node
        config = self.receiver(node.value)
        if config and node.value.func.attr == 'match':
            if (not self.in_callable or len(node.targets) != 1
                    or not isinstance(node.targets[0], ast.Name)):
                self.error(node, 'match requires one ordinary result name inside a Rule/Method')
            if node.targets[0].id in self.bindings:
                self.error(node, 'Table instances cannot be rebound')
            return self.match(node, config)
        if isinstance(node.value, ast.Name) and node.value.id in self.bindings:
            self.error(node, 'Table aliases are unsupported; use the original instance name')
        return self.generic_visit(node)

    def visit_Name(self, node):
        if isinstance(node.ctx, (ast.Store, ast.Del)) and node.id in self.bindings:
            self.error(node, 'Table instances cannot be rebound or deleted')
        return node

    def visit_arg(self, node):
        if node.arg in self.bindings:
            self.error(node, 'Table instance names cannot be shadowed')
        return node

    def visit_Expr(self, node):
        config = self.receiver(node.value)
        if config and node.value.func.attr == 'update':
            if not self.in_callable:
                self.error(node, 'Table operations belong inside a Rule/Method')
            call = node.value
            fields = [kw.arg for kw in call.keywords]
            if (len(call.args) != 1 or not fields or None in fields
                    or len(fields) != len(set(fields))):
                self.error(call, 'update requires one index and explicit unique field keywords')
            for expression in [*call.args, *(kw.value for kw in call.keywords)]:
                self.pure(expression)
            method = self.update_method(config, tuple(sorted(fields)))
            index, patch = self.fresh('index'), self.fresh('patch')
            statements = ast.parse(f'{index} = {ast.unparse(call.args[0])}\n'
                                   f'{patch}: {config.payload} = 0\n').body
            for kw in call.keywords:
                statements.append(ast.Assign(targets=[ast.Attribute(
                    value=ast.Name(id=patch, ctx=ast.Load()), attr=kw.arg, ctx=ast.Store())],
                    value=copy.deepcopy(kw.value)))
            statements += ast.parse(f'{call.func.value.id}.{method}({index}, {patch})\n').body
            return [ast.copy_location(statement, node) for statement in statements]
        return self.generic_visit(node)

    def update_method(self, config, fields):
        suffix = hashlib.sha256(json.dumps(fields).encode()).hexdigest()[:10]
        name = 'update_fields_' + suffix
        module = self.specializations[config][0]
        if any(isinstance(node, ast.FunctionDef) and node.name == name for node in module.body):
            return name
        guard = (f'@ac.method(guard=lambda index, value: index < {config.depth})'
                 if config.bounded else '@ac.method')
        lines = [guard, f'def {name}(index: {config.index_type}, value: {config.payload}) -> None:']
        if config.bounded:
            lines += [f'    for row in range({config.depth}):', '        if index == row:']
            lines += [f'            saved[row].{field} = value.{field}' for field in fields]
        else:
            lines += [f'    saved[index].{field} = value.{field}' for field in fields]
        module.body.extend(ast.parse('\n'.join(lines) + '\n').body)
        return name

    def match(self, node, config):
        call = node.value
        if (call.args or len(call.keywords) != 1 or call.keywords[0].arg != 'where'
                or not isinstance(call.keywords[0].value, ast.Lambda)):
            self.error(call, 'match requires where=lambda row: predicate')
        predicate = call.keywords[0].value
        args = predicate.args
        if (args.posonlyargs or len(args.args) != 1 or args.vararg or args.kwarg
                or args.kwonlyargs or args.defaults):
            self.error(predicate, 'match predicate requires one ordinary argument')
        self.pure(predicate.body)
        self.pure(call.func.value)
        result = node.targets[0].id
        mask = self.fresh('mask')
        snapshot = self.fresh('snapshot')
        statements = ast.parse(f'{snapshot} = {call.func.value.id}.snapshot_rows()\n'
                               f'{mask}: ac.bits[{config.depth}] = 0\n').body
        for index in range(config.depth):
            row = self.fresh('row')
            bit = self.fresh('bit')
            statements += ast.parse(f'{row} = {snapshot}[{index}]\n').body
            condition = ReplaceRow(args.args[0].arg, row).visit(copy.deepcopy(predicate.body))
            statements.append(ast.AnnAssign(target=ast.Name(id=bit, ctx=ast.Store()),
                annotation=ast.parse(f'ac.bits[{config.depth}]', mode='eval').body,
                value=ast.IfExp(test=condition, body=ast.Constant(value=1 << index),
                               orelse=ast.Constant(value=0)), simple=1))
            statements += ast.parse(f'{mask} = {mask} | {bit}\n').body
        statements += ast.parse(f'{result} = {mask}\n').body
        return [ast.copy_location(statement, node) for statement in statements]

    def visit_Call(self, node):
        if self.construction(node):
            self.error(node, 'Table construction requires a named Module-body assignment')
        config = self.receiver(node)
        if config:
            if not self.in_callable:
                self.error(node, 'Table operations belong inside a Rule/Method')
            method = node.func.attr
            if method not in {'read', 'write'}:
                self.error(node, 'Table supports read/write, statement update and assigned match only')
            expected = 1 if method == 'read' else 2
            if len(node.args) != expected or node.keywords:
                self.error(node, f'{method} requires {expected} positional arguments')
        return self.generic_visit(node)


TABLE_COMPONENT = ComponentDefinition(name='Table', module=__name__, lowerer=TableLowerer)
