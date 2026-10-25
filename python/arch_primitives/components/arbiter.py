"""Hardware arbitration with guarded grants and commit-coupled RR updates."""

import ast
from dataclasses import dataclass
import hashlib
import json

from ..errors import ElaborationError
from ..registry import ComponentDefinition


class Arbiter:
    """Source marker for a hardware selection and priority-history owner."""

    def __new__(cls, *args, **kwargs):
        raise TypeError('Arbiter is a hardware source construct; use arch_primitives.elaborate')


class ArbiterError(ElaborationError):
    """Unsupported arbitration configuration or method use."""


@dataclass(frozen=True)
class ArbiterConfiguration:
    inputs: int
    policy: str
    initial: int

    @property
    def name(self):
        digest = hashlib.sha256(json.dumps(self.__dict__, sort_keys=True).encode()).hexdigest()[:10]
        return 'Arbiter_' + self.policy + '_' + digest

    @property
    def index_type(self):
        return f'ac.bits[{max(1, (self.inputs - 1).bit_length())}]'


def arbiter_definition(config):
    name, count, index_type = config.name, config.inputs, config.index_type
    mask_type = f'ac.bits[{count}]'
    choose = name + '_index'
    lines = [f'def {choose}(candidates: {mask_type}, start: {index_type}) -> {index_type}:',
             '    found: ac.u1 = 0', f'    index: {index_type} = 0']
    for row in range(count):
        lines += [f'    if start <= {row} and candidates[{row}:{row + 1}] and not found:',
                  '        found = 1', f'        index = {row}']
    for row in range(count):
        lines += [f'    if candidates[{row}:{row + 1}] and not found:',
                  '        found = 1', f'        index = {row}']
    lines += ['    return index', '', '@ac.module', f'def {name}():']
    rotating = config.policy == 'round_robin'
    if rotating:
        lines += [f'    start: {index_type} = {config.initial}']
    start = 'start' if rotating else '0'
    lines += ['', '    @ac.method', f'    def select(candidates: {mask_type}) -> {mask_type}:',
              f'        index = {choose}(candidates, {start})', f'        selected: {mask_type} = 0']
    for row in range(count):
        lines += [f'        if candidates != 0 and index == {row}:', f'            selected = {1 << row}']
    lines += ['        return selected', '',
              '    @ac.method(guard=lambda candidates: candidates != 0)',
              f'    def grant(candidates: {mask_type}) -> {index_type}:',
              f'        index = {choose}(candidates, {start})']
    if rotating:
        lines += [f'        start = 0 if index == {count - 1} else index + 1']
    lines += ['        return index']
    if rotating:
        bounded = count == 1 or count & (count - 1) != 0
        decorator = f'@ac.method(guard=lambda index: index < {count})' if bounded else '@ac.method'
        lines += ['', '    ' + decorator, f'    def advance(index: {index_type}) -> None:',
                  f'        start = 0 if index == {count - 1} else index + 1']
    return ast.parse('\n'.join(lines) + '\n').body


class ArbiterLowerer(ast.NodeTransformer):
    def __init__(self, markers, specializations, instances, statements):
        self.markers = markers
        self.specializations = specializations
        self.instances = instances
        self.module_assignments = {id(statement) for statement in statements}
        self.bindings = {}
        self.action_context = []

    def error(self, node, message):
        raise ArbiterError(f"line {getattr(node, 'lineno', '?')}: {message}")

    def arbiter_call(self, node):
        return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id in self.markers)

    def configuration(self, call):
        keywords = {keyword.arg: keyword.value for keyword in call.keywords}
        if call.args or None in keywords or len(keywords) != len(call.keywords):
            self.error(call, 'Arbiter requires explicit unique keyword arguments')
        if set(keywords) - {'inputs', 'policy', 'initial'}:
            self.error(call, 'unsupported Arbiter configuration option')
        count = keywords.get('inputs')
        if not isinstance(count, ast.Constant) or type(count.value) is not int or not 1 <= count.value <= 32:
            self.error(call, 'inputs must be a static integer in [1, 32]')
        policy = keywords.get('policy')
        if not isinstance(policy, ast.Constant) or policy.value not in ('round_robin', 'fixed_priority'):
            self.error(call, 'policy must be a literal round_robin or fixed_priority')
        initial = keywords.get('initial', ast.Constant(value=0))
        if not isinstance(initial, ast.Constant) or type(initial.value) is not int or not 0 <= initial.value < count.value:
            self.error(call, 'initial must be a static index in [0, inputs)')
        if policy.value == 'fixed_priority' and 'initial' in keywords:
            self.error(call, 'fixed_priority has no initial RR state')
        config = ArbiterConfiguration(count.value, policy.value, initial.value)
        self.specializations.setdefault(config, arbiter_definition(config))
        return config

    def visit_Assign(self, node):
        if self.arbiter_call(node.value):
            if id(node) not in self.module_assignments or len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
                self.error(node, 'Arbiter must be assigned directly to one name in a Module body')
            target = node.targets[0].id
            if target in self.bindings:
                self.error(node, 'Arbiter instances cannot be rebound')
            config = self.configuration(node.value)
            self.bindings[target] = config
            self.instances.append({'instance': target, 'line': node.lineno,
                                   'specialization': config.name, **config.__dict__})
            node.value = ast.copy_location(ast.Call(func=ast.Name(id=config.name, ctx=ast.Load()),
                                                   args=[], keywords=[]), node.value)
            return node
        if isinstance(node.value, ast.Name) and node.value.id in self.bindings:
            self.error(node, 'Arbiter instance aliases are not supported; use the original name')
        return self.generic_visit(node)

    def visit_Name(self, node):
        if isinstance(node.ctx, (ast.Store, ast.Del)) and node.id in self.bindings:
            self.error(node, 'Arbiter instances cannot be rebound or deleted')
        return node

    def visit_arg(self, node):
        if node.arg in self.bindings:
            self.error(node, 'Arbiter instances cannot be shadowed by a parameter')
        return node

    def visit_FunctionDef(self, node):
        self.action_context.append(set())
        result = self.generic_visit(node)
        self.action_context.pop()
        return result

    def visit_Attribute(self, node):
        if isinstance(node.value, ast.Name) and node.value.id in self.bindings:
            config = self.bindings[node.value.id]
            allowed = {'select', 'grant'}
            if config.policy == 'round_robin':
                allowed.add('advance')
            if node.attr not in allowed:
                self.error(node, f'{node.value.id}.{node.attr} is forbidden for policy={config.policy}')
        return self.generic_visit(node)

    def visit_Call(self, node):
        if self.arbiter_call(node):
            self.error(node, 'Arbiter construction requires a Module-body assignment')
        if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and node.func.value.id in self.bindings:
            self.visit_Attribute(node.func)
            if len(node.args) != 1 or node.keywords:
                self.error(node, node.func.attr + ' requires one positional argument')
            instance = node.func.value.id
            if (self.action_context and self.bindings[instance].policy == 'round_robin'
                    and node.func.attr in ('grant', 'advance')):
                if instance in self.action_context[-1]:
                    self.error(node, 'one RR update call per Rule/Method; grant already advances the priority')
                self.action_context[-1].add(instance)
        return self.generic_visit(node)


ARBITER_COMPONENT = ComponentDefinition(name='Arbiter', module=__name__, lowerer=ArbiterLowerer)
