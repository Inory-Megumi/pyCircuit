"""Pipe marker, configuration, method checks and native module generation."""

import ast
import hashlib
import json
from dataclasses import dataclass

from ..errors import ElaborationError
from ..registry import ComponentDefinition


class Pipe:
    """Source marker; hardware design functions are captured, never executed."""

    def __class_getitem__(cls, payload_type):
        return cls

    def __new__(cls, *args, **kwargs):
        raise TypeError(
            "Pipe is a hardware source construct; use arch_primitives.elaborate"
        )


class PipeError(ElaborationError):
    """An unsupported Pipe configuration or source operation."""


@dataclass(frozen=True)
class PipeConfiguration:
    payload: str
    flow: str
    stages: int
    reset_value: str

    @property
    def name(self):
        identity = json.dumps(self.__dict__, sort_keys=True).encode("ascii")
        return "Pipe_" + self.flow + "_" + hashlib.sha256(identity).hexdigest()[:10]


def pipe_definition(config):
    """Produce ordinary typed state, methods and native Queue allocations."""
    name, payload, count = config.name, config.payload, config.stages
    lines = []
    if config.flow != "none":
        lines += [
            "@ac.struct",
            f"class {name}Sample:",
            "    valid: ac.u1",
            f"    payload: {payload}",
            "",
        ]
    if config.flow == "none":
        lines += ["@ac.module", f"def {name}(incoming: {payload}) -> {payload}:"]
        for index in range(count):
            lines.append(f"    saved{index}: {payload} = {config.reset_value}")
        lines += ["", "    @ac.rule", "    def advance() -> None:"]
        for index in reversed(range(1, count)):
            lines.append(f"        saved{index} = saved{index - 1}")
        lines += ["        saved0 = incoming", f"    return saved{count - 1}"]
    else:
        lines += ["@ac.module", f"def {name}():"]
        for index in range(count):
            lines.append(
                f'    slot{index} = ac.queue[{payload}](depth=1, latency=1, ready_policy="downstream_pop")'
            )
        for index in range(count - 1):
            lines += [
                "",
                "    @ac.rule",
                f"    def transfer{index}() -> None:",
                f"        value = slot{index}.pop()",
                f"        slot{index + 1}.push(value)",
            ]
        if config.flow == "valid_only":
            # Every occupied stage advances each epoch. The unconditional sink
            # drains the final stage, so native downstream-pop credit permits
            # simultaneous replacement without an author-visible ready guard.
            lines += [
                "",
                "    @ac.rule",
                "    def retire() -> None:",
                f"        expired = slot{count - 1}.pop()",
            ]
        lines += [
            "",
            "    @ac.method",
            f"    def push(value: {payload}) -> None:",
            "        slot0.push(value)",
        ]
        if config.flow == "valid_ready":
            lines += [
                "",
                "    @ac.method",
                f"    def pop() -> {payload}:",
                f"        return slot{count - 1}.pop()",
            ]
        lines += [
            "",
            "    @ac.method",
            f"    def view() -> {name}Sample:",
            f"        return {name}Sample(valid=slot{count - 1}.valid, payload=slot{count - 1}.data)",
        ]
    return ast.parse("\n".join(lines) + "\n").body


class PipeLowerer(ast.NodeTransformer):
    def __init__(self, markers, specifications, instances, statements):
        self.markers = markers
        self.specifications = specifications
        self.instances = instances
        self.bindings = {}
        self.module_assignments = {id(statement) for statement in statements}

    def error(self, node, message):
        raise PipeError(f"line {getattr(node, 'lineno', '?')}: {message}")

    def configuration(self, call):
        keywords = {keyword.arg: keyword.value for keyword in call.keywords}
        if len(keywords) != len(call.keywords) or None in keywords:
            self.error(call, "Pipe keywords must be explicit and unique")
        unknown = set(keywords) - {"flow", "stages", "reset_value"}
        if unknown:
            self.error(call, "unsupported Pipe option: " + ", ".join(sorted(unknown)))
        flow = keywords.get("flow")
        if not isinstance(flow, ast.Constant) or flow.value not in (
            "none",
            "valid_only",
            "valid_ready",
        ):
            self.error(call, "flow must be a literal none, valid_only or valid_ready")
        stages = keywords.get("stages", ast.Constant(value=1))
        if (
            not isinstance(stages, ast.Constant)
            or type(stages.value) is not int
            or not 1 <= stages.value <= 16
        ):
            self.error(call, "stages must be a static integer in [1, 16]")
        payload = call.func.slice
        if not isinstance(payload, ast.Name | ast.Attribute | ast.Subscript):
            self.error(call, "T must name a concrete pyCircuit hardware type")
        if flow.value == "none":
            if len(call.args) != 1 or "reset_value" not in keywords:
                self.error(
                    call,
                    "none requires one fixed input and an explicit reset_value of type T",
                )
        elif call.args or "reset_value" in keywords:
            self.error(
                call,
                "valid modes accept input through push, without a reset_value option",
            )
        reset = keywords.get("reset_value", ast.Constant(value=0))
        config = PipeConfiguration(
            ast.unparse(payload), flow.value, stages.value, ast.unparse(reset)
        )
        self.specifications.setdefault(config, pipe_definition(config))
        return config

    def pipe_call(self, node):
        return (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Subscript)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id in self.markers
        )

    def visit_Assign(self, node):  # noqa: N802
        if self.pipe_call(node.value):
            if (
                id(node) not in self.module_assignments
                or len(node.targets) != 1
                or not isinstance(node.targets[0], ast.Name)
            ):
                self.error(
                    node,
                    "Pipe must be assigned once to a name directly in a Module body",
                )
            target = node.targets[0].id
            if target in self.bindings:
                self.error(node, "Pipe instances cannot be rebound")
            config = self.configuration(node.value)
            self.bindings[target] = config
            self.instances.append(
                {
                    "instance": target,
                    "line": node.lineno,
                    "specialization": config.name,
                    **config.__dict__,
                }
            )
            node.value = ast.copy_location(
                ast.Call(
                    func=ast.Name(id=config.name, ctx=ast.Load()),
                    args=node.value.args if config.flow == "none" else [],
                    keywords=[],
                ),
                node.value,
            )
            return node
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            target = node.targets[0].id
            if target in self.bindings:
                self.error(node, "Pipe instances cannot be rebound")
            if isinstance(node.value, ast.Name) and node.value.id in self.bindings:
                self.error(
                    node,
                    "Pipe instance aliases are not supported; use the original name",
                )
        return self.generic_visit(node)

    def visit_Name(self, node):  # noqa: N802
        if isinstance(node.ctx, ast.Store | ast.Del) and node.id in self.bindings:
            self.error(node, "Pipe instances cannot be rebound or deleted")
        return node

    def visit_arg(self, node):  # noqa: N802
        if node.arg in self.bindings:
            self.error(node, "Pipe instances cannot be shadowed by a parameter")
        return node

    def visit_Call(self, node):  # noqa: N802
        if self.pipe_call(node):
            self.error(
                node,
                "Pipe construction is only allowed in a named Module-body assignment",
            )
        if isinstance(node.func, ast.Attribute) and isinstance(
            node.func.value, ast.Name
        ):
            instance, method = node.func.value.id, node.func.attr
            if instance in self.bindings:
                config = self.bindings[instance]
                allowed = {"view"}
                if config.flow != "none":
                    allowed.add("push")
                if config.flow == "valid_ready":
                    allowed.add("pop")
                if method not in allowed:
                    self.error(
                        node, f"{instance}.{method} is forbidden for flow={config.flow}"
                    )
                expected = 1 if method == "push" else 0
                if len(node.args) != expected or node.keywords:
                    self.error(
                        node, f"{method} requires {expected} positional arguments"
                    )
                if config.flow == "none":
                    return ast.copy_location(
                        ast.Name(id=instance, ctx=ast.Load()), node
                    )
        return self.generic_visit(node)


PIPE_COMPONENT = ComponentDefinition(
    name="Pipe",
    module=__name__,
    lowerer=PipeLowerer,
)
