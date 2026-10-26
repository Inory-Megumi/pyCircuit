"""Compose registered architecture components into official pyCircuit source."""

import ast
import hashlib
from pathlib import Path

from .errors import ElaborationError
from .registry import component_registry


def elaborate(source, destination, *, components=None):
    """Expand registered components without executing authored design functions."""
    source, destination = Path(source), Path(destination)
    if source.resolve() == destination.resolve():
        raise ElaborationError("expanded output must not overwrite the authored source")
    original_bytes = source.read_bytes()
    tree = ast.parse(original_bytes.decode("utf-8"), filename=str(source))
    registry = component_registry(components)
    import_modules = {
        module for component in registry.values() for module in component.import_modules
    }
    helper_owners = {}
    for component in registry.values():
        for helper in component.helpers:
            if helper in registry or helper in helper_owners:
                raise ElaborationError("duplicate component helper: " + helper)
            helper_owners[helper] = component
    markers, aliases, helpers, body = {}, {}, {}, []
    for node in tree.body:
        if isinstance(node, ast.ImportFrom) and node.module in import_modules:
            for item in node.names:
                component = registry.get(item.name) or helper_owners.get(item.name)
                if component is None or node.module not in component.import_modules:
                    raise ElaborationError(
                        "unsupported architecture component import: " + item.name
                    )
                alias = item.asname or item.name
                if alias in aliases:
                    raise ElaborationError("duplicate component import alias: " + alias)
                aliases[alias] = component.name
                component_markers = markers.setdefault(component.name, set())
                if item.name == component.name:
                    component_markers.add(alias)
                else:
                    helpers.setdefault(component.name, {})[alias] = item.name
        else:
            body.append(node)
    if not markers:
        raise ElaborationError(
            "source must explicitly import an architecture component"
        )
    if not any(
        isinstance(node, ast.Import)
        and any(item.name == "pycircuit" and item.asname == "ac" for item in node.names)
        for node in body
    ):
        raise ElaborationError("this prototype requires import pycircuit as ac")
    prepared = {}
    for name, component_markers in markers.items():
        if registry[name].prepare is not None:
            options = (
                {"helpers": helpers.get(name, {})} if registry[name].helpers else {}
            )
            body, prepared[name] = registry[name].prepare(
                component_markers, body, **options
            )
    specializations = {name: {} for name in markers}
    instances = []
    for node in body:
        if isinstance(node, ast.FunctionDef) and any(
            isinstance(decorator, ast.Attribute)
            and isinstance(decorator.value, ast.Name)
            and decorator.value.id == "ac"
            and decorator.attr == "module"
            for decorator in node.decorator_list
        ):
            for name, component_markers in markers.items():
                start = len(instances)
                lowerer = registry[name].lowerer(
                    component_markers,
                    specializations[name],
                    instances,
                    node.body,
                    **prepared.get(name, {}),
                )
                node.body = [lowerer.visit(statement) for statement in node.body]
                if hasattr(lowerer, "finalize"):
                    lowerer.finalize()
                for instance in instances[start:]:
                    instance["component"] = name
    if not instances:
        raise ElaborationError(
            "no module-scoped architecture component instances were found"
        )
    generated = [
        node
        for definitions in specializations.values()
        for nodes in definitions.values()
        for node in nodes
    ]
    names = [
        node.name
        for node in generated
        if isinstance(node, ast.FunctionDef | ast.ClassDef)
    ]
    generated_names = set(names)
    if len(names) != len(generated_names):
        raise ElaborationError("generated architecture component names collide")
    if any(
        isinstance(node, ast.Name)
        and isinstance(node.ctx, ast.Store)
        and node.id in generated_names
        or isinstance(node, ast.FunctionDef | ast.ClassDef)
        and node.name in generated_names
        for node in ast.walk(tree)
    ):
        raise ElaborationError(
            "authored names collide with a generated component specialization"
        )
    # Keep deterministic source ownership: generated module definitions follow
    # authored callers, with every Rule/Method edge intact.
    tree.body = body + generated
    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and node.id in aliases:
            raise ElaborationError(
                f"line {getattr(node, 'lineno', '?')}: unresolved component use: {node.id}"
            )
    ast.fix_missing_locations(tree)
    expanded = (
        "# Elaborated architecture components; edit the authored source instead.\n"
        + ast.unparse(tree)
        + "\n"
    )
    if not expanded.isascii():
        raise ElaborationError("authored hardware source must use ASCII")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(expanded, encoding="ascii", newline="\n")
    return {
        "schema": "arch-primitives/v1",
        "source": str(source),
        "source_sha256": hashlib.sha256(original_bytes).hexdigest(),
        "expanded_sha256": hashlib.sha256(expanded.encode()).hexdigest(),
        "components": list(markers),
        "instances": instances,
        "compiler_builtin": False,
        "route": "static source elaboration -> official compile/link/emit",
    }
