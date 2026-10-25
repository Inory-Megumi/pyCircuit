"""Component registration contract used by the source elaborator."""

from dataclasses import dataclass

from .errors import ElaborationError


@dataclass(frozen=True)
class ComponentDefinition:
    """A public source marker and its module-scoped AST lowering pass.

    The lowerer receives (markers, specializations, instances, statements).
    It stores generated definitions by specialization key and records instance
    properties. The driver handles imports, assembly, output and the manifest.
    An optional prepare(markers, body) hook removes source declarations and
    returns the remaining body plus component-specific lowerer arguments.
    An optional lowerer.finalize() validates complete local call graphs.
    """

    name: str
    module: str
    lowerer: type
    prepare: object = None
    helpers: tuple = ()

    @property
    def import_modules(self):
        return ('arch_primitives', 'arch_primitives.components', self.module)


def component_registry(components=None):
    """Resolve the built-in catalog or an explicitly supplied component set."""
    if components is None:
        from .components import COMPONENTS
        components = COMPONENTS
    registry = {}
    for component in components:
        if not component.name.isidentifier() or component.name in registry:
            raise ElaborationError('invalid or duplicate component name: ' + component.name)
        registry[component.name] = component
    return registry
