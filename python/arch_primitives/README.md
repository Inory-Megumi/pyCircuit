# Architecture extensions

This package ships with the downstream PyCircuit Python package and CMake SDK.
Its maintained source is in `Inory-Megumi/pyCircuit`, branch `codex/archlab`.
The original import and source identities are recorded in `ORIGIN.json`.

```python
from arch_primitives import Pipe, Table, Arbiter, FSM, Pattern, Edge, Next
```

Use `pycircuit elaborate author.py -o expanded/author.py`, then the standard
`pycircuit compile`, `link` and `emit` commands. The existing
`python -m arch_primitives` entry point and `elaborate()` API remain available.
Expansion parses source syntax without executing hardware functions and produces
ordinary PyCircuit definitions plus an `arch-primitives/v1` component manifest.

See [the extension guide](../../docs/extensions/architecture.md) for component
contracts, compiler dependencies, validation evidence and remaining limits.
Counter remains research-only and is not exported. Optional FSM graph analysis
requires NetworkX; ordinary expansion has no new runtime dependency.
