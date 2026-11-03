# Architecture libraries

Reusable components belong in ordinary pyCircuit source libraries. They use the
same Module, Method and Rule semantics as consumer designs and compile through
the native Python capture, ACIR analysis and verified C++/Verilog flow. Pipe,
Counter, FSM and arbitration policy do not require component-specific compiler
operations or an additional source expander.

## Retired expansion entry

`pycircuit elaborate` is removed from the public driver. The SDK and wheel no
longer install `arch_primitives`. Its retained source is a migration input,
not a supported compilation entry. It must not be used as an automatic fallback
for source that the native frontend does not support.

The previous Pipe, Table, Arbiter and FSM expansion implementations and their
qualification remain available at
[the preceding source identity](https://github.com/Inory-Megumi/pyCircuit/tree/d70fd9b62081984b9c5dae7d098639c0d796d531/python/arch_primitives).
Historical qualification does not establish support for a replacement library.
The Architecture Lab also preserves its pinned demos and execution evidence.

## Native capability work

See [native operation interfaces](native-actions.md) for explicit Method kinds,
statement guards, successful-call observations, the bounded forward profile and
the ordinary source Pipe. Removing the expander does not establish replacement
qualification. No new Table library or LRU qualification is included.
