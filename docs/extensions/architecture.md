# Architecture extensions in the downstream compiler

`Inory-Megumi/pyCircuit`, branch `codex/archlab`, is the maintained source for
the architecture extension package and its compiler fixes. The upstream is
`PTO-ISA/pyCircuit`; this branch starts at `775d0f68ce40733c8f197b59011373e4e330895b`.
Compiler fixes remain separate commits on this single development line:
admission parse reuse, shared FSM writer exclusivity, then immutable transaction
analysis and typed Queue grant proofs.

## Public extension package

The Python distribution and CMake SDK install `arch_primitives` alongside
`pycircuit`. Existing imports are preserved:

```python
from arch_primitives import Pipe, Table, Arbiter, FSM, Pattern, Edge, Next
```

| Component | Current contract |
| --- | --- |
| Pipe | Static payload type; `none`, `valid_only`, `valid_ready`; explicit stage count. `none` requires a reset value. Elastic stages use native Queues. |
| Table | Register storage and routing with `read`, `write`, `update`, `match`. Match returns a bitmap and adds no arbitration. |
| Arbiter | Fixed or round-robin selection; guarded grant; advance is RR-only. Selection, eligibility and final commit remain distinct. |
| FSM | Enum or bounded scalar Struct state, legal edges, committed snapshot, hierarchical Pattern/Edge/Next definitions. Outer rules own cross-resource atomic commits. |

Counter is not exported. Automatic pipelining, arbitrary state types and a
general formal proof system are not provided. The optional graph-analysis API
uses NetworkX independently of hardware compilation.

## Expand, then compile

```text
pycircuit elaborate author.py -o expanded/author.py
pycircuit compile -c expanded/author.py --source-root expanded -o unit
pycircuit link unit --top author.Demo -o final.ac
pycircuit emit final.ac --target verilog -o rtl
```

`elaborate` creates the requested Python source and its `.components.json`
sidecar. Existing outputs require `--replace`; the authored source is protected.
The existing `python -m arch_primitives` and Python `elaborate()` API remain
available. Expansion parses the author source without importing or executing it.

This is a compiler-distributed extension stage producing ordinary module/method
definitions. All type, effect, resource, atomicity and final hardware checks
still use the normal source-unit compiler and common verified IR. The manifest
records `compiler_builtin=false`; no native Pipe/FSM IR operation is implied.
Shared Struct FSM writers depend on the compiler fixes on this development line.

## Ownership and qualification

The imported extension source identities are retained in
[`ORIGIN.json`](../../python/arch_primitives/ORIGIN.json). The Architecture Lab
keeps consumer demos, independent models, HNI RRT/RDT analysis and immutable
qualification receipts. Its former library directory is a pinned consumer
snapshot; future implementation changes belong here and update that pin.

Historical component and compiler qualification is documented in the
[Lab results](https://github.com/Inory-Megumi/PyCircuit-Architecture-Lab/blob/31e197b5d708dc03bd418850bd7c27f3f4efb23a/docs/RESEARCH_RESULTS.md)
and [compiler receipts](https://github.com/Inory-Megumi/PyCircuit-Architecture-Lab/tree/31e197b5d708dc03bd418850bd7c27f3f4efb23a/work/compiler_fixes).
The three compiler commits reproduce the recorded qualified file bytes; this
repository-management operation does not rerun native compiler, RTL or PPA gates.
New host tests cover extension CLI behavior, package staging and source parity.
No release or installed compiler activation follows from a source push.
