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
| Arbiter | Fixed, round-robin or `lru` selection; guarded grant; advance is RR-only. LRU uses pairwise least-recently-served order and updates only with its caller's successful commit. |
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

### LRU service order

`Arbiter(inputs=4, policy="lru")` retains the existing `select` and `grant`
interfaces. `select(requests)` is a read-only one-hot query (zero for no
requests). `grant(requests)` returns the chosen index, guards its caller on
empty requests, and proposes a service-order update in that same transaction.
Blocked output pushes or other required calls discard the entire update.
Queries before and after `grant` read the same committed age snapshot.

Initial priority is `0 > 1 > ... > N-1`; LRU rejects `initial` and `advance`.
The implementation stores N*(N-1)/2 pairwise bits. A committed winner becomes
youngest relative to every other input; other pairs retain their order.
Request withdrawal does not erase service history. This is service age per
input, rather than transaction arrival age. N=1 has no priority state.
One `grant` per instance per Rule/Method is accepted; multiple calls, including
exclusive source branches, are rejected conservatively. Cross-rule writer
legality remains subject to the normal compiler checks. Selection is not locked.
Selection and pair updates use ordinary bitwise expressions and `ac.concat`;
grant decoding reuses `ac.priority_encode`. Literal queries containing at most
two candidate bits are folded into private read-only methods using the exact
pair relation. Dynamic masks retain the general matrix selection logic.

This local extension update is recorded separately in `ORIGIN.json` while the
original imported hashes remain intact. Consumer demos and independent C++ /
Verilator models live in the Architecture Lab. Finite host checks are not
native compile, four-state, formal, or PPA qualification.

The imported extension source identities are retained in
[`ORIGIN.json`](https://github.com/Inory-Megumi/pyCircuit/blob/e749c7e53dc4f0b1b292551a24358adbb1f4b2cc/python/arch_primitives/ORIGIN.json). The Architecture Lab
keeps consumer demos, independent models, HNI RRT/RDT analysis and immutable
qualification receipts. Its former library directory is a pinned consumer
snapshot; future implementation changes belong here and update that pin.

Historical component and compiler qualification is documented in the
[Lab results](https://github.com/Inory-Megumi/PyCircuit-Architecture-Lab/blob/31e197b5d708dc03bd418850bd7c27f3f4efb23a/docs/RESEARCH_RESULTS.md)
and [compiler receipts](https://github.com/Inory-Megumi/PyCircuit-Architecture-Lab/tree/31e197b5d708dc03bd418850bd7c27f3f4efb23a/work/compiler_fixes).
The three compiler commits reproduce the recorded qualified file bytes; this
initial repository-management operation did not rerun native compiler, RTL or PPA gates.
New host tests cover extension CLI behavior, package staging and source parity.
No release or installed compiler activation follows from a source push.

## Upstream integration on 2026-10-26

The integration candidate includes upstream `16453e2b` and the prior downstream
compiler fixes. Directly nested Rules register once by declaration, and their
bare names supply Module/System results. Extension-generated autonomous Rules
follow that contract; callers must migrate explicit activation calls separately.
The retired `after`/EHR behavior is not restored.

`Pipe(flow="valid_only")` retains its fixed stage latency and no-backpressure
contract. Native one-entry Queues transfer occupied stages each epoch; an
autonomous final-stage consumer expires the previous output. Downstream-pop
credit permits concurrent replacement. Its public methods remain `push` and
read-only `view`; no public `pop` or ready port is added. Empty epochs propagate
bubbles, and blocked outer transactions contribute no input token.

LRU service order and all resource effects remain part of the caller's atomic
transaction. Immutable metadata measurements, complete scope bindings and
read-only identity results are reused within their proof owners. Scope/type,
ownership, admission, private-route and conflict checks remain independent;
analysis caps are unchanged.

Qualification of the local integration passed the official API gate (25 CTest
entries, including the selected lit gate), examples gate (13 CTest entries for
seven designs), strict documentation build, repository metadata checks, API
hygiene and changed-file Ruff/Black checks. Focused native source/transaction
checks passed 504 tests; that selection overlaps the API gate. The bounded
capture/publication plus extension unit selection passed 272 tests with three
conditional skips. SourceIdentifier's oracle uses CPython 3.14.6 / Unicode 16;
the lit launcher requires its matching Python module path.

Migrated Lab copies remove explicit Rule activation/result calls without
changing ordered business Rule ASTs, original stimuli or independent models.
Sixteen positive cases passed source compile/link, C++/Verilog emit, slang and
known-0/1 C++/Verilator simulation: 23,664 field comparisons per backend with
equal observations. Three genuine conflict cases retain expected link rejection.
Coverage includes all Arbiter policies and LRU edges, Pipe bubbles/replacement,
Table atomicity, shared FSM writers, and WriteExecution mixed/stress traffic.
WriteExecution's old final beat and next committed control head remain in one
outer Rule; there is no cross-Rule forwarding or empty-queue bypass.

Three targeted Boolean-record execution tests and the official enum/Table smoke
tests also passed their Icarus four-state checks. This does not qualify whole
components or HNI for arbitrary X/Z inputs. Full nightly, VCS, reference RTL
equivalence, formal proof and PPA were not run. The Lab retains the exact merge,
source migration and qualification receipts separately from historical evidence.
No remote push, release or default compiler activation follows from this local
integration.
