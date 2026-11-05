# Ordered Rule development

This fork starts from official commit
`8b6eb3c46f78a44babb33945072f744f64c2f01f` on branch
`codex/rule-order-20261105`. The user selected explicit Rule order with
compiler-owned state versions. This local candidate implements ordered autonomous
Rules while preserving the official behavior of unordered roots. It has not
replaced the lab's default SDK or any ETX installation.

## First implementation batch

The initial performance change indexes hardware identity candidates by SSA value
and a hash of the actual root/instance path. Cache hits still compare full scope
and bindings; stop matches still compare resolved payload types. The hash only
narrows candidates, including when paths collide. Existing work limits and
failure checks remain enabled.

The official baseline exhausts its 4M source-check budget on the shared
64-instance benchmark, reproduced on ETX and locally. The local candidate passes
all six benchmark cases, including that case, through compile/link, both emits,
independent rebuild checks and generated C++ library compilation. The five
cases that pass on both versions produce 290 byte-identical final IR and backend
files. This establishes a capacity improvement; one timing sample per version
does not establish a general speedup.

Three focused native test suites, the 64-instance source-graph regression and
32 measurement-tool tests pass. The minimal counter also agrees across generated
C++ workers 1/2 and Icarus RTL for ten sampling epochs. Large benchmark circuits
were not behaviorally simulated. The candidate has not replaced the ETX SDK or
the lab's default toolchain. This evidence belongs to the initial scope-index
candidate; the ordered-Rule candidate is qualified separately below.

## First semantic slice

The candidate separates Rule behavior from one centralized schedule:

```python
from pycircuit import bits, module, rule, schedule


@module
def OrderedCounter() -> bits[8]:
    count: bits[8] = 3

    @rule
    def increment() -> None:
        count = count + 1

    @rule
    def scale() -> None:
        count = count * 2

    schedule(increment, scale)
    return count
```

The executable example is `examples/ordered_counter/ordered_counter.py`.
This syntax requires this fork's candidate; the pinned official baseline rejects
it. Ordering is retained in source bodies and schema-4 publication summaries.
Linking recomputes registration dependencies, and standalone routed/final checks
authenticate forwarded state, predecessor final enables and physical commits.
The declaration follows its named directly nested autonomous Rules and precedes
the Module's return. It requires at least one name, without duplicates or keyword
arguments. Each Module has at most one list; Rules outside it remain independent
automatic roots. Import aliases and `ac.schedule(...)` use the same bound API.
Method and cross-instance ordering remain unsupported. The previous public
`@rule(after=...)` spelling is rejected; internal authenticated `ac.after` edges
remain the native representation of adjacent list entries.

This organization follows [Koika's separation of Rules and scheduler](https://github.com/mit-plv/koika#schedulers).
It does not implement Koika's complete scheduler or explicit read/write port
semantics: this fork uses the user-selected implicit state versions instead.

Rules remain separate atomic roots. For `A` before `B`, both the guard and body
of `B` read the state produced by successful `A`. If `A` is ineligible, its
writes are discarded and `B` reads the incoming state. If `B` is ineligible,
successful `A` still commits. Methods called within either Rule remain bound
to that Rule's atomic transaction.

Order describes combinational evaluation within one cycle. There is one
physical state update at the active edge, with no added pipeline stage.
Ordinary module outputs continue to expose registered current state. Unordered
Rules retain the official current-state semantics and conflict checks.

For each state owner, the conceptual chain is:

```text
v0 = registered current state
v1 = A commits ? A candidate(v0) : v0
v2 = B commits ? B candidate(v1) : v1
next registered state = v2
```

This notation describes known Boolean controls. Implementation must retain the
compiler's four-state checks, reset semantics and failure behavior; an unknown
enable cannot silently be treated as false. Ordering must follow actual state
owner identity, including reads without writes. Lexical variable names and
source declaration order do not establish an order.

## Acceptance examples

Use literal expected results independent of compiler output. Every case must
compile and link through the public driver, emit both targets from the same
verified final artifact, and execute generated C++ and RTL.

| Initial state and Rules | Declared order | Expected next state |
| --- | --- | --- |
| `x=3`; A adds 1; B doubles | A before B | 8 |
| `x=3`; A adds 1; B doubles | B before A | 7 |
| `x=3`; A adds 1; B doubles if `x==4` | A before B | 8 |
| `x=3`; disabled A adds 1; B doubles | A before B | 6 |
| `x=3`; A adds 1; disabled B doubles | A before B | 4 |

Resource-blocked cases additionally establish final commit behavior: blocking
A holds all of A's effects while allowing B; blocking B preserves successful A.
Existing unordered, reset, atomicity and source-authentication tests remain
separate regression evidence. Cycles and unordered overlapping writers must
fail rather than acquire an arbitrary priority. Cross-instance ordering and
multiple-predecessor joins require separate design work.

A single predecessor per declaration still supports `A -> B -> C` and longer
chains: all three Rules may write the same variable. A join instead declares
both `A -> C` and `B -> C` without saying how A and B relate. The candidate does
not infer an order between such writers.

The current functional tests cover both two-Rule orders, forwarded guards,
disabled predecessors, Method/Queue-blocked roots and three-Rule chains with a
writing or non-writing middle Rule. Numerical oracles are literal, independent
of compiler output. Both backends consume the same final artifact. Additional
negative tests preserve existing publications on invalid ordering; native reload
tests reject erased/cyclic order, wrong data/enable captures and a forged entry
witness. Historical fixtures remain negative for unsupported registration forms.

The earlier decorator-based candidate passed 18 public tests and three native
suites; its SDK and receipts remain separate historical evidence. Positive
cases agree across C++ workers 1/2 and Icarus RTL, including X/Z payloads, two
independent instances, interface-only imports and saved-anchor reload. The
standalone example produces `3, 3, 8, 8, 18, 18, 38, 38`. This does not establish
exhaustive four-state control correctness or formal equivalence. No synthesis or
PPA campaign was run. The six existing source-build benchmark cases, including
64 shared instances, remain a separate compile/link/emit/C++-build check.

The centralized-scheduler candidate passes 17 public cases (the migrated 16
cases plus the omitted-Rule case), all three native suites, 73 public-surface/SDK
helper tests and the standalone example. Positive cases agree across C++ workers
1/2 and Icarus RTL. Reversing only the schedule list gives 7 instead of 8. The
unlisted Rule test independently checks continued execution and current-state
reads; renamed imports survive interface-only compilation and saved-anchor reload.
Three representative schedule rejection cases replace the five decorator-form
negative cases; the removed cases are not claimed as current executions.
The source-build benchmark was not rerun for this syntax change; its previous
results above belong to the earlier candidate. Work limits and native forwarding
algorithms are unchanged. Exact candidate files and logs are recorded under the
ignored `docs/gates/logs/central-scheduler-20261105/` directory.

DWire is not implemented. Defaulted same-cycle wires and a counter that combines
independent increment/decrement events remain a separate primitive feature;
ordered register forwarding does not supply that behavior by itself.

## Native implementation boundaries

1. Capture explicit order as source-owned syntax and preserve it in the source
   interface and independently verified summary. Do not execute Python designs.
2. Build a deterministic order over actual Rule registrations. Extend state
   analysis with each owner's incoming version, including guard reads.
3. Forward committed versions in transaction lowering and compose the final
   physical update. Preserve separate root admission and atomicity.
4. Authenticate predecessor identities, forwarded values and final commit in
   standalone hardware verification. Do not relax existing proof checks to
   admit a generated circuit.
5. Preserve source locations and Rule/state names for both backends. Record
   stage cost on the unchanged benchmark before and after the implementation.

The former implementation preceding official commit `fa5ab4cd` is a reference
for state forwarding, not a patch to import wholesale. Its metadata and
registration semantics predate the current independent-root implementation.
Only the relevant state-forwarding/proof machinery is adapted. Current autonomous
registration, receiver checks, indexed-write checks and the scope-index capacity
fix remain in place. No compiler work limits are raised.

The initial forwarding representation retains matching ancestor proposals per
state owner. A long chain can therefore produce quadratic forwarding metadata;
linear-size version publication is future optimization, not a delivered claim.
Existing un-ordered benchmarks and short ordered examples measure different
properties; neither establishes HNI-scale ordered compilation capacity.

## Next features

A DWire-style value has a default each cycle and no retained state. Increment
and decrement should use distinct event wires and one counter updater:
`next_count = count + inc_event - dec_event`. Simultaneous successful events
then cancel without ordering the two event producers. DWire itself does not
define addition of multiple writes to the same wire. Event visibility, multiple
writers, admission dependencies and boundary behavior need their own contract.

Readable RTL should retain module boundaries where possible, readable state and
Rule names, and a map from source location to generated objects. Backend naming
must not change scheduling or behavior. Reuse individual readability changes
from the earlier fork only after reviewing them against this official base.

Compile cost is measured separately for source compile/link, each backend emit,
generated C++ compilation, no-op builds and dependency invalidation. The current
source-unit benchmark is described in the repository's `benchmarks/README.md`.
Small functional examples do not establish HNI-scale compilation capacity.
