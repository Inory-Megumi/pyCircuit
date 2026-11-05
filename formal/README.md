# Rule semantics exploration

This proof project explores Rule composition and refinement on the `explore`
branch, with pyCircuit source baseline
`27f4ae6b435d24738db6a5224428aef75b6663f7`. The initial proof checkpoint is
`8533455424d7a23d55cce284cd030dc899a19873`. Local Rule safety obligations compose
into safety of ordered schedules and finite execution histories. A separately
defined BitVec counter now refines the natural-number specification under an
explicit capacity constraint. An artifact experiment connects exported Rule
models to actual compiler output through automatically generated RTL references.
The [minimal syntax core](SYNTAX.md) adds closed typed Rule expressions and
commands whose behavior comes from generic interpreters.
The [typed-IR model exporter](EXPORT.md) derives that syntax automatically from
the native compiler's published source artifact within a deliberately bounded
profile. It preserves the existing capture/compile/link/emit route.
The [symbolic validation](VALIDATION.md) proves lowering from Rule syntax to
typed transition terms and compares a serialized model with same-unit RTL.
The [contract and source-library stage](LIBRARY.md) extends that route to
internal state, computed observations, Rule contracts and reusable buffers.
The [counterexample workflow](COUNTEREXAMPLES.md) adds reachable Z3 search,
kernel-checked concrete witnesses, and actual C++/RTL trace and waveform replay.
The [bounded CEGAR loop](CEGAR.md) adds transition-equation abstraction, concrete
feasibility checks and kernel-checked elimination of spurious paths.
The [roadmap](ROADMAP.md) records the original proposal and deferred directions.

## Reproduce

Install [elan](https://github.com/leanprover/elan), the Lean toolchain manager.
The project pins the official `leanprover/lean4:v4.35.0` release and uses only
its bundled standard library; it has no Mathlib, Python or SMT dependency.

From this directory:

```sh
cd lean
elan toolchain install leanprover/lean4:v4.35.0
lake build
lake env lean -DwarningAsError=true RuleSemantics/Audit.lean
```

On Windows, elan's executables are normally under `%USERPROFILE%\.elan\bin`.
Restart the terminal after installation if that directory is not yet on PATH.
`lake build` checks every imported proof and independent acceptance example.
The audit command prints the transitive axioms of the principal theorems even
when the build is already up to date. For a fresh verification, run `lake clean`
followed by `lake build`.

The library treats warnings as errors. Proofs must contain no `sorry`, `admit`,
custom axioms, `unsafe` declarations or `native_decide`. Concrete examples use
kernel-checked `decide`; arithmetic obligations use Lean's proof-producing
`omega` tactic. The axiom report distinguishes Lean's standard logical axioms
from an admitted proof such as `sorryAx`. The trusted foundation includes Lean's
kernel and the installed official toolchain; this experiment does not verify
the theorem prover itself.
Current contract commutation and counter-library proofs additionally use Lean's
standard `Classical.choice`; it is reported explicitly alongside `propext` and
`Quot.sound`. No custom axiom or admitted proof is used.

## Execution model

An `Action State Event Value` maps an incoming candidate state to either:

- `some (value, nextState, events)`: an accepted result;
- `none`: ordinary resource/guard ineligibility.

Action composition forwards candidate state and accumulates abstract events.
If a later action rejects, the entire enclosing action returns `none`.
`runRule` is the outer atomic boundary: it accepts all resulting state and
events together, or returns the original state and an empty event list.

`runSchedule` invokes that boundary separately for each Rule. Later Rules read
the accepted candidate version from earlier Rules, including in their guards.
A rejected successor does not undo a predecessor. These are intermediate
versions within one successful abstract cycle, not multiple physical clock
edges. Every Rule in one cycle receives the same input. `runHistory` permits
both a new input and a new finite schedule on every cycle.

`none` is **not** an assertion failure, unknown-control fault, or whole-system
failure. Such failures have different discard semantics in pyCircuit and are
outside this first model. Events represent abstract transactional effects;
their list order does not claim to model sampled `log`/`report` publication.

The abstract Action model permits arbitrary total functions as semantic
parameters. The new syntax layer restricts programs to explicit expression and
command constructors and interprets them into that model. Neither layer proves
hardware realizability, infers resources, or establishes frontend admission.

## Proofs and their scope

| File | Result |
| --- | --- |
| [Core.lean](lean/RuleSemantics/Core.lean) | Successful action composition forwards candidate state and events; reassociating action composition preserves behavior; a rejected action discards its enclosing transaction; a rejected scheduled successor preserves its predecessor. |
| [Safety.lean](lean/RuleSemantics/Safety.lean) | Local preservation obligations imply preservation by every finite schedule, every admitted finite input/schedule history, and every history prefix. |
| [Counter.lean](lean/RuleSemantics/Counter.lean) | Guarded increment/decrement establish those local obligations for unrestricted natural-number state, and therefore preserve `count ≤ capacity` for arbitrary capacities, bounded initial states, schedules and histories. |
| [Acceptance.lean](lean/RuleSemantics/Acceptance.lean) | Independently derived composite-state, event rollback, candidate-visibility and changing-input history examples. |
| [Refinement.lean](lean/RuleSemantics/Refinement.lean) | Exact candidate correspondence lifts to Rule execution, operation-family schedules and varying-input histories, preserving projected state and ordered events. |
| [BitVecCounter.lean](lean/RuleSemantics/BitVecCounter.lean) | Unsigned guards and modular BitVec updates refine the Nat counter for arbitrary widths and representable capacities; Nat safety transfers to every finite history prefix. |
| [BitVecAcceptance.lean](lean/RuleSemantics/BitVecAcceptance.lean) | Independent finite-width boundary, event-history and out-of-range-capacity examples. |
| [CounterReference.lean](lean/RuleSemantics/CounterReference.lean) | A separate three-bit combinational reference refines the fixed increment/decrement schedule and its Nat state for arbitrary finite request histories. |
| [CounterReferenceAcceptance.lean](lean/RuleSemantics/CounterReferenceAcceptance.lean) | All eight encoded states and four request combinations, plus independent boundary and order checks. |
| [Syntax.lean](lean/RuleSemantics/Syntax.lean) | Closed typed expressions and commands, direct candidate evaluation, structural Action interpretation, register-update laws and correspondence/invariant lifting. |
| [SyntaxCounter.lean](lean/RuleSemantics/SyntaxCounter.lean) | A counter defined as Rule syntax, interpreted generically and connected to the existing reference and Nat history proofs. |
| [SyntaxAcceptance.lean](lean/RuleSemantics/SyntaxAcceptance.lean) | Independent heterogeneous-register, forwarding, modular arithmetic, rejection/rollback and schedule-order expectations. |
| [Symbolic.lean](lean/RuleSemantics/Symbolic.lean) | Typed symbolic terms, finite cached banks, and expression/command/Rule/schedule state correspondence with the syntax interpreter. |
| [SymbolicSerialize.lean](lean/RuleSemantics/SymbolicSerialize.lean) | Bounded executable lowering and JSON serialization; output encoding remains trusted. |
| [SymbolicAcceptance.lean](lean/RuleSemantics/SymbolicAcceptance.lean) | Independent literal checks of heterogeneous forwarding, rollback and preservation of earlier roots after symbolic lowering. |
| [Contracts.lean](lean/RuleSemantics/Contracts.lean) | Pre/postconditions, sequential composition, frame/read-write locality, and sufficient independence for commutation and snapshot merge. |
| [Library.lean](lean/RuleSemantics/Library.lean) | Register, ordered counter, single-entry FIFO and two-entry FIFO models; abstract list correspondence and capacity/history properties. |
| [LibraryAcceptance.lean](lean/RuleSemantics/LibraryAcceptance.lean) | Independent frame/commutation checks, an order-sensitive guard dependency, and full FIFO replacement with arbitrary payloads. |
| [Witness.lean](lean/RuleSemantics/Witness.lean) | Full concrete-trace checking implies reachable property violation, with state/output observations and environmental constraints tied to Core execution. |
| [Audit.lean](lean/RuleSemantics/Audit.lean) | Transitive axiom reports for principal proof results. |

The generic safety theorem assumes each Rule preserves an invariant. It does
not automatically prove that local obligation for arbitrary Rules. The counter
proof discharges the obligations for actual guarded arithmetic definitions.
Its state is `Nat`, rather than a bounded type or a clipped value, so its upper
bound is a theorem about the transitions. Capacity zero is included. This is a
bounded mathematical counter, not the modular fixed-width counter in existing
pyCircuit examples.

Two counter results expose the limits of composition:

- From zero, for any positive capacity, increment then decrement ends at zero;
  decrement then increment ends at one. Both preserve bounds, so safety alone
  does not justify reordering.
- At capacity one, two increments in separate roots from zero end at one
  and retain the first event. Putting those increments in one Rule rejects the
  entire transaction and ends at zero with no events. Rule fusion requires a
  separate semantic argument.

Repeated operation entries denote separate abstract root invocations. They do
not authorize repeating a source Rule name in `schedule(...)`, which the
current language rejects.

The rollback lemmas follow the chosen semantics; they specify the boundary and
check internal consistency. They do not prove that the existing compiler
implements that boundary. The Lean build alone establishes no RTL equivalence,
PPA result, productivity improvement, or complete-language theorem.

## Finite-width refinement

`BitVecCounter` uses `BitVec width` state, unsigned BitVec comparisons against
encoded bounds, and modular BitVec addition/subtraction. Its transitions do
not invoke the Nat counter. Both implementations use the same request,
operation and abstract event types.

The state projection is `count.toNat`. For every input and every BitVec state,
the local refinement proofs establish equality of complete candidates:
ordinary rejection agrees, and accepted values, projected state and events
agree. The parameter condition is:

```text
capacity < 2 ^ width
```

The increment guard implies that adding one stays at or below capacity and
strictly below the modulus. The decrement guard implies that subtracting one
does not underflow. Thus the actual modular updates agree with the Nat updates
on every accepted branch. Representability of one is proved only in those
branches; it is not assumed for zero-width values.

Instantiating the generic refinement lemmas gives, for every finite history:

```text
projectResult BitVec.toNat
  (BitVecCounter.executeHistory width capacity history count)
  = Counter.executeHistory capacity history count.toNat
```

This equality includes the complete ordered event list and needs no initial
capacity-bound hypothesis. Transferring the safety theorem additionally
requires `count.toNat ≤ capacity`. Under that initial condition, every history
prefix remains bounded. At capacity zero, this condition restricts the initial
state to zero; an out-of-bound nonzero state can still decrement.

Widths and capacities are universally quantified, including maximum capacity
`2 ^ width - 1`. Width zero is a mathematical BitVec boundary case: only capacity
zero satisfies the parameter condition. It does not establish admission of
zero-width pyCircuit source types, which require positive widths.

The capacity condition cannot simply be dropped. At width two, encoding capacity
four truncates it to zero: an increment request from zero is rejected by the
BitVec model, while the Nat model accepts it and emits an increment event. The
independent acceptance file proves this concrete difference, as well as the
last admissible increment, full/empty rejection, order-sensitive behavior and
a changing-input history.

This is a proof about two independently authored Lean models. Connecting either
model to a captured pyCircuit program or generated RTL requires additional
evidence, described below. The guarded bounded counter has different behavior from
the existing DWire example's deliberately wrapping counter.

## Connection to pyCircuit

The intended source of the ordered-root behavior is the current
[language reference](../docs/reference/language.md), particularly explicit
`schedule(...)`, same-Rule sequential candidates, and separate root admission.
The [ordered Rule development record](../docs/development/ordered-rule-development.md)
provides additional examples; its old statement that DWire is unimplemented is
superseded by the [DWire contract](../docs/development/dwire-development.md) and
the current language reference. The
[physical RTL presentation](../docs/development/rtl-presentation.md) documents
the current export and source mappings. Historical proposal status is not
treated as implementation evidence.

The Lean models exclude DWire, Queue and memory resources, unordered roots,
cross-module ownership, reset, X/Z, physical clock history, assertion faults,
observation publication, source admission, and compiler lowering. BitVec modular
arithmetic is modeled; the guarded refinement proves that accepted updates do
not wrap under its stated parameter condition. No product language, compiler
or runtime semantics are changed.

The [counter artifact experiment](artifact/README.md) compiles actual sources,
exports their typed Rule models, and links/emits RTL from the same units. A
generic proved symbolic lowerer produces next-state terms. Executing the Lean
serializer and a verification-only SV encoder replaces the handwritten SV
reference. Yosys compares arbitrary related states across one clock edge.
The original counter and a renamed four-bit variant exercise this route;
guard, arithmetic and schedule mutations require concrete semantic mismatches.
Hidden state is bound through verified source-owner identities and actual
emitted storage paths. All stored state remains part of the relation.

This connection covers state and public outputs of each generated artifact's
known-two-state, reset-deasserted synthesis projection. Model extraction,
serialization, SV encoding and Yosys frontend/lowering/SAT remain trusted; no
RTL certificate is checked by Lean. The model-level counter proofs still
connect the original counter to Nat safety. Module contracts, general compiler
refinement, and the excluded behaviors remain separate proof obligations.
LLVM/MLIR, Yosys and Verilator are prerequisites for the artifact tests, not for
the standalone Lean proofs.
