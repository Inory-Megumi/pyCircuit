# Rule semantics exploration

This is the first mechanically checked specification experiment for the
`explore` branch, based on pyCircuit commit
`27f4ae6b435d24738db6a5224428aef75b6663f7`. It asks whether local Rule safety
obligations compose into safety of ordered schedules and finite execution
histories. The mathematical model is separate from the product compiler.

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

The model permits arbitrary total action functions as semantic parameters. It
does not define a source syntax, prove hardware realizability, infer resources,
or establish which action functions the pyCircuit frontend accepts.

## Proofs and their scope

| File | Result |
| --- | --- |
| [Core.lean](lean/RuleSemantics/Core.lean) | Successful action composition forwards candidate state and events; reassociating action composition preserves behavior; a rejected action discards its enclosing transaction; a rejected scheduled successor preserves its predecessor. |
| [Safety.lean](lean/RuleSemantics/Safety.lean) | Local preservation obligations imply preservation by every finite schedule, every admitted finite input/schedule history, and every history prefix. |
| [Counter.lean](lean/RuleSemantics/Counter.lean) | Guarded increment/decrement establish those local obligations for unrestricted natural-number state, and therefore preserve `count ≤ capacity` for arbitrary capacities, bounded initial states, schedules and histories. |
| [Acceptance.lean](lean/RuleSemantics/Acceptance.lean) | Independently derived composite-state, event rollback, candidate-visibility and changing-input history examples. |
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
implements that boundary. Similarly, passing this project establishes no RTL
equivalence, PPA result, productivity improvement, or complete-language theorem.

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

This first model excludes DWire, Queue and memory resources, unordered roots,
cross-module ownership, reset, X/Z, physical clock history, assertion faults,
observation publication, bit-vector wraparound, source admission, and compiler
lowering. No product language, compiler or runtime semantics are changed.

The next concrete proof target is a finite-width counter implementation related
to this natural-number specification by an explicit state relation. After
establishing that connection, module contracts and a selected actual lowering
can be treated as separate refinement obligations. Installing LLVM/MLIR,
Verilog simulators and an RTL formal flow belongs to that compiler-connected
stage; they are not prerequisites for the proofs in this directory.
