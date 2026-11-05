# Rule exploration roadmap

Recorded on 2026-11-06 after the delivered library checkpoint `596ccae`.
This preserves the planning discussion. The first bounded search/certificate/
replay slice is now implemented in [counterexamples](COUNTEREXAMPLES.md).
The subsequent [bounded CEGAR stage](CEGAR.md) adds equation abstraction and
counterexample-guided refinement. Predicate synthesis and broader composition
directions below remain deferred.

## Deferred direction

The user deferred the broader roadmap while exploring counterexample debugging:

1. Generalize register/counter/buffer widths and supported capacities, reusing
   component contracts and proofs across instances.
2. Develop cross-module composition using interface contracts, including state
   isolation, Method calls, admission and transaction boundaries.
3. Generate explicit proof obligations and verification receipts through the
   existing compile/export/validate route.
4. Extend hardware semantics, beginning with reset establishing invariants;
   four-state behavior and further resources need their own semantics.

The proposed integration example is a two-buffer pipeline: derive capacity,
ordering, no-loss and no-duplication properties from component contracts, then
connect the composition to actual generated RTL. Progress/liveness would need
explicit environmental fairness assumptions in addition to safety properties.
These items remain deferred, not completed or currently being implemented.

## Current question: Z3 counterexamples and executable replay

The user proposes combining Lean with Z3 to find failing cases and show them
in C++ traces and waveforms. The proposed responsibility split is:

- Lean defines/checks semantics and properties, proves general theorems, and
  checks a concrete witness against the actual exported Rule model.
- Z3 searches a supported finite-width property/transition fragment for a
  counterexample. It consumes the existing typed model/formula, not Python
  source text or arbitrary failed Lean goals.
- Generated C++ and RTL replay the same concrete input sequence independently.
  Backend observations are checked against the kernel-checked model trace.

An unfinished Lean proof is not evidence that a property is false. A tactic
failure may mean the proof needs another lemma; an elaboration/type/tool error
is not a semantic counterexample. Automatic search first requires a well-typed
explicit property and a supported transition model. Unsupported properties
must be reported, rather than silently approximated into a different claim.

### Reachable safety counterexamples

For an explicit state predicate P, environment constraint E and transition T,
the initial search asks whether this formula is satisfiable at depth k:

```text
Init(s[0])
and T(s[0], input[0], s[1]) and ... and T(s[k-1], input[k-1], s[k])
and E(s[0], input[0]) and ... and E(s[k-1], input[k-1])
and not P(s[k])
```

Search increasing depths from zero to a stated bound. This gives a shortest
violating prefix only when every smaller depth was checked UNSAT. A timeout or
UNKNOWN leaves that depth unresolved. UNSAT through a finite bound is a bounded
result, not a proof over arbitrary histories. Transition/output predicates
also need explicit input and observation phases rather than being treated as
state predicates by default.

An induction-step or contract counterexample starting in an arbitrary state is
reported separately: it may expose an insufficient invariant or precondition.
It must not be called an executable startup trace unless a reachable prefix is
also found. Backend state injection, if ever supported, needs an explicit label.

Init initially denotes the declared model initial state. A replay adapter must
demonstrate the corresponding backend starting state using its actual startup
or reset mechanism. An assumed initial state does not establish reset semantics
or universal reset correctness.

### Concrete witness and replay

Keep one case artifact containing source/model/property identities, finite
widths, initial-state and environmental assumptions, ordered per-cycle inputs,
model states/outputs, the first violation and solver status/bound. Property
identity remains independent of any deliberately faulty DUT implementation.

For the supported decidable fragment, generate a concrete Lean obligation
checking the exported model's execution of those inputs, every advertised state
and output observation, the initial/environment constraints and the failed property.
The kernel checks the resulting proof; Z3's SAT answer alone is not acceptance.
This certifies the concrete model witness, not the general Z3 encoding or the
source-to-model exporter. UNSAT proof certificates are outside the first slice.

Replay inputs through existing generated-model/System adapters. Record named
inputs, states and outputs at defined Work/Xfer or clock-edge phases. Preserve
source occurrence mappings and compare every advertised observation to the
model witness. Observing the state after the last transition may require one
additional observation phase without counting it as another transition.

Emit a text/JSON C++ trace and an actual RTL simulation VCD via the test harness.
A VCD synthesized from the mathematical witness, if useful, must be labeled a
model waveform and kept distinct from an observed RTL waveform. Additional
verification probes belong in test adapters, not authored production modules.
Rule guard/commit explanations can later come from interpreter instrumentation;
the current final-state formula alone does not retain those observations.

The possible outcomes must stay distinct:

- SAT with a Lean-checked reachable witness and matching backend replay:
  demonstrated property violation for that design/specification.
- SAT rejected by the concrete Lean check: an encoding/integration discrepancy.
- A checked witness whose backend observations differ: a model/backend or replay
  discrepancy; inspect mapping and sampling before attributing a compiler bug.
- Bounded UNSAT, UNKNOWN/timeout, unsupported property, and tool failure:
  separate results, none labeled a discovered counterexample.

### Proposed first acceptance example

Use the existing three-bit, capacity-five counter and an independent property
`count <= 5`. In a test-owned faulty variant, change increment `+ 1` to `+ 2`
while retaining the guard `count < 5`. From declared initial count zero, three
increment-only transitions give `0 -> 2 -> 4 -> 6`, violating the property.
This is an illustrative, analytically derived case, not a new executed result.

The acceptance target is for Z3 to discover a reachable violating sequence
without prebinding those inputs, Lean to check the concrete violation, and the
actual generated C++/RTL to reproduce it. Preserve the original healthy design
as a bounded no-counterexample control. Its existing unbounded correctness
theorem remains separate evidence from that bounded search.

No new language frontend or alternate compiler is needed. First implementation
should reuse the typed Rule expressions/transition serialization, native source
units and existing system-test infrastructure. It must preserve bit widths,
unsigned comparisons, modular arithmetic and source identities. Initial scope
is the existing flat, known-two-state profile; general properties, resources,
hierarchy, X/Z and arbitrary Lean-to-SMT translation are excluded.

## Implementation follow-through

The current Yosys validator already retains fixed-reference semantic
counterexamples, but its negative-control API binds specified states and inputs.
The library consumer already has generated C++/RTL execution and independent
trace oracles. The first automatic Z3 search, concrete-witness Lean certificate,
shared case artifact and actual backend waveform workflow is described in
[counterexamples](COUNTEREXAMPLES.md). The [bounded CEGAR stage](CEGAR.md) now
adds refinement by restoring omitted register equations. Automatic lemma discovery,
predicate abstraction and the broader cross-module roadmap remain future work.
