# Bounded counterexample-guided abstraction refinement

This stage adds a CEGAR loop to the existing [counterexample workflow](COUNTEREXAMPLES.md).
It abstracts the transition relation by omitting selected register update equations.
It does not introduce a new source language or compiler route.

## Abstraction and refinement

Let `T(s, i)` be the exported next-state function and `R` the retained register
indices. The abstract transition permits a successor `s'` when the environment
holds and every retained register satisfies `s'[r] = T(s, i)[r]`. Other register
updates are unconstrained values of their declared bit widths. Initial state,
property, environment, inputs and output expressions remain exact.

Every concrete transition satisfies this abstract relation, for every `R`.
Adding a register to `R` strengthens the relation while preserving all concrete
behaviors. The search never assumes the property it is trying to verify.

`tests/system/formal_cegar.py` implements the following loop:

1. Search increasing depths from zero through the stated bound in the current
   abstraction, using the shared typed Z3 encoder.
2. For an abstract candidate, bind **every state and input row**, initialization,
   output, environment and final violation, and check all concrete update equations.
3. If satisfiable, return the concrete case for existing Lean witness checking and
   C++/RTL replay. A candidate is never replayed merely because it is abstract SAT.
4. If unsatisfiable, select an omitted register equation violated at a particular
   edge. Retain that equation globally, record the refinement, and search again.
   If no omitted update explains the discrepancy, report an integration error.

The selected equation excludes that exact path. Retention is strict and monotone;
there can be at most one addition per register, followed by a final search even
after the last permitted addition. This is transition-equation abstraction over
the full state vector, not predicate abstraction or automatic lemma discovery.

## Lean proof boundary

`RuleSemantics/Abstraction.lean` defines the relation using the actual Syntax/Core
schedule interpreter. Its generic proofs establish concrete transition and history
coverage, monotonicity, elimination of a path containing a violated added equation,
and transfer of bounded abstract safety to concrete safety.

`write_lean_refinement` generates a certificate for each applied refinement. It
checks the old abstract path, selected omitted register and violated edge against
the original exported model, and derives exclusion under the new mask. Model,
interface, widths, owners and property identities accompany the certificate.
The concrete result separately uses the existing `Witness.check_sound` certificate.
Certificates use the ordinary Lean kernel without admitted proofs or added axioms.

The Python search and certificate emission are separate APIs: callers must run Lean
on emitted certificates before describing refinements or final witnesses as kernel
checked. The acceptance workflow does so. The generic safety-transfer theorem does
not turn a solver's UNSAT response into a Lean proof of bounded safety. SMT answers,
serialization and source-to-model extraction remain trust boundaries. An encoding
disagreement rejected by Lean is an integration failure, not another refinement.

## Results and artifacts

`search_cegar(formula_path, specification, ...)` returns `pycircuit-rule-cegar-v1`.
Every iteration records its retained register indices, abstract search, concrete
feasibility outcome, and any applied edge/register refinement. Abstract candidates
have a distinct schema and status from concrete cases. Only concrete SAT produces
a `counterexample` field accepted by the existing certificate and replay APIs.

Final outcomes are:

- `counterexample`: a concretely feasible path. Its shortest claim relies on
  abstract UNSAT at all smaller depths and concrete SAT for the reported path;
  that basis is explicitly recorded in the concrete case.
- `bounded_unsat`: no abstract violation through the bound, hence no concrete
  violation within that bound under the model and solver assumptions.
- `unknown`: the first abstract or concrete query was unresolved; stop and record
  the stage and solver reason.
- `refinement_limit`: a spurious candidate needs another equation, but the allowed
  number of additions has been used. This is incomplete, not a safety result.
- `resource_limit`: the aggregate solver-call or formula-work budget was exhausted.
  The interrupted phase and reason remain explicit; no result is invented for it.

Defaults permit all omitted registers to be restored, at most 256 solver checks,
and 16,000,000 accumulated term-bit work units. Each query charges the validated
formula/property work times its path-row count. This is bounded accounting, not a
measurement of solver CPU work. The existing depth limit of 64, per-query timeout,
formula limits and per-unroll work limit remain. Limits may be lowered; a final
search after the last refinement still consumes resources.

Acceptance retains `cegar-result.json`, `Refinement.lean` with its checker log,
the final concrete case/certificate when present, and actual C++/RTL traces and VCD.
Source, model, formula, helper, tool and backend identities use the existing receipts.

## Acceptance and scope

The existing healthy counter and its test-owned `+2` faulty variant start with no
retained equations. Both must produce a spurious depth-one violation and restore
the counter update. The healthy model then returns bounded UNSAT through depth
six. The faulty model produces the actual shortest trace `0 -> 2 -> 4 -> 6`, checked
by Lean and replayed on generated C++ and physical RTL. Independent acceptance
also checks semantic certificate tampering and unresolved/budget outcomes.

Run the existing entry with the optional formal dependencies installed:

```sh
bash tools/run_api_tests.sh --tier gate --formal
```

The first profile remains flat, finite-width and known-two-state. Replay retains
its existing public-state-observation requirements. No unbounded safety result,
automatic invariant synthesis, interpolation, arbitrary Lean-goal translation,
hierarchy/resource generalization or measured speedup is claimed. These examples
restore their only register equation; they establish the loop, not a benefit from
keeping large designs abstract.
