# Reachable counterexamples and backend replay

This profile combines the existing proved Rule semantics with Z3 search and
concrete Lean certificates. It produces replay cases for actual generated C++
and physical RTL, including a real simulation VCD. The source capture,
compile/link/emit route is unchanged.

An unfinished Lean proof is not a counterexample. Search requires an explicit
well-typed property. Elaboration errors, unsupported operations, timeouts and
bounded absence of a counterexample retain distinct meanings.

## Search contract

`tests/system/formal_counterexample.py` consumes the version-two transition
formula serialized from an actual exported Lean model. The SV validator and
Z3 path share the checked model/term fold in `formal_rule_model.py`: names,
owner identities, widths, expression types and expansion budgets have one
validation owner. Z3 uses unsigned comparisons and modular bit-vector arithmetic.

The property artifact has schema `pycircuit-rule-property-v1`, a name, a Bool
`property` term and a Bool `environment` term. Terms use the existing transition
expression format. The state property cannot contain input reads; the environment
may refer to state and inputs. Neither term is inferred from a proof error or
from a desired DUT result. In particular, the target property is not assumed
as an invariant restricting reachable states.

The search begins at declared register initial values and checks depths zero
through the requested bound. Each extension adds the actual transition and its
environment condition. The target violation is checked under a temporary solver
scope and is removed before extending the reachable prefix.

Results distinguish:

- `counterexample`: a Z3 candidate with a concrete reachable trace. Its
  `shortest` claim is relative to the recorded environment and supported model,
  and requires every smaller depth to have returned UNSAT. Kernel checking and
  backend replay are subsequent steps, not implied by this search status.
- `bounded_unsat`: every depth through the recorded bound is UNSAT. This is not
  a proof over unbounded histories.
- `unknown`: stop at the first UNKNOWN/timeout and retain the solver reason.
  No counterexample or shortest-prefix claim is emitted.

Unsupported schemas/types/budgets are rejected, while invocation/tool failures
remain errors. Bounds are at most 64 transitions and 16,000,000 weighted
unrolled term bits, in addition to existing formula limits. Solver timeout is
explicit and finite. Arbitrary-state induction witnesses and arbitrary Lean
propositions are outside this reachable-state profile.

## Case and kernel certificate

A case records formula and property digests, source/interface identities,
declared initialization, solver version/timeout, every checked depth and its
status. The source-unit orchestration additionally freezes the source and
exported-model digests before certification. The model digest is required by
`write_lean_witness`; verification receipts bind the native unit, final IR and
both backend artifacts to that source snapshot.

A depth-k candidate contains k+1 rows. Each row records inputs, current state
and current outputs. Only the first k inputs drive transitions and satisfy the
environment. The last input is zero and supplies an observation of the final
state; it does not cause another transition and need not satisfy the environment.

`Witness.lean` checks every row against the original Syntax/Core interpreter,
not the JSON formula or Z3's evaluation. It checks the initial state, complete
state/output vectors, every transition and environmental constraint, and the
final state-property violation. The generated certificate also checks exported
names, source owners, register/input/output types and widths, and initial values.
Concrete equality and `decide` proofs are checked by Lean's kernel.

`Witness.check_sound` proves that a successful check denotes an actual Core
history reaching a violating state. Further theorems establish every advertised
observation and transition environment condition. These reuse the same Rule
semantics and ordinary rejection/hold behavior as earlier composition proofs.
No `sorry`, custom axiom, `native_decide` or raised proof-search limit is used.

The existing symbolic-correctness lemmas support lowering to the transition
representation used in search. This stage does not automatically invent
invariants, discover new lemmas, eliminate state via abstraction, or implement a
general CEGAR loop. The broader abstraction roadmap remains deferred.

## Actual C++ and RTL replay

`formal_counterexample_replay.py` generates test adapters for the actual emitted
models. The first replay profile requires all logical registers to have direct
public output observations and accepts flat Bits inputs. Other computed outputs
are also checked. Unsupported interfaces fail explicitly.

The C++ adapter uses the public generated root, normal Runtime Build/Reset and
Work/check/Xfer execution. It reads back actual input and output ports. C++
logical state is observed through the direct public outputs; it is not described
as independent inspection of private storage. The physical RTL adapter uses
the complete emitted RTL closure with checks enabled and reads state from exact
`rtl-names.json` storage paths matched by source owner/name/width/kind. Its
public outputs are observed separately. No production debug ports are added.

Both adapters check actual initial observations against declared model initials.
There are exactly k rising transitions and k+1 observations, using low-clock
samples for each recorded current state. Every actual input, state observation
and output must agree with the kernel-checked candidate. Unknown values,
physical fault diagnostics, reordered/missing rows and disagreements fail replay.

Artifacts include:

- `counterexample.json`: property, assumptions, solver history and witness;
- `Witness.lean` and its checker log: the concrete kernel certificate;
- `cpp-trace.json` and `rtl-trace.json`: actual backend observations;
- `replay.vcd`: actual Icarus simulation inputs, state probes and output signals;
- `replay-metadata.json`: the two state-observation bases and physical probe paths;
- the existing source/artifact/tool/command receipt.

The VCD is not synthesized from the expected witness. A disagreement between a
checked model and a backend trace is reported as a replay/model/backend
discrepancy; it does not by itself identify which compiler or adapter is wrong.

## Reproduce and acceptance

Install the optional dependency into the Python environment used by the tests:

```sh
python -m pip install '.[formal]'
bash tools/run_api_tests.sh --tier gate --formal
```

The optional extra pins `z3-solver==4.15.4.0`. The existing formal profile also
requires Lean, the native CompilerDev installation, Yosys, Verilator and Icarus.
The [testing guide](../docs/development/testing-and-gates.md#optional-rule-formal-validation)
describes tool paths and retained gate artifacts. Focused development uses the
existing pytest entry with `tests/system/test_formal_counterexample.py` and the
same environment. Use a disposable `--basetemp` to retain replay outputs.

Independent acceptance compiles the existing counter and a test-owned variant
whose increment changes from `+ 1` to `+ 2`. The property remains `count <= 5`.
From initial zero, unconstrained search within the specified environment finds
the shortest three-transition failure `0 -> 2 -> 4 -> 6`, without prebinding
the input sequence. The healthy counter has no violation through depth six.
These are candidate-specific execution results, not an unbounded Z3 proof.

Acceptance also rejects altered input/state/output witnesses in Lean, retains
UNKNOWN as unresolved, and checks meaningful environmental restrictions:
forbidding increment prevents the fault within the bound, while requiring
increment still permits a final zero-input observation. Real C++/RTL traces and
independently parsed VCD values must match the discovered witness.

The result is conditional on source capture/type analysis, model extraction,
metadata and the surrounding tooling. A checked SAT witness reduces trust in
the Z3 encoding for that concrete violation. Bounded UNSAT and shortest-prefix
claims still trust the solver/encoding. Replay startup checks do not establish
universal reset, X/Z, physical timing or whole-compiler correctness.
