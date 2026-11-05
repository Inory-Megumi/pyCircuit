# Minimal Rule syntax and semantics

This milestone gives Rules an explicit, closed syntax in Lean. It is a
formalization layer, not a second pyCircuit compiler or a new authoring API.
The existing Python compiler remains the production compilation route.

## Scope and representation

A finite signature declares register widths and input types. Registers contain
fixed-width unsigned BitVec values; inputs may be Boolean or BitVec values.
Expressions are indexed by their value type. Constructors represent literals,
register reads, input reads, same-width modular addition/subtraction, unsigned
less-than, equality, Boolean conjunction and negation, typed conditionals,
Boolean-to-Bits(1) conversion and high/low concatenation. Expressions contain no
arbitrary Lean functions that could hide a program's transition semantics.
Evaluation is pure and total. Mixed-width arithmetic and ill-typed writes are
excluded by the syntax's type indices.

The shared register-update operation has proved read-after-write and
unrelated-register preservation laws. Interpreter correspondence alone would
not detect a mistake shared by both interpretations in that operation.

The mathematical BitVec width parameter may include zero, as in the existing
BitVec model. This does not claim that pyCircuit admits zero-width source types.
The counter and independent multi-register examples use positive widths.

Commands are skip, typed register assignment, sequential composition, and an
admission requirement. Each assignment evaluates its right-hand side in the
current candidate state. Later commands observe earlier candidate writes.
An admission requirement that evaluates false rejects the entire candidate.
It represents ordinary ineligibility inside this semantic core, not Python
`assert`, a product language statement, or a whole-system fault.

A Rule has an entry guard and a command body. Its entry guard sees the state
at that Rule's invocation. A successful body commits its entire candidate;
rejection returns the entry state. An explicit ordered schedule invokes each
Rule with its own atomic boundary, forwarding accepted state to the next Rule.
The input environment is unchanged within a cycle. Finite histories may vary
inputs and ordered schedules from cycle to cycle.

There are no local bindings or saved-value snapshots in this first syntax.
Resources, calls, loops, unordered roots, reset, clocks, X/Z values, faults,
observable events, and source admission are outside its scope. In particular,
input Booleans model known request bits; they do not redefine pyCircuit `u1`.

## Two interpretations and proof obligations

The direct interpreter evaluates command syntax into `Option State`. Its
rejection result carries no partially updated state. Rule execution converts
rejection to a hold of the Rule's entry state. Schedules and histories execute
these Rules sequentially.
Schedules and histories reuse the existing Core executors through a direct
candidate adapter; no independent scheduling framework is introduced.

A separate structural interpretation maps the same syntax to existing
`Action` combinators: assignment to `modify`, requirement to `guard`, and
sequence to `bind`. It uses `Empty` as the event type. The Rule entry guard is
composed with the interpreted body; the existing `runRule` supplies rollback.

Structural induction establishes equality of the full candidate outcomes,
including rejection, between the direct interpreter and Action interpretation.
The equality then lifts to Rule execution, schedules, and finite histories.
Existing local invariant-preservation obligations transfer to the syntax
interpreter and every finite history prefix. These are semantic consistency
theorems, not a proof that the product compiler accepts or preserves the syntax.

## Counter connection and acceptance

The counter is defined once as syntax: one three-bit register, two Boolean inputs,
guarded increment/decrement Rules, and an increment-then-decrement schedule.
Its behavior is obtained by the generic interpreter; there is no counter-specific
transition evaluator. `SyntaxCounter.step_refines` proves that the observed
register after one cycle equals `CounterReference.step`. `history_refines`
lifts that result to arbitrary finite request histories; Nat correspondence and
bounds reuse the existing reference theorems. Correspondence covers all eight
encoded initial states. Bounds additionally require an initial count at most five.

Independent acceptance checks exercise literal expected results for forwarded
multi-register writes at different widths, modular arithmetic, late rejection
with whole-root rollback, preservation of an earlier independent root, and the
counter's order-sensitive empty boundary. Both interpretations satisfy the
independent expectations through kernel-checked concrete evaluation, without
using the interpreter-correspondence theorem to derive either expected result.

The handwritten `SyntaxCounter` mapping is manually reviewed. The
[typed-IR exporter](EXPORT.md) separately constructs syntax data from the native
compiler's published source artifact and checks it with independent obligations.
The exporter and upstream capture/type analysis remain trusted. The subsequent
[symbolic lowering](VALIDATION.md) proves a generic connection from this syntax
to typed next-state terms, then generates a reference for actual RTL validation.
Serialization, SV encoding and Yosys remain trusted; no kernel-checked theorem
about the emitted RTL bytes is claimed.

## Validation and ownership

Implementation belongs in `lean/RuleSemantics/Syntax.lean` and
`lean/RuleSemantics/SyntaxCounter.lean`; independent examples belong in
`lean/RuleSemantics/SyntaxAcceptance.lean`. The integration owner updates the
default audit imports and this documentation. Independent design/decomposition,
implementation, acceptance, and final review follow repository governance.

Run a clean Lake build and warning-as-error axiom audit. Proofs must use no
`sorry`, custom axioms, unsafe execution, or `native_decide`. Run changed-file
formatting and strict documentation checks. Record fresh validation and exact
content identities in ignored local gate logs; do not use those logs as test
inputs. No product compiler changes, additional backend, or new test runner
belong to this milestone.
