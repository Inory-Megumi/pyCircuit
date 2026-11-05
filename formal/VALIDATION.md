# Automatic Rule model and RTL validation

This stage compares actual emitted RTL with a reference generated from the
[exported Lean Rule model](EXPORT.md), without a handwritten SV transition.
Production compilation continues through the same public compile/link/emit route.
The reference is verification-only and never supplies DUT results.

## Symbolic semantics

`Symbolic.Term` is a typed expression language corresponding to `Syntax.Expr`,
plus a conditional expression. Its state reads denote cycle-entry register
values. Lowering an expression substitutes the current symbolic register bank.
A command produces a speculative bank and an admission predicate. Sequence
passes the first candidate to the second command and conjoins their admission.
Because expressions are total and two-state, speculative later expressions may
be constructed even when earlier admission is false.

Each Rule commits, for every register:

```text
if entry_guard && body_admission then candidate else rule_entry_state
```

The schedule threads these committed banks. Structural proofs relate symbolic
expression evaluation, complete command candidate outcomes, Rule execution and
schedule state to the existing Syntax/Core interpreter. Events are not modeled.

Finite dependent banks are eagerly cached after writes and Rule commits. A
cache identity theorem preserves semantics; caching prevents repeated expansion
of lazy state-transformer functions. Executable preflight runs before symbolic
lowering: at most 64 registers and 64 inputs, depth 256, and a weighted construction budget of
100,000 (counting repeated AST visits and materialized bank entries). Schedule
construction uses a fold. Serialization separately bounds expanded term visits
to 100,000, depth to 256, and encoded text to 8 MiB. Exceeding any limit rejects
the artifact; it never substitutes or truncates a transition.

## Formula artifact and encoding

The driver evaluates the actual `PycircuitExport` definitions with the generic
Lean serializer. It does not parse Lean text or reconstruct the counter. The
JSON artifact identifies schema `pycircuit-rule-transition-v1` and contains:

- `inputs`: ordered rows `{name, type}`;
- `registers`: ordered rows `{name, width, initial}`, with decimal-string initials;
- `outputs`: ordered rows `{name, register}`;
- `next`: one typed term per register.

Types are `{kind: "bool"}` or `{kind: "bits", width: N}`. Every term contains
`op` and `type`. Operations are `boolLit`, `bitsLit`, `input`, `read`, `add`,
`sub`, `ult`, `eq`, `and`, `not`, and `ite`. Literals have `value` (Bool or a
decimal string), reads/inputs have `index`, and other operations have ordered
`args`. Term types, index bounds and operand widths are checked by the verifier
before encoding. The hardware encoder admits positive widths up to 4,096 bits,
at most 4,096 combined register/input bits, at most 64 public outputs totaling
4,096 bits (including aliases), and at most 1,000,000 expanded
term-result bits (the sum of result widths over visited terms). These additional
encoding limits reject oversized formulas before invoking Yosys.

The reusable verifier in the existing system pytest suite emits explicitly
sized unsigned SV wires for those terms and one reference register per source
register. Addition/subtraction truncate at each declared result width. Typed
conditionals encode as ternaries. This serializer and SV encoding remain trusted;
the symbolic-correctness theorem alone does not certify their output bytes.

## State and interface relation

The hardware validator requires at least one register and public outputs to
cover every source register. This is narrower than the exporter profile and
the symbolic theorem. Hidden state is rejected before SAT.
Input/output identities and widths are bound through exported model metadata
and emitted `ports.json`, with clock/reset identified by domain ordinals.
An output mapping chooses a canonical public observation per register; aliases
are retained and every public output is compared.

The full RTL closure comes from `generated.json`. Yosys reads the original bytes
with `SYNTHESIS`, lowers processes without optimization, flattens, and removes
all initialization attributes before optimization. Normalized state is audited:
each canonical register observation must match the ordered Q bits of one DFF
bank of the declared width, register banks are disjoint, all storage is covered,
and every DFF uses the common positive-edge clock. Aliases must observe their
mapped bank; no extra state, memories, latches or unknown constants are admitted.

The SAT assumption relates canonical register states in frame one, with reset
held low. The proof checks next-state and all-output equality in frame two.
A satisfying all-ones state witness checks that initialization has not silently
restricted the relation. Removing initialization is an abstraction for arbitrary
state transition reasoning; it is not a proof of reset or startup behavior.

## Acceptance and identity

Each positive case compiles once, exports its source unit to Lean, serializes
that exact model, and links/emits RTL from the same unit. Receipts bind source,
unit, final IR, generated model, symbolic library, formula, encoder, reference,
miter, raw RTL, normalized netlist, tool identities and solver results.

The original counter and renamed four-bit/capacity-nine counter must pass with
no handwritten reference. Fault controls freeze the original model/formula,
then compile only a changed DUT. Parsed solver traces must show:

| Fault | Current state and requests | Reference next | DUT next |
| --- | --- | --- | --- |
| Increment guard `< 5` changed to `< 4` | 4, increment only | 5 | 4 |
| Increment `+ 1` changed to `+ 2` | 0, increment only | 1 | 2 |
| Reversed Rule order | 0, both requests | 0 | 1 |

Hash/interface/parser failures are not semantic counterexamples. A separate
profile check uses a compiler-accepted design with one hidden register and
requires explicit rejection. Normal checked RTL simulation remains covered by
the independent existing testbench.

This is per-artifact known-two-state, reset-inactive, state/output validation.
It retains trust in capture/type/state analysis, model extraction, serialization,
the verification harness and Yosys. The new Lean theorem covers symbolic
lowering. No general compiler, four-state, reset, physical-timing or resource
correctness theorem is claimed.
