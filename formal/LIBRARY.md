# Rule contracts and verified source library

This stage builds on [automatic validation](VALIDATION.md). It adds internal
state mapping, compositional Rule contracts, a small reusable source library,
and one reproducible entry point in the existing test/build infrastructure.
The implementation includes all four capabilities below. This document states
their contracts and acceptance requirements; candidate-specific execution
results are recorded separately. Passing the focused formal checks does not
establish that the broader repository API gate passes.

## State identity and observations

The typed-source exporter records the selected definition and each register's
verified source occurrence identity. Physical RTL emission records that same
identity alongside the actual emitted storage scope/value path and width.
The root-wrapper instance path is emitted from the same naming operation used
to print its instance. These are compiler metadata, not guessed signal names.
The profile remains flat scalar Bits state with one clock/reset domain. General
hierarchical state, collections, memories and native Queue storage are rejected.

The validator binds model register identities to these emitted storage paths,
connects observation wires after process lowering/flattening and before dead
state cleanup, then performs the existing exact ordered-Q/disjoint/all-storage
audit. No debug ports are added to authored sources or emitted production RTL.
Missing, duplicate, extra, reordered or inconsistent mappings must not pass.
One hidden two-register design exercises actual cross-root data dependence,
unequal initial values and independently enabled updates. A hidden-update fault
must produce a concrete next-state counterexample against the fixed model.

Public outputs become typed pure expressions over committed state and inputs.
The minimal expression extension is typed conditional, Boolean-to-one-bit
conversion, and bit concatenation. Struct construction packs declared fields
in the compiler's existing most-significant-field-first order. Inputs/state
remain Bits; arbitrary record operations and source branches remain outside
this export slice. A one-bit OR is explicitly translated through Boolean
negation/conjunction. Existing state-version and snapshot restrictions remain.

The version-two JSON schema records definition identity, register owner keys,
typed public output terms, and next-state terms. The generic encoder only
interprets those typed terms. Output expressions read current reference
registers, not the symbolic next-state bank. SAT relates all state at frame one,
checks public observations at that frame, and checks both state and public
observations at frame two. Both frames' input values remain arbitrary. State
correspondence must never be replaced by an assumption of output equality.
Existing size/depth/work limits also cover output expression construction and
serialization; all encoded state/input/output/term bounds remain explicit.

## Contracts and composition

Contracts use the existing Syntax interpreter and Core schedule, with Empty
events. A Rule contract relates input, entry state and committed exit state,
under a precondition. Candidate obligations cover success, and a separate hold
obligation covers ordinary rejection. This is not an assertion-fault model.

Sequential composition requires the first postcondition to establish the
successor precondition. Each root retains its own rollback boundary. Local
invariant contracts connect to the existing arbitrary finite-history and prefix
preservation theorems.

Structural read/write footprints establish that a Rule preserves registers
outside its writes. Sufficient independence requires each Rule's writes to be
disjoint from the other's reads and writes, including guard reads. Under this
condition, prove the two schedules commute and agree with merging independently
computed entry-state candidates. These are semantic conditions for a possible
parallel implementation, not evidence that the compiler selects such hardware.
No claim about reordering observable nonempty event traces is made.

## Source library and mathematical specifications

The first library contains concrete reusable flat Modules with explicit request
interfaces: Register8, Counter3, Slot8 and Fifo2x8. Register/counter
outputs are scalar; buffer outputs form one named Struct containing ready,
valid and data. Module-owned state and ordinary ordered Rules implement each
component. Clock/reset and physical storage remain compiler-owned. The library
can be independently compiled and instantiated through the existing source-unit
workflow. It adds no frontend or runtime API.
Acceptance includes a separately compiled importing consumer, linked against
the published library unit, with generated C++ and RTL execution evidence.

Buffers implement known-two-state, one-edge availability, no empty bypass,
old-head consumption and downstream-pop replacement. Public data is zero when
invalid. A pop is considered before insertion. Capacity guards belong to this
library's own storage implementation, not duplicated admission around another
resource. Native `ac.queue` has its own existing contract and is not certified
by proofs about these distinct source implementations.
Slot8 denotes a single-entry FIFO with this policy. Counter3 saturates in
increment-then-decrement order: at capacity five with both requests, it becomes
four because the increment rejects before decrement executes.

The two-entry FIFO has front/back payload registers and a two-bit occupancy.
Its three ordered roots consume, append-to-one-entry, and insert-into-empty.
The append root precedes empty insertion so an empty enqueue cannot occur twice.
Each root has a cohesive guarded effect. The invariant is occupancy at most two.
Counts outside that invariant remain included in model/RTL transition checking,
but are excluded explicitly from the abstract queue-refinement theorem.

The abstract queue specification is a list of payloads, with guarded append and
head removal. Proofs quantify arbitrary payloads and arbitrary finite request
histories. For FIFO insertion, prove the two concrete insertion roots together
refine one abstract push; neither concrete root alone has the same admission.
Prove capacity preservation, data order, observation correspondence and history
prefix properties. Single-slot storage refines lists of length at most one.
Register correctness is enabled-write/otherwise-hold; counter correctness reuses
the existing finite-width-to-Nat refinement under representable capacity.

Each actual exported source AST must be connected to the library model through
a kernel-checked obligation. A manually authored mathematical FIFO theorem
without that source connection is insufficient acceptance. Generic symbolic
lowering then connects that AST to the automatically generated RTL reference.

## Integration and acceptance

Extend the existing artifact pytest and its reusable helpers; do not add a
parallel test runner. One documented build/test entry builds the Lean project
and invokes actual native compile/export/link/emit, model obligations, formula
generation, state/output auditing and Yosys comparison for the source library.
Use existing generated System/backend test infrastructure for library use and
independent protocol stimulus; keep mathematical oracles out of source designs.

Required evidence includes:

- hidden-state positive and fixed-reference hidden-update counterexample;
- actual register, counter, slot and FIFO compilation/export/kernel checks;
- multi-register and packed/computed-output RTL equivalence with full state audit;
- independent buffer boundary, stall, simultaneous pop/push and data-order checks;
- independent contract/footprint/commutation acceptance, including dependent
  roots whose order demonstrably changes behavior;
- existing exporter/artifact regressions, source-map/output metadata checks,
  affected compiler gates, clean Lean build/axiom audit, pre-commit and docs.

Preserve raw manifests, tools, commands, receipts and source/artifact hashes.
Commit local checkpoints on explore; unrelated benchmark work stays separate.

The resulting argument remains conditional on source capture/type analysis,
model extraction, metadata, serialization/encoding and solver correctness.
Universal reset, X/Z, physical timing, general compiler correctness, arbitrary
hierarchy/resources, and unbounded/parameterized FIFO implementations are not
established by these bounded components.
