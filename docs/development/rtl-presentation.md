# Typed RTL presentation

Hardware RTL export prepares one read-only presentation graph after common IR
verification and optimization. Physical and synthesis modes use this graph;
managed RTL retains its simulation ABI. This work does not change source
admission, scheduling, storage, resource sharing or the selected SDK.

## Planning before printing

The graph records original SSA values, exact forwarding aliases, typed input
relations, actual output and instance-pin consumers, and source provenance.
Storage and opaque ownership boundaries stop traversal. Whole-value strongly
connected components remain conservative layout clusters: the existing common
verifier owns field-sensitive legality, and presentation must not reject a legal
record-field dependency as a hardware cycle.

Explicit worklists compute liveness, conservative four-state facts, unique or
shared consumer context, and source-root ownership. Aggregate field and element
slots carry context along typed edges. Actual root registration and receiver
identity distinguish same-spelled Rules in different instances. Shared ownership
remains shared instead of selecting the first caller visited.

Source bindings take precedence over generated labels. Anonymous labels combine
an endpoint or source role with an operation or result-slot meaning. Generated
identifiers use the common legal-name policy; explicitly authored SystemVerilog
keywords retain their source identity through standard escaped identifiers.
Long formulas are not serialized into generated names. Collision suffixes are
local disambiguators, not global SSA identities.

One-bit projections use finite four-state operator tables and preserve exact
X/Z behavior. Materialization uses typed graph cost, independent of identifier
length. A scalar expression has a 12-unit planning limit; large aggregate lists
stay shallow lists. Shared producers retain a single materialized definition.
Optional structured layouts honor the planned boundaries. Pattern-specific
formatting may decline a layout; the total typed plan still supplies context and
materialization rather than an unqualified numbered wire.

## Publication and verification

Every hardware module publishes a `typed-rtl-presentation-v1` plan in
`rtl-names.json`. Each live value has its original identity, context, consumers,
source scope, materialization reason and expression cost. Hardware publication
requires complete live coverage and zero unplanned emitted values. The export
also checks that the verified common artifact is unchanged.

Tests exercise source renaming, dead-code insertion, shared arithmetic, deep
control, typed result slots, Enum/Table layouts, legal field dependencies,
multiple instances, and finite four-state projections. Comparing both emitters
on the same verified final artifact isolates presentation from unrelated frontend
changes. These checks establish concrete invariants, not universal subjective
readability or full formal equivalence.

The current authoring support scope is native Rule/Method and `pycircuit.lib`.
Historical `arch_primitives` and Compose examples keep their previous identities;
this presentation change adds no compatibility path for them.
