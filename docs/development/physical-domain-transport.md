# Physical domain transport

An ordinary child's internal capture outputs and Rule captures may forward a
verified physical clock identity. Projection follows these edges through the
actual bound child occurrence and its yielded value. Collection outputs need
uniform identity across their actual occurrences. Traversal keeps the existing
depth and work limits.

Every real consumer remains checked. Arithmetic, selection, data conversions
and root output payloads cannot consume a clock. Sampling and storage must
still use the actual root clock/reset pair, authenticated independently of the
transparent capture edge. A child result's ordinal or name grants no domain
identity by itself.

This check does not mutate common IR, change transaction concurrency or add
storage. It is separate from readable Verilog presentation. Focused positive
and negative cases live in tests/system/test_physical_domain_forwarding.py;
the existing projection rejection suite remains required.
