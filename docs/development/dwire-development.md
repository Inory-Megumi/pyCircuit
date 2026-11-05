# Same-cycle DWire

This local implementation follows the centralized-scheduler candidate on
`codex/rule-order-20261105`. It does not select a new default SDK. The implemented
scope is scalar Bits with the drive and atomicity contract below.

```python
increment: bits[1] = dwire()
decrement: bits[1] = dwire()
data: bits[32] = dwire()
```

There is one wire API, `dwire()`, for flags and wider data. It takes no arguments;
the annotation supplies its type. The user selected this unified interface on
2026-11-05. There is no separate data-wire declaration or user-specified default.
An annotated Module variable initialized with `dwire()` is combinational, not a
register. Assignments inside a Rule or its
called Methods propose writes. The value visible to other Rules and Module
outputs is the final successful writer's value, or compiler-driven zero if that
entire root does not commit or executes no assignment. This rule is identical
for one-bit flags and wider values. Readers do not wait for a writer. No value
survives to the next sample. Both backends must
consume the same verified final graph and emit no storage for this declaration.

Conceptually the drive is `value = writer_fire ? writer_data : 0`, with
conditional writes inside the Rule included in the write intent. A one-bit
write of `1` therefore produces the corresponding successful-write pulse.
Zero is an idle combinational value, not an initialization or reset value.

The first supported payload is scalar Bits. One actual atomic root may write a
wire; multiple roots writing the same wire reject even when listed in a schedule.
Repeated assignments in the same root retain ordinary last-assignment semantics.
Reading and writing the same wire within one atomic root rejects, including
through Methods and guards. Explicit Rule ordering does not turn a wire into a
register or supply priority among wire writers. Separate wires remain independent.

Read-after-write dependencies are ordinary same-cycle combinational dependencies,
independent of declaration order. Cycles reject; no fixed point, inserted cycle,
hidden storage or arbitrary arbitration is permitted. An X/Z payload remains
data; reached unknown control still follows the existing compiler checks.
Reset retains the ordinary register reset behavior. The wire is combinational
even during reset, and has no independent reset history.

A reader is a separate atomic root. If it is blocked, an already-successful writer
does not roll back: DWire is not a reliable event queue or an acknowledgement.
A counter implemented with two event wires therefore uses one unconditional,
nonblocking updater. Its effects must be checked as an object property. It must
not depend on an updater's final result to decide the producer's admission.

For unit increment/decrement, both false and both true hold the count directly.
Otherwise the counter adds or subtracts one. The Bits demo uses modular arithmetic
and checks cancellation at both boundaries. Capacity admission, saturation,
automatic priority, multiple same-kind producers and cross-cycle retention are
separate contracts, not implicit DWire behavior.

Qualification must cover return to zero, wider payloads, writer rollback,
reader independence, guards, Methods, multiple instances, reset and X/Z payloads;
representative rejection checks cover multiple writers and combinational cycles.
Standalone routed/final verification must authenticate zero, the declaration,
writer's final enable and the combinational physical implementation.

The runnable example is `examples/dwire_counter`, with a README and generated
System scenario. C++ workers 1/2 and Icarus agree for its ten sampling epochs.
Public checks cover 1/8/32-bit use, zero idle behavior, conditional and Method
writes, writer rollback, reader independence, boundary cancellation, X/Z data,
reset and reached unknown controls. Independent provider compilation, two actual
instances and saved-anchor reload use the same native link/emit path. Native
refinement tests reject substituted data, idle values and final enables.

The reached-control test follows existing sampling semantics: a prior low epoch
can publish; an X/Z guard faults before the rising epoch publishes or commits.
Formal proof, synthesis/PPA, general Enum/Struct payloads and independent agent
review are not included in this qualification. No work budget was raised.

The earlier argument-taking prototype and its evidence remain under the ignored
`docs/gates/logs/dwire-progress-20261105/` identity. Its nonzero-default tests do
not describe this interface. A separate current qualification records the
no-argument cases and their independently derived zero-idle expectations.
