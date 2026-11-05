# DWire counter

This example requires the local `codex/rule-order-20261105` DWire candidate.
Declare the same `dwire()` for one-bit flags and wider Bits values. It takes no
arguments and owns no storage. Successful writes drive the wire in the same
cycle; otherwise the compiler drives zero. The payload width comes from the
annotation. No user-authored default value or separate data-wire API is needed.

`Counter` has independent increment and decrement Rules. Both may fire together,
and the unconditional updater holds when both or neither request is present.
There is no priority or `schedule` between the two requests. The 8-bit counter
wraps on a lone increment/decrement at its boundaries; simultaneous requests
hold even at a boundary.

The scenario applies both requests, increment only, decrement only, and neither.
Starting at 3, the observable count is `3, 3, 4, 3, 3`. Each value is logged at
the low and high clock samples before the edge commits the next value.

```sh
pycircuit run examples/dwire_counter --cycles 5
pycircuit run examples/dwire_counter --target verilog --cycles 5
```

Select the candidate installation with `--toolchain /path/to/install-dwire`.
Only the counter and scenario phase retain state; `inc` and `dec` are
combinational. Each DWire has one atomic writer root. Methods retain the calling
Rule's commit boundary, and a failed writer drives zero. A blocked reader does
not roll back a successful writer or retain its event, so the updater here must
remain unconditional and nonblocking. DWire is not a queue or an acknowledgement.
