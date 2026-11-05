# Ordered counter

This example requires the local `codex/rule-order-20261105` candidate.
The official base does not accept its `schedule` declaration.

`schedule(increment, double)` orders the two Rules in each cycle. Starting from 3, the
registered counter follows 3, 8, 18, 38. The compiler forwards the successful
increment's value to `double`; both Rules remain separate atomic roots, and
storage updates once at the clock edge.

With the candidate installed:

```sh
pycircuit run examples/ordered_counter --cycles 4
pycircuit run examples/ordered_counter --target verilog --cycles 4
```

Use `--toolchain /path/to/install-scheduler` when selecting the installation.
The default low/high sampling logs are `3, 3, 8, 8, 18, 18, 38, 38` on both
generated C++ and RTL. The managed RTL runner selects the compatible simulator;
the local qualification uses Icarus.

For three writers, use `schedule(increment, double, third)`. Swap the first two
names to obtain 7 instead of 8 after the first edge, without editing either Rule.
Every pair of overlapping writers needs a defined relative order. Rules outside
the list retain current-state reads and existing disjointness/exclusivity checks.
The declaration follows the named Rules and precedes the Module's return.

This is ordered register forwarding. For independent same-cycle requests, see
the separate [DWire counter](../dwire_counter/README.md) in the newer local
DWire candidate. The earlier `install-scheduler` qualification remains separate.
