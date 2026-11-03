# Native operations and ordinary libraries

These examples require a compiler built from this native-actions branch. Put
that installation's `bin` directory on `PATH` and point `PYC_TOOLCHAIN_ROOT` to
the same installation before using the commands below.

`notification.py` is an ordinary Cell: an empty public action defines a call
identity, its independent update Rule observes active/args, and a query reads
committed state. `notification_system.py` drives two instances from two exclusive
caller Rules. A late false statement guard blocks both notifications; the
independent tick Rule continues. Rebinding a caller local does not change an
earlier argument snapshot.

`pipeline.py` uses the source library `python/pycircuit/lib/pipe.py`. Three
buffers and four independent Rules express producer, transformations
and consumer. Each stage pops an old token and pushes its transformed value to
the next stage in one atomic caller. Queue admission supplies backpressure and
full-slot replacement. The compiler has no Pipe-specific operation or name.

`Pipe(Width=8, Depth=1)` defaults to one slot. Set a positive static depth, such
as `Pipe(Width=16, Depth=4)`, to increase capacity while retaining the one-edge
minimum availability latency. The demo forwards `Pipeline(..., Depth=4)` to all
three buffers; omitting Depth preserves its original depth-one behavior.

Compile the notification example from the repository root:

```sh
pycircuit compile -c examples/native_actions/notification.py --source-root examples/native_actions --package-prefix native_demo -o build/native-demo/cell
pycircuit compile -c examples/native_actions/notification_system.py --source-root examples/native_actions --package-prefix native_demo -I build/native-demo/cell -o build/native-demo/system
pycircuit link build/native-demo/cell build/native-demo/system --top native_demo.notification_system.Exercise -o build/native-demo/system.ac
pycircuit emit build/native-demo/system.ac --target cpp -o build/native-demo/cpp
pycircuit emit build/native-demo/system.ac --target verilog -o build/native-demo/verilog
cmake -S build/native-demo/cpp -B build/native-demo/cpp-build -G Ninja -Dpycircuit_DIR="$PYC_TOOLCHAIN_ROOT/share/pycircuit/cmake"
cmake --build build/native-demo/cpp-build --target pycircuit_sim
build/native-demo/cpp-build/bin/pycircuit_sim --cycles 5 --workers 2
```

Build the generated Verilog project the same way with a distinct build directory
and run its simulator with `+cycles=5`. The regression additionally compiles the
unchanged emitted RTL with Verilator. Both targets consume the same verified
final artifact.

Compile Pipe as a separate explicit provider before compiling a pipeline consumer:

```sh
pycircuit compile -c python/pycircuit/lib/pipe.py --source-root python/pycircuit/lib --package-prefix pycircuit.lib -o build/native-demo/pipe
pycircuit compile -c examples/native_actions/pipeline.py --source-root examples/native_actions --package-prefix native_demo -I build/native-demo/pipe -o build/native-demo/pipeline
```

The independent system regressions in `tests/system/test_native_actions.py`
qualify notification snapshots, late admission, the stalled three-buffer pipeline
at depths 1, 3 and 4,
and same-root replacement at nondefault Pipe widths. Their oracles use literal
expected states or old-state FIFO equations. No Table, LRU, arbitrary payload
type or automatic scheduling qualification follows from these examples.

See `docs/extensions/native-actions.md` for query/action/private contracts,
`ac.fired(rule)`, the bounded root-final forwarding profile and its limits.

## Reading hardware RTL

The default Verilog output is the managed simulation view. Its encoded port
names, transaction captures, check protocol and storage wrappers preserve the
simulation ABI. Use the synthesis view when inspecting reset-based hardware:

```sh
pycircuit emit build/native-demo/module.ac --target verilog --rtl-mode synthesis -o build/native-demo/hardware
```

This requires a Module root; a System is a closed simulation harness. For the
parameterized pipeline, the qualified hardware path instantiates the unchanged
`Pipeline` in an ordinary Module with a concrete `Depth`, then links that Module.
The native synthesis regression includes depths 1 and 3. Direct open-parameter
FIFO roots remain subject to the existing static-demand admission limits.

The renderer follows actual Queue-owner paths for private transport interfaces,
including nested ordinary objects. Exact private Bits constant returns are
written as equally sized literals at their consumers; declared public outputs
and stateful instances remain. Source Rule scopes survive transaction routing,
so the pipeline computations retain their produce/double/transform/consume
sections. Shared operators keep their original producer. The common IR, native
admission, FIFO kernel and managed port ABI are not changed by this view.
