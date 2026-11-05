# Benchmarks

The old builder/QueueGraph performance drivers have been retired. Current
source compiler evidence measures correctness of the serial source-owned route. Scale,
incremental compilation and parallel scheduling benchmarks belong to build reliability and
must invoke the public compile/link/emit driver against a pinned candidate.
Historical benchmark implementations remain in Git, outside the active route.

The source-unit workload measures shared definitions at 1/16/64 instances and
distinct leaves at 1/8/32 sources. Its generator and driver are owned here and
in `tools/`, respectively; see the [repository map](../docs/development/repository-layout.md). Generate
fixtures with `benchmarks/source-units/generate.py`, or run the full
public-driver measurement from the checkout:

```sh
python tools/measure_source_build.py --prefix <installed-prefix> --output-dir .pycircuit_out/measurement-measure
```

The output directory must be absent or empty. Prefix metadata must match the
checkout revision; dirty candidate bytes are separately bound in gate evidence.
The report records executed Ninja commands, source and model invalidation,
artifact sizes, wall times including startup, and sampled process-group RSS.
RSS sampling can miss short-lived peaks and counts shared pages in each process.
Commands launched in separate process groups are excluded, so this is not a
measurement of whole-build or compiler peak memory.
The report binds the measurement script, generator and sampler by SHA-256.

Every generated source owns one implementation unit. The fixture emits a module
library, with `.cpp` and `.v` source groups; it does not emit a System runner.
The measurement checks independent rebuild determinism, compiles the generated
C++ library and exercises body, provider-interface and toolchain invalidation.
It explicitly reports functional C++/RTL simulation as unmeasured. Use the
separate example and API tests for behavioral evidence.
Failed cases retain their diagnostics and measurements, and the remaining
cases still run. Any failed case makes the overall command return nonzero.

`measure_build_resources.py` still targets the retired System/C ABI fixture and
is not the current source-unit benchmark entry point.
