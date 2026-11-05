# Generated Rule artifact verification

This experiment compares actual pyCircuit RTL with a reference generated from
the exported Lean Rule model of the same compiled source unit. The original
source has three-bit state, capacity five, and increment-then-decrement order.
A renamed four-bit, capacity-nine source exercises the same generic route.
See [automatic validation](../VALIDATION.md) for semantics, bounds and schema.

## Correspondence

The native exporter produces closed typed Rule syntax. The proved symbolic
lowerer substitutes candidate register values, preserves Rule admission and
rollback, and threads the ordered schedule. Executing the generic Lean
serializer on those actual definitions produces typed next-state terms.
The verification-only Python encoder translates the terms into sized SV wires
and reference registers; there is no handwritten SV transition reference.

The existing pytest suite at `tests/system/test_formal_counter_artifact.py`
binds public ports using `ports.json` and loads the full RTL inventory from
`generated.json`. The test adapter only binds ports. Yosys lowers and flattens
the original emitted RTL, removes initialization attributes, and audits that
all state consists of the expected disjoint positive-edge DFF banks. Public
outputs must cover every model register; hidden state is rejected before SAT.

With reset held low, SAT assumes equal arbitrary register states in frame one
and proves equal next states and all public outputs in frame two. An all-ones
state witness checks that initialization did not restrict the relation.
The original case includes all eight encoded current states, even unreachable
counts six and seven. The renamed case likewise includes all sixteen states.

Three fault controls compile changed DUTs while keeping the original model,
formula and generated reference fixed. Parsed solver traces must show the
independently specified differences in the increment guard, arithmetic and
Rule order. Tool errors do not count as detected semantic faults.

The independent [checked_tb.sv](checked_tb.sv) runs normal checked RTL in
Verilator without `SYNTHESIS`. It checks reset, hold, increment, decrement,
simultaneous requests, and full/empty boundaries, requiring the success marker
and no physical-fault report. C++ is also emitted from the original final IR;
this is emission evidence, not native C++ execution evidence.

## Reproduce

Build and install this checkout's CompilerDev tools with LLVM/MLIR 22.1.8 and
build the [Lean project](../README.md). Install pytest, a recent Yosys with
sequential SAT/SystemVerilog support, and Verilator with timing support.
The recorded toolchain uses `yowasp-yosys==0.70.0.0.post1259` (Yosys 0.70,
revision `28ba3cb92`), Verilator 5.052 and pytest 9.2.0. Yosys 0.9 cannot parse
this emitted RTL; tests do not rewrite it to accommodate old parsers.

From the repository root:

```sh
export PYC_TOOLCHAIN_ROOT=/absolute/path/to/install
export PYCIRCUIT_SOURCE_COMPILER="$PYC_TOOLCHAIN_ROOT/bin/pycircuit-source-unit"
export PYCIRCUIT_LINKER="$PYC_TOOLCHAIN_ROOT/bin/pycircuit-link"
export PYCIRCUIT_EMITTER="$PYC_TOOLCHAIN_ROOT/bin/pycircuit-emit"
export PATH="$PYC_TOOLCHAIN_ROOT/bin:$PATH"
# Optional: export YOSYS=yowasp-yosys
python -m pytest tests/system/test_formal_counter_artifact.py -v \
  --basetemp=/absolute/path/to/disposable-artifact-output
```

Lean uses `PYC_LAKE` (default `lake`); `PYC_LEAN` may select an adapter invoking
the real Lean kernel with the project's import environment, as described in
[the exporter instructions](../EXPORT.md). Pytest clears `--basetemp`; choose
a dedicated disposable path without spaces for Verilator's make build. Ensure
its C++ compiler is on `PATH`. Retain raw artifacts and receipts together:
they record input/library/encoder/tool hashes and actual commands/results.

## Trust boundary

Lean proves symbolic lowering agrees with the Rule syntax interpreter. The
hardware result concerns each emitted RTL artifact's known-two-state
`SYNTHESIS` projection, one positive edge, reset inactive, state and public
outputs. Capture/type analysis, model extraction, Lean execution/serialization,
SV encoding, the state audit, and Yosys remain trusted. No solver certificate
or emitted RTL bytes are verified by the Lean kernel.

Reset, X/Z behavior, physical timing, events, resources and general compiler
correctness remain outside this result. Checked simulation provides concrete
reset/boundary evidence, not a universal proof of those behaviors. The retained
`CounterReference` Lean proofs connect the original model to Nat history safety;
the automatic RTL comparison no longer relies on a manually transcribed SV
version of that expression.
