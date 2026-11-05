# Generated counter artifact verification

This experiment connects one actual pyCircuit program to the Rule models in
[the Lean project](../README.md). The source has three-bit state, capacity five,
and a fixed increment-then-decrement schedule. Verification uses the public
compile/link/emit route and the physical RTL emitted from the saved final IR.
The same final IR also emits C++; C++ emission is not native execution evidence.

## Correspondence

For known request bits and current state `q`, the independent reference computes:

```text
q1 = if increment && q < 5 then q + 1 else q
q2 = if decrement && q1 > 0 then q1 - 1 else q1
```

[counter_reference.sv](counter_reference.sv) expresses this transition in RTL.
[CounterReference.lean](../lean/RuleSemantics/CounterReference.lean) separately
expresses it using `BitVec 3`. Lean proves that its state agrees with the ordered
Rule model, and then with the Nat model, for every finite request history.
The initial state need not be bounded for correspondence. Safety additionally
requires an initial count at most five; every history prefix then stays bounded.

The artifact tests live in the existing pytest suite at
`tests/system/test_formal_counter_artifact.py`. They bind the actual emitted
public ports using `ports.json` and load the full RTL inventory from
`generated.json`. The test adapter only renames ports; it supplies no DUT logic.

The Yosys miter compares the public DUT and reference count outputs. After
process lowering and flattening, all initialization attributes are removed
before optimization. The normalized design is checked for exactly two
three-bit state banks, whose Q bits are the compared public outputs and whose
positive-edge clocks are the shared clock. This checks that the assumed current
state relation is the relation on all stored state.

With reset held low, the solver assumes equal arbitrary counts in frame one
and proves equality in frame two. The two frames represent one state update.
This covers all eight encoded current states and all four request combinations,
including unreachable counts six and seven. A separate satisfying witness from
count seven checks that initialization did not silently restrict the proof.

A negative control recompiles the Python source with only the schedule reversed.
From zero with both requests asserted, the expected next states are one for the
mutant and zero for the reference. The test requires this concrete semantic
counterexample, rather than accepting a tool failure as a detected mismatch.

The independent [checked_tb.sv](checked_tb.sv) runs normal checked RTL in
Verilator without defining `SYNTHESIS`. It checks post-edge values for reset,
hold, increment, decrement, simultaneous requests, and full/empty boundaries.
It requires the success marker and no physical-fault report.

## Reproduce

Build and install the current checkout using its CompilerDev profile and exact
LLVM/MLIR 22.1.8 dependency, following the repository build documentation. Install
pytest, a current Yosys with sequential SAT and SystemVerilog support, and
Verilator with timing support. Yosys 0.9 cannot parse this emitted RTL; the
test intentionally does not rewrite it. A recent `yowasp-yosys` package is an
alternative to a native Yosys installation; select it with `YOSYS=yowasp-yosys`.
The initial passing run used `yowasp-yosys==0.70.0.0.post1259` (Yosys 0.70,
revision `28ba3cb92`), Verilator 5.052 and pytest 9.2.0. Receipts record the
compiler executables, toolchain metadata, WASM binary and input/artifact hashes.
Then, from the repository root, using absolute paths for the installation and
a temporary output directory:

```sh
export PYC_TOOLCHAIN_ROOT=/absolute/path/to/install
export PYCIRCUIT_SOURCE_COMPILER="$PYC_TOOLCHAIN_ROOT/bin/pycircuit-source-unit"
export PYCIRCUIT_LINKER="$PYC_TOOLCHAIN_ROOT/bin/pycircuit-link"
export PYCIRCUIT_EMITTER="$PYC_TOOLCHAIN_ROOT/bin/pycircuit-emit"
export PATH="$PYC_TOOLCHAIN_ROOT/bin:$PATH"
# When using the Python-distributed WASM build:
# export YOSYS=yowasp-yosys
python -m pytest tests/system/test_formal_counter_artifact.py -v \
  --basetemp=/absolute/path/to/fresh-artifact-output
```

Pytest clears its chosen `--basetemp` directory; select a dedicated disposable
directory. Use a path without spaces for Verilator's generated make build.
Ensure the C++ compiler used by that Verilator installation is on `PATH`.
The Lean checks are reproduced separately with the commands in
[the proof README](../README.md). Keep generated artifacts and test logs together
with their recorded content hashes when reporting results.

## Trust boundary

The hardware proof concerns the generated RTL's `SYNTHESIS` known-two-state
projection, one positive clock edge, reset deasserted, and state outputs only.
It does not certify X/Z behavior, physical timing, reset semantics, event traces,
resource rollback, arbitrary sources, or the compiler as a whole. The checked
simulation adds concrete reset and boundary observations; it is not a universal
proof of those excluded behaviors.

The end-to-end argument still trusts Yosys parsing, process lowering and SAT,
the test adapter and state audit, and the manually reviewed correspondence
between the SV and Lean reference expressions. No SAT proof certificate is
imported into Lean. Lean checks its own model theorems with its kernel.
Combining those model theorems with the one-step artifact result gives a
state-history correspondence argument under the stated hardware assumptions;
it is not a single kernel-checked theorem about emitted RTL.
