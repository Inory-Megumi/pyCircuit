# Export a Rule model from typed source IR

This stage removes manual transcription of the counter's Rule AST. It consumes
the source implementation artifact published by the existing Python capture and
native compiler. It does not parse Python again, execute design functions, or
provide another production compilation route.

## Interface

The read-only `ac-export-rule-lean` pass belongs to ACIRTransforms and is exposed
through the existing CompilerDev `pycircuit-opt` tool:

```sh
pycircuit-opt guarded_counter.ac \
  --ac-export-rule-lean='top=checks.guarded_counter.GuardedCounter output=CounterModel.lean' \
  -o /dev/null
```

`top` selects the exact module symbol; `output` selects a Lean file. Both are
required. The pass validates and constructs the entire model before publishing
it atomically through a temporary file in the destination directory. Successful
export replaces the selected output. A rejected model leaves existing output
unchanged and creates no partial output. The input IR is not modified.
Export limits are 256 nested expression/command levels, 100,000 expanded expression
nodes across the model, and 8 MiB of generated text. Every recursive expansion
is charged, including repeated visits to shared SSA values; exceeding a limit
rejects export rather than truncating or substituting a model.

Output imports `RuleSemantics.Syntax` and defines deterministic data in namespace
`PycircuitExport`: `signature`, `initialState`, individual Rule definitions and
the ordered `rules` list. Register/input names and indices accompany the model.
`definitionName` and `registerKeys` bind the selected definition and verified
source owner occurrences. `outputExpressions : List (Output signature)` contains
typed packed observations over committed state and inputs. Names are quoted
data, never interpolated as Lean identifiers or used to choose semantics.

The output contains closed syntax data, not emitted counter-specific evaluators
or an exporter-authored claim of correctness. Independent Lean obligations use
the existing generic interpreter and reference theorems.

## Accepted profile

The selected module is flat, with concrete positive-width Bits inputs/registers,
known constant initial register values, and one shared clock/reset domain.
Compiler-generated domain ports are identified by verified domain metadata,
excluded from the data signature, and forbidden as data dependencies.

Source-body validation and the existing transaction/state analyses supply owner
identity, resolved widths, registration bindings and ordering. Autonomous source
Rules are `ac.transaction` roots. The normal verified transparent registration
entry resolves to its same-module `ac.method` guard/body. This special compiler
wrapper is supported; general Method calls, hierarchy and resources are not.
The pure combinational `ac.rule` operation is not treated as an atomic root.

All selected roots must form a total order through validated `ac.after`
predecessor identities; a single root is also allowed. Textual operation order
is never a schedule. Unordered/omitted parallel roots are rejected rather than
silently assigned sequential forwarding semantics.

The initial expression profile admits known Bits constants, module data inputs,
whole-register candidate reads, same-width add/sub, and verified identity
extract/resize. Predicate contexts additionally admit unsigned comparisons,
equality, one-bit conjunction/disjunction/negation, and typed conditional
selection. Bits(1) inputs remain Bits(1), with
predicate interpretation explicitly represented by equality to one. Comparison
results used as Bits payloads explicitly convert through `Expr.bit`. Constructed
Struct outputs concatenate fields in declared most-significant-first order.
Inputs and registers remain Bits; general record accesses and source branches
are outside this export profile. Unsupported operations are rejected even if a narrower use might
otherwise ignore them.

Bodies contain ordered whole-register writes on proven-true authored paths.
Every entry guard becomes a syntax Rule guard; every write becomes a typed
assignment. No source assertion is translated to `Syntax.require`: assertion
failure and ordinary ineligibility have different semantics. Branches, selected
writes, formal writes, checks, observations and other effects are outside this
first export profile.

## Snapshot and state-version discipline

The transaction analysis already distinguishes SSA values from successive owner
candidates. At each exported use, every referenced state-read version must
equal that owner's current version at that point in the Rule. Only then may it
be represented by `Expr.reg`. An unchanged other register may still be read.
The same discipline applies in guards. State-dependent module-body captures are
rejected even before a root-local write: those are committed-state snapshots,
not the forwarded state at a later root's entry. Initially only module data
inputs and known literals, optionally through verified identity wiring, may be
captured. Root-local current-state reads must use the analysis's explicit read
bindings; a raw module state result is not a substitute for such a binding.
Only the separate public-output traversal may read module state directly; those
expressions observe committed state, not a Rule's current candidate. This does
not relax the capture or stale-SSA restrictions inside Rules.

For example, `saved = count; count = count + 1; count = saved + 1` must not become
two dynamic register increments. A stale saved read is rejected until the
syntax gains an explicit snapshot representation. This rejection is conservative;
it does not claim that the original program is invalid pyCircuit.

## Verification and trust

Independent checks use the actual compile-to-source-unit route followed by this
native export and the Lean kernel. The original counter must agree with the
existing reference for all requests and all encoded states. A renamed four-bit,
capacity-nine variant checks that names, widths and constants are extracted.
A separately compiled reversed schedule must retain its different behavior.
One stale-snapshot case checks rejection without partial publication.

The [automatic artifact validation](VALIDATION.md) executes this exported model
through a proved symbolic lowerer and serializes its transition to generate a
reference for RTL from the same compiled unit. Checked RTL simulation remains
an independent observation check.
This export is a known-two-state, reset-inactive model of state transitions.
It does not prove reset, X/Z, fault behavior, physical timing or events.
The Python-to-typed-IR path and the native exporter remain trusted components:
Lean checks the exported program and its stated properties, not the correctness
of the extraction implementation. Unsupported source programs fail export;
they do not acquire a fallback model.

## Reproduce the independent checks

Build and install this checkout's CompilerDev tools with LLVM/MLIR 22.1.8, and
build the [Lean project](README.md) with its pinned toolchain. From the repository
root, select the installed native tools and invoke the existing pytest suite:

```sh
export PYC_TOOLCHAIN_ROOT=/absolute/path/to/install
export PYCIRCUIT_SOURCE_COMPILER="$PYC_TOOLCHAIN_ROOT/bin/pycircuit-source-unit"
export PYCIRCUIT_LINKER="$PYC_TOOLCHAIN_ROOT/bin/pycircuit-link"
export PYCIRCUIT_EMITTER="$PYC_TOOLCHAIN_ROOT/bin/pycircuit-emit"
export PATH="$PYC_TOOLCHAIN_ROOT/bin:$PATH"
python -m pytest tests/system/test_formal_rule_export.py -v \
  --basetemp=/absolute/path/to/disposable-export-output
```

`PYCIRCUIT_OPT` may select a specific optimizer executable; otherwise the test
uses the installation above. Lean checks use `PYC_LAKE` (default `lake`) and
`lake env lean` from the formal project. Alternatively, `PYC_LEAN` selects an
executable that supplies that same import environment, useful when the native
compiler and Lean run on opposite sides of WSL. Such an adapter must invoke the
real Lean kernel and propagate its exit status. The test does not simulate or
replace Lean. Pytest clears its `--basetemp` directory; use a dedicated directory.
