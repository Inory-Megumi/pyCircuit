# Verified Rule source library

These ordinary pyCircuit Modules are the first concrete source library of the
[Rule contract exploration](../LIBRARY.md). Compile `basic.py` as one source
unit and import its published interface from a consumer; `consumer.py` is an
independently compiled generated System exercising the components together.
They use the production capture/compile/link/emit route and introduce no API.

| Component | Inputs | Result and behavior |
| --- | --- | --- |
| `Register8` | `write:u1, data:u8` | Eight-bit stored value; writes when requested and otherwise holds. |
| `Counter3` | `increment:u1, decrement:u1` | Three-bit count bounded by five from zero; increment precedes decrement. |
| `Slot8` | `put:u1, data:u8, take:u1` | One-entry FIFO with the protocol below. |
| `Fifo2x8` | `put:u1, data:u8, take:u1` | Two-entry FIFO with the same protocol. |

Buffers return a named `BufferOutput` with `ready`, `valid` and eight-bit `data`.
Outputs observe current committed state. A transfer consumes the old head when
`take && valid`; an input transfers when `put && ready`. A full buffer can pop
and replace in one edge. An empty buffer cannot consume its newly arriving
token in that edge. Data is zero while invalid and held while a valid head is
stalled. The two-entry FIFO preserves insertion order; it is a shift-register
implementation with fixed width and depth, not a general parameterized FIFO.

The counter is ordered saturation: both requests at count five produce four,
because increment rejects before decrement runs; both requests at zero produce
zero. Each Rule owns its atomic boundary. All state initializes to zero.

Lean proves Rule contracts and independence conditions, arbitrary-payload queue
refinement across finite histories, observations and capacity preservation.
Actual native-exported ASTs are kernel-checked against these models. The generic
RTL comparison observes internal storage via compiler owner metadata and checks
state and public outputs. Queue-list refinement requires occupancy at most the
declared capacity; RTL transition checking includes spare encoded count values.

Run the reproducible pipeline from the repository root after configuring the
CompilerDev test installation and required tools:

```sh
bash tools/run_api_tests.sh --tier gate --formal
```

The [testing guide](../../docs/development/testing-and-gates.md#optional-rule-formal-validation)
describes environment variables and evidence. The source-library tests also
rebuild the consumer and compare generated C++ (workers one/two) and RTL traces
against an independent list-based protocol oracle.

These components have their own external protocol. Existing native `ac.queue`
storage and Method admission are outside their proof. Hardware equivalence is
known-two-state and reset inactive; universal reset, X/Z, physical timing and
whole-compiler correctness remain outside the result.
