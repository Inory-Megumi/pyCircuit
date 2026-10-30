# Readable physical RTL

`--rtl-mode synthesis` is a separate reset-based export for an open Module root.
It emits no startup `initial`, private check ports, check blocks, fault history
or runtime diagnostic tasks. Declared values remain synchronous reset values.
Only the selected root hierarchy is emitted. Current storage support is
authenticated typed DFF/DFFE instances and storage Collections. Nominal record
and enum storage use the existing packed layout; Collection lane order and
per-lane update endpoints remain unchanged. Other primitive storage and Queue
are rejected before publication rather than exporting simulation models.
System roots remain simulation harnesses and are not synthesis exports.

Synthesis comparison starts after a successful reset with legal binary inputs.
This export does not preserve startup observations before reset or illegal-input
fault history. It changes neither the verified IR nor the source/C++/managed
contracts. `--rtl-mode physical` retains its original instrumented startup and
fault behavior. Source assertions and X/Z diagnostics belong in that validation
export, not the reset-based hardware output. This does not claim all-design
synthesizability or measured synthesis/PPA; use the scoped execution evidence.

Physical emission may present verified scalar DFF/DFFE state as named
`always_ff` blocks. This is an export representation of the same final IR;
source authoring and admission are unchanged. Source binding provenance is
retained through import, source control normalization, transaction expansion
and record forwarding as non-semantic Location metadata. It adds no SSA uses
or semantic operation attributes. Original-source authentication compares the
original Location beneath this presentation wrapper, retaining exact opcode,
attributes, properties, result types, operands and source identity checks.

The presentation uses the authenticated commit endpoint, logical payload type
and proven static initializer. Physical Collections retain the instrumented
primitive-instance path; synthesis Collections use lane-local always_ff blocks.
Physical
clock/reset mapping, root fault history, strict/if_one reset interpretation,
unknown-control errors, NBA updates and whole-root zero commit are retained.
Physical state keeps its source spelling when available; port and parameter
collisions receive a deterministic suffix. Compiler-generated domain inputs
export as clk/rst, while authored ports keep their names. Ports metadata, child
connections and root wrappers use the same mapping. Redundant per-state write,
commit and domain aliases are omitted. Physical private check ports have
`__checks_*` names; managed ports retain their existing ABI.

Short expressions may inline only with one effective consumer through Rule
and identity-slice forwarding. Shared arithmetic keeps one SSA wire; division
and remainder keep their existing specialized emission. Every inlined result
keeps its width boundary and unsigned Bits interpretation. Unnamed, single-use
field and slice references may print directly because they already have their
declared self-determined type and width. Named or shared projections retain a
wire. Aggregate constructors remain typed boundaries. Unsupported consumers
retain named values. No common-IR optimization or hardware hierarchy is replaced.

A DFFE candidate `condition ? new : same_old_Q` may omit its hold arm only
when the actual write enable structurally implies known-one `condition`.
Otherwise it retains its original candidate. Physical controls may remove
Boolean normalization shells only while preserving knownness and known-one
truth; this does not permit dropping unknown-control faults.

One-input Boolean functions are summarized over 0, 1, X and Z, with bounded
work and conservative fallback. Only exact known-bit conditions become
procedural branches; unknown-capable selects keep their merge semantics.
Branch facts may remove implied inner selects without duplicating shared
expressions. Assignment context may supply the final exact width, while
intermediate truncation boundaries remain explicit. Equal-width unsigned
add/sub/mul/and/or/xor consumers may reuse an inline expression body without
its sizing shell. Different-width contexts, shifts, signed conversions and
unsupported consumers retain the original shell. This decision is made from
typed SSA values, not by parsing emitted RTL strings.

Local source bindings name surviving wires in all RTL modes. Shared values
retain aliases without creating duplicate arithmetic. The generated
rtl-names.json records each emitted binding's scope, source location, optimized
value ordinal, type and actual RTL expression. Dead values are not resurrected
to preserve a name. Anonymous generated values receive operation-based names.
Fresh derived operations inherit only the original diagnostic position, with
binding wrappers removed recursively. Clones retain their same computation's
names; actual SSA replacement, forwarding and constant pooling explicitly
transfer value bindings. Reusing a branch position cannot name an unrelated
record or mask result after a scalar local from that branch.
Nominal types keep unambiguous source names; enum members are scoped localparam
symbols over the original logic-vector typedef, preserving arbitrary codes and
X/Z representation. Naming collisions are resolved deterministically.
ASCII source value bindings rejected by the shared C++ identifier policy use
standard escaped SV identifiers instead of hexadecimal display names. The
required terminating space is retained at every reference. Collision allocation
uses the logical name before escaping, so escaped `\\packed_1` with its terminating
space and ordinary `packed_1` cannot
declare two signals with the same identity. C++ naming and source spelling do
not change; this local-value rule does not rename public ports or types.

A selected, genuinely combinational Module closure can export without a clock
domain or check lifecycle. The empty owner inventory is accepted only after
checking the reachable closure for sampled effects and primitive endpoints.
An empty managed inventory is not evidence that state or domains are absent.
Synthesis requests the owning verifier's complete bounded occurrence inventory,
including unchecked primitive-only closures. Explicit domains follow actual
root bits and ordered record fields through real occurrence arguments. Derived
clocks, reused clock/reset pins and clock use as data or exported records remain
rejected. The instrumented physical profile retains its single-domain DFF/DFFE
limit; synthesis also supports the existing FIFO and synchronous Memory kernels.
Authenticated value/resource availability remains in the Rule fire and proposals;
physical availability controls add reached-path knownness faults to the existing
whole-root permit. Synthesis retains the reset/known-control/source-assertion
preconditions of the reset-based hardware profile; it does not establish four-state
fault equivalence to managed execution.

The installed FIFO/Memory source templates provide an internal
PYCIRCUIT_PLAIN_RTL branch for hardware-only ports and physical-edge commits.
Their ordinary ABI, arithmetic, storage, policy, latency and response kernels are
unchanged. Publication selects the SYNTHESIS and plain export branches from those
source inputs; native-generated DUT RTL is never reparsed or patched. Unknown
macro conditions remain for the SV preprocessor. runtime_sources.json binds each
input/profile/output hash. Independent preprocessor comparisons qualify both the
default interfaces and the selected export. No function simulation or synthesis
result follows from that text comparison.

Private transaction ports receive names from authenticated storage dependencies,
and module names use source spelling when globally unambiguous. Parameters,
source ports, qualified fallback names and primitive module names remain reserved.
Private identity returns through Rule captures may be omitted by connecting
callers directly to the corresponding input. Source outputs and validity outputs
are retained; definitions used by Collections keep their packed interface.

Diagnostics are collected in a `__checks` block. Its automatic `allow_update`
function evaluates the current clock at the sampling edge, preserving failure
gating without a new clock-dependent continuous-wire scheduling race. Declared
startup initialization and synchronous reset remain separate operations with
their original values; neither is inferred from the spelling of a demo name.

Closed Table geometry prints its checked cardinality and packed bit width
directly. Constant lane selections retain the original first-element-at-MSB
layout. A dynamic index is compared in max(index width, bits needed for the
extent), so narrow index types cannot truncate a non-power-of-two extent.
Physical and synthesis exports display closed Table layers as ascending packed
array dimensions over the original element type. Element zero stays at the
MSB, including nested Tables, primitive connections and per-lane initialization.
Managed and symbolic layouts retain the original packed-vector representation.
Per-field choices may display as one aggregate ternary only when every declared
field uses the same selector and the same two typed records. Table reconstruction
additionally requires the same two Tables and exact lane ordinals. Named/shared
selectors are retained; differing conditions and field layouts use the original
form. The four-state conditional still merges each payload bit.
This recursive IR layout does not expand source admission: source Tables still
require a Bits/Enum/Struct element, and direct Table-of-Table annotations remain
rejected. Long assignments wrap only at existing whitespace outside strings;
no token or arithmetic node changes. Equal-width one-bit consumers may omit
redundant inner sizing shells, and logical shifts may reuse an equal-width left
operand body while retaining the shift result's original sizing boundary.
Only known, representable index constants are folded; potentially wrapping
integer literals retain the existing sized comparison. Out-of-range constant
reads keep false availability and X payload. Uniform Tables may print as packed
replication with the same element type, width and cardinality.

Reserved anonymous call-site IDs receive a display name derived from the callee
Module. This changes no occurrence, source identity or partition. Authored
instance names retain the existing collision handling.

Static name/layout checks live in `tests/system/test_readable_value_names.py`
and `tests/system/test_readable_aggregate_layout.py`
and the nominal-storage case in `test_synthesis_rtl_export.py`. Name metadata,
CSE-equivalence/hash neutrality and original Location identity have native
checks in SourceValueSemanticsTest.cpp. Functional checks remain in
`tests/system/test_physical_rtl_readability.py` and
the existing physical export/projection suites. The API and examples gates
remain separate required candidate checks. Text size is a readability measure,
not a claim about synthesized area, timing or equivalence.

Experimental Method ownership uses non-semantic Location provenance retained
only after the owning transaction correspondence verifier accepts its detached
candidate. Canonical receiver occurrences identify the target; display names
never select an owner. CSE replacements retain all owners without adding SSA
uses or semantic attributes. Shared optimized nodes remain at their original
common ancestor. The optimized common IR and C++ backend are not repartitioned.

The RTL construction plan cuts regionless pure nodes into occurrence-relative
variants along the canonical receiver path. It checks unique placement, exact operands,
original output/state aliases, original candidate D/E values and all live cut
edges. Compiler-generated routing adapters may follow their sole receiver;
shared final enables and resource-wide grants stay in the caller. Removing a
private identity route reconnects the same SSA value, without a new state,
cycle, arbitration decision or autonomous commit rule. Declared source inputs
remain inputs. Compiler-private root defaults bind the exact literals formerly
connected by the root wrapper. Availability ports use their source result names.

The generated rtl-names.json records module-local values, typed operands,
source scopes, allocations, actual expressions and partition decisions. Null
expressions denote values without a separate emitted expression. Qualified RTL
names and nominal/member compounds use the RTL namespace independently of C++
mangling. All these are presentation decisions over a verified hardware graph.

Indivisible nested regions retain their original scope. Source admission of
generic Methods and new parameter kinds is unchanged; arbitrary region
ownership recovery is not claimed. Current static catalog evidence must report its actual
coverage and any retained decisions. Structural cut validation and unchanged
optimized IR do not constitute RTL formal equivalence or a PPA result.

Physical and synthesis rendering forwards unnamed exact-width Enum carrier
conversions to the memoized original producer. Enum widths come from the
verified nominal declaration. Only the data result of enum.from_bits is an
alias; its separate membership result retains ordinary four-state equality/OR
over all original codes. Invalid and X/Z carriers remain ordinary data. Member
constants render with their declared symbolic names, and authored bindings keep
typed named wires. This does not recode an Enum or change the common IR.

Effective use counting follows both results of a decode and all encoding views,
so shared arithmetic remains one computation. Typed width casts still bound a
narrow calculation before widening. Unknown selectors retain the existing ?:;
they are not changed to procedural if/case. Enum storage exposes the original
D and E with named next/enable wire aliases, preserving its exact reset, hold
condition and clock. Comparison labels derive from actual same-Enum carriers
and members, with the normal identifier/collision allocator. There is no FSM
name, member-code, member-count or fixed-width special case.

The static Enum conformance covers sparse and derived encodings, 1/72-bit
carriers, state, nominal ports, Struct/Table use, explicit decode/membership,
round trips, ignored membership and shared/narrow arithmetic. Record graph/C++
text preservation and static RTL checks separately from simulation/formal/PPA.

Unknown-condition select trees now have a typed presentation plan. Same-width
single-consumer arms can share one multiline ?: expression, independent of the
total string length. Authored names, effective multi-use values, actual port
boundaries and width changes end expansion. Shared roots remain one named wire.
The existing known-condition structured printer retains its original path,
including known-condition children inside an otherwise unknown-condition tree.
Already named or explicitly retained producers are opaque layout boundaries.

Each expanded arm has the same verified unsigned Bits width. Leaf arithmetic
and resize expressions retain their own bounds; an explicit outer width cast
seals the complete expression against a later wider context. Enum conversion
data can forward only under the same exact-width rules above. Membership, X/Z,
priority, default arms, D/E and clock/reset behavior are not reconstructed.

One plan contains at most 32 select nodes. Larger trees retain memoized wire
boundaries rather than expanding an unbounded expression. The 96-character
limit still chooses compact leaf presentation and ordinary non-select inlining;
it no longer forces a private single-use select subtree into an opcode wire.
No source-check budget or common-IR pass changes. Static conformance covers
chains, both arms, shared choices, narrow/widened arithmetic and a 40-node cut.

Closed typed Tables now have a row-construction plan over the unchanged SSA.
Private, regionless, memory-effect-free maps and exact elementwise aggregate
choices can share one generate block, including the original collection D/E
endpoint in synthesis exports. Shape, element type and ordinal must match.
Bits, exact-width Enum carriers, records and nested records use the same rule.
The condition and both candidates are the original values; unknown conditions
remain ?:, and partial field writes still use the existing merge renderer.

Exact splats and all-identical-SSA table constructors supply one scalar to a
lane. Scalar captures are rendered once outside the loop. Uniform clock/reset
pins use that same authenticated scalar; other pins keep their original packed
lane indexing. Initializers retain each original lane value and reset behavior.
Physical exports with checks retain their original primitive/check interface.

Every candidate cut follows Rule forwarding and checks all live outside uses.
Shared maps and post-write tables used by dynamic reads remain one materialized
vector. Authored bindings and ownership-opaque values are boundaries. Only
unobservable pure map outputs and merge masks can lose their separate wires;
required data, guards, membership, checks and side effects stay live. No Boolean
algebra, scheduling, arbitration, width conversion or common-IR optimization is
changed. A 256-node presentation budget falls back at existing vector boundaries
and never changes the source-check budget. Whole-vector uniform choices may use
packed replication; lane operands always use typed element projection instead.

Generated rtl-names.json values include rtl_scope for expressions local to a
generate block. Source names, module-local SSA IDs and original operands remain
the navigation authority. Static cases cover routed Bits/Enum/record storage,
partial writes, nested payloads, sequential write/read dependencies, private
and shared map chains, scalar captures, nonuniform initializers, wide carriers,
and unchanged source admission rejections. These are compile/emit/static checks,
not functional simulation, RTL equivalence or PPA evidence.

Source operation names now accompany anonymous generated roles in non-semantic
per-result Location metadata, retained only after transaction correspondence
verification. Exact bound values, branch conditions, selected-write lane
comparisons/merges, method exit versions and caller result bindings supply the
roles. No role is inferred from a demo name or a condition's Boolean formula.
The actual storage enable endpoint supplies its display hint independently of
address hit. Names never create uses or authored-binding/inlining boundaries.

The renderer prefers actual caller result bindings and qualifies conflicting
local names by their original method scope. Unnamed values may use condition,
state_after_method, method_state_hit/lane_value/value roles. Multiple merged
origins remain recorded, and shared values are not attributed exclusively to
one method. Existing symbolic Enum comparison names take precedence. Identifier
escaping and collisions use the normal allocator; scalar widths and the
original four-state expressions are unchanged.

Source-call comments list lexical calls and their actual updated state names;
they do not claim unconditional execution or independent method commits. A
32-call comment limit refers readers to rtl-names.json for the complete index.
That index records all per-value source_roles, canonical receiver paths and
before/after version edges. Role metadata is stripped only from diagnostic
identity and ignored by operation equivalence/hash; CSE replacements retain
every origin at the replacement result. Dedicated native tests check these
properties, while static source cases cover renamed methods, ordered table
updates, common conditions and shared caller aliases.

Synthesis rendering now buffers typed declarations and concurrent source
sections separately in each lexical scope. Constants, state registers and
signals precede executable members. Net declaration continuous initializers
print as the same wire plus an explicit assign; variable initializers are not
converted. Module-level signals stay in the module; generate-local signals
stay in their original generate block and precede that block's logic.

Source method sections follow recorded lexical call order. Source-rule result
wiring, actual atomic enable endpoints, individual instance/state updates and
output connections have separate sections. Shared multi-method computation is
emitted once in module wiring. A caller/result alias may share its producer's
method section; this is presentation, not physical ownership or scheduling.
An entirely inlined method does not acquire a wire or empty section merely to
display a heading. This section-layout pass preserves original scopes, names,
expression text, processes and procedural statement order. No module/always block is split
or merged, and no clock cycle is introduced. Managed and instrumented physical
layout keeps its established path.

The emission buffers receive declarations, source groups and explicit scope
boundaries directly from the typed renderer. They never parse or rearrange
generated Verilog text. Static slang syntax comparison separately allows only
trivia removal, concurrent member ordering and wire continuous-initializer
syntax. It keeps procedural ordering, declaration types, expressions, generate
scopes, names and ports exact, and checks declaration-first placement in each
changed synthesis scope. This evidence is distinct from formal equivalence.

Value spelling and materialization are separate decisions. Authored bindings
and symbolic Enum comparisons remain preferred. Exact storage enables, typed
result-slot contracts, verified source roles, and unique typed consumer paths
supply generated names. TableGet.in_range, EnumFromBits.member, TableChoose's
index/valid slots, and ValueMerge.en have distinct meanings. A membership or
range predicate is never named as its payload or as an atomic commit.

Anonymous Struct/Table constructors query actual aggregate fields, broadcast
elements, Rule/Map forwarding, output ports and storage D pins. Conflicting
uses, unsupported paths or a bounded display walk produce a neutral nominal
type name. Shared data roles remain shared_write_value/shared_lane_value;
only shared condition roles use shared_condition. No method/type spelling or
constant encoding selects a hardware policy. These queries do not call net(),
attach source bindings, add SSA uses, force a wire, or change CSE/DCE identity.

The allocator reserves all authored aliases and storage identities before
traversal. Generated names, collision suffixes, scratch arrays, genvars and
block labels cannot consume a later authored name. Escaped identifiers share
their logical namespace with simple identifiers. TableChoose/Fold scratch
arrays use the same allocator as ordinary generated signals.
Compound instance and purpose names start from the logical identifier stem,
before reapplying SV escaping; an anonymous call to a keyword-named module does
not turn an already escaped module token into an encoded compound name.

Private scalar expansion uses at most 12 typed display units, counting an
operation, literal or materialized input as one unit and recursively charging
already inlined inputs. Original sharing/authored/width/port and explicit
retention boundaries still apply. Identifier length controls line wrapping
only. This replaces the old 96-character expansion test, which inadvertently
allowed a rename to move a wire boundary. This is a presentation change, not
a common-IR optimization: every original operator, shared producer, D/E value,
width seal, clock/reset and procedural update retains its original identity.
Some private temporary wire positions differ from older presentation output;
those differences must be reported instead of claimed to be rename-only.

Unanchored scalar helpers have a module-wide read-only purpose plan, seeded by
actual output ports, instance input pins and existing source/slot/endpoint
anchors. The walk stops at a nearer anchor or a storage/region boundary. Each
original value accepts at most two distinct contexts, so processing is bounded
by the actual graph and shared contexts stay neutral. Labels use consumer
context plus value/predicate and the exact optimized_value ID in rtl-names.json;
multiple contexts use shared_value/shared_predicate. Missing context stays a
neutral value/predicate ID. It is never invented business behavior. Constructor
and auxiliary-slot rules retain their more specific precedence.

Purpose propagation follows result-slot dependencies: a Table range flag reads
the index, a choice reads its match mask, and merge.en reads its guards. It does
not attribute payload computations to those predicates. Record field projections
are conservative cuts instead of treating every record field as an input to a
single projected field. The verifier-witness operand of ValueRequire is omitted
just as in runtime expression emission. New or unresolved regions retain neutral
names instead of speculative cross-region propagation.

The value-order table is shared with source navigation. Symbolic Enum name
queries use source anchors rather than recursively calling net(). Consequently
name planning cannot emit an operand, and readable identifiers no longer use an
opcode/print-order counter as their final fallback. The managed harness keeps
its existing spelling and lifecycle. The keyword-name regression retains the
same source and all seven bitwise operators, checking generated identifier
legality without requiring an obsolete opcode-number spelling.

One-bit control presentation additionally has a memoized four-state view.
For each supported pure operation, it enumerates at most 64 operand tuples
over conservative domains, respecting repeated occurrences of the same SSA
input. Only a constant result or an exact operand projection can forward a
generated value. In particular `z & 1` remains X, while `select(c, b, b)` keeps
b including Z. Authored identities, opaque ownership and unsupported operations
remain boundaries. No common IR, pass, resource policy or original use is
rewritten; surviving shared producers retain net() memoization. The navigation
map records domains, operand IDs and projections for independent finite checks.

Presentation-use counts start from actual module outputs, instance pins,
ownership exports and retained physical checks, after proven forwarding.
Verifier witnesses do not become runtime consumers. Large known Boolean
conjunctions may be written as fully initialized always_comb requirement blocks.
Only private conjunction/conditional-requirement nodes are opened; shared
nontrivial predicates remain wires. Adjacent identical known guard paths share
one if block. Path facts can remove a private selected payload under a proven
branch; its case-equality readiness test is retained. Unknown selectors keep
their ternaries. This is not a rename-only transformation or an RTL formal
equivalence claim: Boolean operator counts and private wires can change.

Synthesis can collect 3--64 repeated concrete Module occurrences into typed
interface arrays and a generate loop. Group membership requires the identical
callee, parameter/type-argument attributes, rendered bindings, and input/output
types. It does not depend on names or examples. Every lane remains a distinct
original occurrence and keeps its input expressions; equal shared inputs are
connected directly. Original allocation identities and generated hierarchy
paths remain in rtl-names.json. Authored result bindings, ownership partitions,
open types and incompatible specializations retain their established paths.
No arbitration, temporal multiplexing or shared state is introduced.

Synthesis projects compiler-private child-module outputs through existing
source result records when their exact canonical SSA value is a record field.
It also removes private outputs with no effective consumer across any ordinary
occurrence. Public source outputs, availability companions, selected roots,
collections retain their established boundaries. Ownership variants apply the
same exact source-field projection without changing public outputs.
Projection follows actual StructCreate/StructGet paths; it creates no new read,
arithmetic or duplicate producer. The common IR and C++ ABI are unchanged.
Private queue inputs are described through authenticated queue-wiring bindings
and actual resource occurrences (for example requests_push_data), independently
of any example or method spelling. Port and value navigation records retain
original slots, canonical SSA values, field schemas and projection paths.

Conditional requirements can use facts from several strict one-bit tests.
The display analysis composes conservative four-state domains under these facts;
only a proven constant selector opens a private selection. Strict comparisons
on arbitrary computed one-bit values are facts about that value, not guessed
facts about its inputs. Shared requirements remain a single net, and their
case-equality ready/capacity checks remain present. Fact certificates record
assumptions, facts and selector domains for independent finite checks.

Generated local identifiers use ordinary ASCII tokens, normalize separators
and underscore runs, and give keyword-derived stems a safe suffix through the
existing collision allocator. Authored names and their source mappings retain
their separate precedence, including standard escapes where required. Pure
control queries preserve resource/instance fields, typed comparison subjects,
guard relationships and shared consumer contexts instead of opcode counters.

Receiver variants are keyed by parent occurrence scope and actual allocation.
Intermediate variants relay exact original values rather than re-evaluating
leaf arithmetic. Repeated definitions retain independent storage; original
shared producers stay at their common ancestor. Lowering-created routing
adapters follow local storage endpoints only when their original use permits
one placement. Final D/E values and all live cut edges are checked separately.
Private state-input names follow authenticated owner paths to the declaration;
private identity returns can forward through several actual child instances.

Open value and type parameters retain their original owner namespace. A scope
variant transports ancestor parameter bindings explicitly, so two definitions
using the same W or T name cannot capture each other's type or width. Generic
bodies remain symbolic; parameter defaults do not establish closed facts. The
common verifier still owns parameter admission and checks. This is not new
frontend generic-state or generic-Method support.

Under an original DFFE write enable, consecutive exact-old-Q hold adapters may
be peeled only while that enable structurally implies every original guard.
Intermediate widths, unknown controls, unrelated guards and partial-field
updates retain their original expression boundaries. Shared data is memoized.

Navigation records original value/operand IDs separately from rendering aliases,
along with each occurrence's captures, exports, replaced pins, static bindings
and operator placement. An independent hierarchy-wiring checker reconstructs
original wire equivalence classes without trusting planned cut aliases. The
emitter fingerprints verified common IR before and after presentation and rejects
a mutation. These checks are structural evidence, not RTL formal proof.

## Current compose and Method lowering

Presentation metadata is retained on the current compose readiness, candidate
and Method parameter implementation. It does not replace those implementations
or change their admission, budgets, source authentication or final commit.
Fresh compact branch merges receive the original source position without the
branch's result-name metadata; exact result bindings are then transferred to
their corresponding values. A Boolean binding cannot name an aggregate helper.

A verified whole-value merge with one empty field path and one guard can use
the same typed choice presentation as a decomposed branch. Its independent
enable result must be unused; partial paths and live auxiliary results retain
the ordinary renderer. Existing use and sharing checks still bound lane
projection. Both TableRead and TableGet retain their original range expression
and unknown payload branch; only TableGet has a membership result to declare.

Managed ports, instance identifiers and observation paths retain the existing
native-compatible naming ABI. Readable physical/synthesis names do not change
that protocol. Managed source groups also retain every final source definition,
including logical Method entry definitions outside the selected closure.
Their original root-default ports remain present, with constants supplied by
the existing wrapper rather than substituted into managed module bodies.
Provenance visits original source operations in source order;
pointer-keyed IRMapping iteration must not determine nested Location order.
Independent compilations retain byte-identical final artifacts, including
display metadata, for generated System comparisons across backends.
