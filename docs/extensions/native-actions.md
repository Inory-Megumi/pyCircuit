# Native operation interfaces

Libraries use ordinary Module, Method and Rule source through the native
compile/link/emit flow. Pipe, counters, FSM and selection policy have no special
compiler names or runtime scheduler. Internal Rules remain independent roots.

## Method contracts

Bare `@ac.method` keeps native ordered candidate semantics: repeated calls and
later assignments in one root are legal. A callee reads its caller's current
candidate; another root starts from committed state.

`@ac.method(kind="action")` opts into one observable operation identity. Empty
notification bodies are legal. Each concrete instance permits at most one
successful invocation per cycle, proved from actual call paths and complete
caller admission. Two calls on the same source path reject, including inside a
root with a false guard. Equal arguments do not excuse a duplicate call.

`@ac.method(kind="query")` is transitively read-only. It can read state and call
other explicit queries or the standard Queue's `peek`; writes, action/bare
callees, assertions, logs and reports reject. A query can still have an admission
condition, including an unavailable Queue head. Bind a query result in a normal
statement before using it in a conditional or guard predicate; native eager
expression evaluation is unchanged.

`private=True` uses native private visibility: lexical calls are allowed,
external calls reject. Private plus explicit action is currently unsupported.
Private ordinary helpers preserve the public action identities they call.

## Statement guards and observations

`ac.guard(predicate)` samples the current candidate at that statement and adds a
condition to the whole outer Rule. A late false guard discards all that caller's
proposed effects, including earlier cross-object calls. It is not an early
return: later source remains checked. A conditional statement guard applies only
on its actual source path.

Inside an object's Rule or Method, `operation.active` observes the final event
of an explicit public action on that instance. `operation.args.parameter` is the
by-value callpoint snapshot. Read arguments inside an explicit statement
`if operation.active:`; eager Boolean/conditional expressions and preceding
statement guards do not establish argument validity.

```python
@ac.method(kind="action")
def write(value: ac.u8) -> None:
    pass

@ac.rule
def update() -> None:
    if write.active:
        stored = write.args.value
```

This updater is independent. If its own guard blocks, the language does not
automatically roll back write's caller. Same-cycle object promises are library
properties that require validation.

`ac.fired(rule)` observes one statically registered lexical nested Rule, including
a void/no-write root. It does not call that Rule or read its returned payload.
This explicit spelling preserves ordinary Rule result fields such as `active`.
Arbitrary aliases, source-global templates and rootless module-body observations
are unsupported. Own-calling-root observations reject; other-root cycles are
checked by the native dependency analysis.

Events describe admission during Work. Native whole-system assertion or unknown
control failure can still discard the epoch before Xfer. They do not depend on
global assertion success. Existing zero-commit-on-failure behavior is unchanged.

## Forwarding candidate

`ac.forward(state_leaf, source=operation)` provides a bounded native profile in
this candidate. Its receiver is persistent Bits or a static Struct field ending in
Bits; its source is a registered nested Rule or explicit action with a real
potential assignment to that leaf. A notification name does not identify an
independent updater. Bare/query sources, dynamic/Table receivers, whole Struct
results and inherited formal-proposal footprints are outside this first slice.

A Rule source selects its final candidate. The initial action profile requires
that invocation's whole-owner exit version to be the root's final version;
later writes or joins to that owner reject the forward reference. Ordinary
Methods retain their existing sequential behavior. General overwritten exits
require a separately checked candidate-history certificate. Only leaves actually
written in the source subtree contribute; inactive/unwritten leaves use committed
old Q, even if the caller previously changed another candidate field. Identity
writes count. The observer acquires no implicit admission dependency or rollback
group. Own-calling-root forward references reject.

The current candidate requires relevant writes to have a proved true raw authored
path. The source mask is the OR of final fire AND each relevant raw write path,
including branches containing only state assignments. Existing field write masks
are reused; whole-owner masks added for observation never affect commit routing.
The final verifier binds payload and permission to the actual inventoried root
writer candidate and matching leaf domains. Original-source replay checks action
attribution and the exit/final restriction. This is not reconstruction of erased
Python statement history from an arbitrary final hardware artifact.

The forward mask uses ordinary four-state bit operations. It can be more unknown
than the native joined write intent: when an X condition has equal assignments in
both arms, storage can still commit a known value while OR of the individual raw
paths remains X. Forwarding does not add a knownness test or change that commit.

## Ordinary source Pipe

`pycircuit.lib.pipe.Pipe(Width=8, Depth=1)` wraps one standard latency-1 Queue
with downstream-pop readiness and a positive static capacity `Depth`.
Bare push/pop delegate to that one allocation;
the query peek reads its required committed head.
A blocked required peek/pop/push prevents the
whole outer caller from committing. A full slot can pop and replace its old
token at one edge, with no empty same-edge flow-through.
Within one Rule, pop precedes a push that needs its replacement credit; an earlier
push does not borrow credit from a later pop. A subsequent peek still reads the
committed old head until the edge.

The library is an explicit source-unit provider. It is installed as source under
`pycircuit/lib`; importing it does not execute a host hardware model. Compile
its provider and the consumer separately, then link their complete closure.
The source at `examples/native_actions/pipeline.py` uses four simple Rules and no
manually repeated ready/full conditions.

Width and Depth are native static Integer parameters. For example,
`Pipe(Width=16, Depth=4)` holds up to four tokens. Capacity does not change the
one-edge minimum availability latency; Depth is fixed at instantiation.
Zero or negative actual depths reject through the native Queue contract.
This library does not claim universal payload T, other flow modes or arbitrary
stage counts. `peek()` is a blocking committed-head query. The historical
`view()->Sample` API retains its earlier implementation identity.
