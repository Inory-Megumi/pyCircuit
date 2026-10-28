# Method composition

Method composition uses one contract. A Method defines its
ordinary state update; the calling outer Rule owns atomic commit. A composer
declares admission and resolves simultaneous successful operations. It creates
no independent Rule or runtime operation queue.

```python
@ac.module
def Counter():
    count: ac.u3 = 0

    @ac.method
    def inc() -> None:
        count = count + 1

    @ac.method
    def dec() -> None:
        count = count - 1

    @ac.compose(target=count, operations=(inc, dec))
    def combine(old, ops):
        ops.dec.ready = old != 0
        ops.inc.ready = (old < 7) or ops.dec.active
        return old

    @ac.method
    def read() -> ac.u3:
        return count
```

All ready declarations must be unconditional leading assignments. Missing ready
means true; existing Method guards are also required. Ready expressions use the closed composer scope: declared old-state and
peer-active views plus closed constants. They cannot capture Method arguments,
Module runtime inputs, unrelated owner state or compiler temporary names.
Parameter-dependent conditions belong in the ordinary Method guard. They may not
read candidate values/write views or their own final activity. Actual dependency
cycles are rejected, not solved by iteration. Public `ac.admit` is removed.

`active` includes the invocation branch and the entire outer Rule's final commit,
including downstream resource availability and guards after the Method call.
The example can increment a full counter only if decrement commits. An empty
counter does not consume a same-cycle increment. Independent Rules still read
committed current state; this readiness dependency does not forward candidate data.

The selected next state follows one rule:

| Successful operations | Selected value |
| --- | --- |
| None | Old state |
| Exactly one | That Method's complete candidate |
| Two or more | Composer return value |

The return expression can use `old`, `ops.<name>.active`,
`ops.<name>.value` and `ops.<name>.writes`. It is a pure combinational expression;
its hardware need not be inactive when its result is unselected. For write/clear
with clear priority the whole body can be `return ops.clear.value`. With three or
more operations, the author must resolve every possible overlapping subset.

Multiple scalar targets use `target=(count, valid)`, views `old.count` and
`ops.inc.value.count`, and a return tuple in target order. A registered derived
field such as valid must be updated in each Method's ordinary candidate, or be
represented as a read-only expression. It cannot rely on the overlap-only return
to repair singleton updates. Struct and native Table targets use the same
candidate and authored-write views; this does not add Table port declarations,
address-matched capacity credit or arbitration.

One operation may have multiple statically exclusive invocation sites. Different
operations can run in distinct Rules simultaneously or in mutually exclusive
branches of one Rule. Multiple calls of the same operation that can co-occur,
and sequential same-group calls in one Rule, remain rejected. A composer does
not arbitrate callers. Source replay and final hardware wiring checks retain
the owner, candidate, branch and final-commit proofs.

Named FSM edges can be elaborated to distinct guarded Methods. An edge's source
condition remains a Method guard; compatible simultaneous edges use the same
composer contract. Writers proven mutually exclusive can use ordinary writer
checks. When those checks cannot prove the guards disjoint, an explicit composer
is still required; the extension does not expand that separate proof engine.
