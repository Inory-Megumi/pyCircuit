# ruff: noqa: F823, F841 -- Module state captured by Rules is compiler-owned.
import pycircuit as ac


@ac.module
def GuardedCounter(inc_request: ac.u1, dec_request: ac.u1) -> ac.u3:  # noqa: N802
    count: ac.u3 = 0

    @ac.rule(guard=lambda: inc_request & (count < 5))
    def increment() -> None:
        count = count + 1

    @ac.rule(guard=lambda: dec_request & (count > 0))
    def decrement() -> None:
        count = count - 1

    ac.schedule(increment, decrement)
    return count
