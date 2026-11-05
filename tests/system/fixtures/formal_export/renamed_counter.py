# ruff: noqa: F823, F841 -- Module state captured by Rules is compiler-owned.
import pycircuit as ac


@ac.module
def RenamedCounter(raise_request: ac.u1, lower_request: ac.u1) -> ac.u4:  # noqa: N802
    occupancy: ac.u4 = 0

    @ac.rule(guard=lambda: raise_request & (occupancy < 9))
    def raise_level() -> None:
        occupancy = occupancy + 1

    @ac.rule(guard=lambda: lower_request & (occupancy > 0))
    def lower_level() -> None:
        occupancy = occupancy - 1

    ac.schedule(raise_level, lower_level)
    return occupancy
