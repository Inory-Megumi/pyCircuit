# ruff: noqa: F823, F841 -- Module state captured by Rules is compiler-owned.
import pycircuit as ac


@ac.module
def SavedSnapshot() -> ac.u3:  # noqa: N802
    count: ac.u3 = 0

    @ac.rule
    def advance() -> None:
        saved = count
        count = count + 1
        count = saved + 1

    return count
