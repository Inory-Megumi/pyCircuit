# ruff: noqa: F823, F841 -- Module state captured by Rules is compiler-owned.
"""Hidden state forwards into a later root independently of public observations."""

import pycircuit as ac


@ac.module
def HiddenPair(advance: ac.u1, fold: ac.u1, incoming: ac.u3) -> ac.u3:  # noqa: N802
    visible: ac.u3 = 0
    hidden: ac.u3 = 1

    @ac.rule(guard=lambda: advance)
    def update_hidden() -> None:
        hidden = hidden + incoming

    @ac.rule(guard=lambda: fold)
    def accumulate() -> None:
        visible = visible + hidden

    ac.schedule(update_hidden, accumulate)
    return visible
