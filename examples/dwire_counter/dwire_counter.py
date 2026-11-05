# ruff: noqa: F823 -- Module variables captured by Rules are compiler-owned.
from pycircuit import bits, dwire, log, module, rule, system


@module
def Counter(inc_request: bits[1], dec_request: bits[1]) -> bits[8]:  # noqa: N802
    count: bits[8] = 3
    inc: bits[1] = dwire()
    dec: bits[1] = dwire()

    @rule(guard=lambda: inc_request)
    def increment() -> None:
        inc = 1

    @rule(guard=lambda: dec_request)
    def decrement() -> None:
        dec = 1

    @rule
    def update() -> None:
        if inc != dec:
            if inc:
                count = count + 1
            else:
                count = count - 1

    return count


@system
def ExerciseDWireCounter():  # noqa: N802
    phase: bits[2] = 0
    value = Counter(phase < 2, (phase == 0) | (phase == 2))

    @rule
    def advance() -> None:
        phase = phase + 1

    @rule
    def observe() -> None:
        log("info", "dwire count", value)
