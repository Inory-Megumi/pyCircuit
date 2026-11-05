"""Same-cycle wires publish only complete atomic writes, without retained state."""

from __future__ import annotations

import pytest
from test_ordered_rules import _check_final
from test_source_system_execution import _cli, _compile, _ok

pytestmark = pytest.mark.system


def _design(tmp_path, body, *, initial=3, result="count", top="Exercise", width=8):
    source = tmp_path / "source"
    source.mkdir()
    path = source / "wires.py"
    path.write_text(
        f"""import pycircuit as ac

@ac.module
def Counter() -> ac.bits[{width}]:
    count: ac.bits[{width}] = {initial}
{body}
    return {result}

@ac.system
def Exercise():
    value = Counter()
    @ac.rule
    def observe() -> None:
        ac.log("info", "wire result", value)
"""
    )
    unit = tmp_path / "unit"
    compiled = _compile(source, "wires.py", unit)
    if compiled.returncode:
        return compiled, None
    final = tmp_path / "wire.ac"
    linked = _cli("link", str(unit), "--top", f"checks.wires.{top}", "-o", str(final))
    return linked, final


@pytest.mark.parametrize("width", [8, 32])
def test_wire_returns_to_zero_without_a_new_write(tmp_path, width):
    body = f"""    event: ac.bits[{width}] = ac.dwire()
    phase: ac.u2 = 0
    @ac.rule(guard=lambda: phase == 0)
    def produce() -> None:
        event = 7
    @ac.rule
    def consume() -> None:
        count = count + event
    @ac.rule
    def advance() -> None:
        phase = phase + 1
"""
    status, final = _design(tmp_path, body, width=width)
    _ok(status)
    assert '"ac.dwire"' in final.read_text()
    _check_final(final, tmp_path, [3, 10, 10, 10])


@pytest.mark.parametrize("initial", [0, 255])
def test_independent_increment_and_decrement_cancel_at_boundaries(tmp_path, initial):
    body = """    increment: ac.u1 = ac.dwire()
    decrement: ac.u1 = ac.dwire()
    phase: ac.u2 = 0
    @ac.rule(guard=lambda: phase < 2)
    def request_increment() -> None:
        increment = 1
    @ac.rule(guard=lambda: (phase == 0) | (phase == 2))
    def request_decrement() -> None:
        decrement = 1
    @ac.rule
    def update() -> None:
        if increment != decrement:
            if increment:
                count = count + 1
            else:
                count = count - 1
    @ac.rule
    def advance() -> None:
        phase = phase + 1
"""
    status, final = _design(tmp_path, body, initial=initial)
    _ok(status)
    _check_final(
        final, tmp_path, [initial, initial, (initial + 1) % 256, initial, initial]
    )


@pytest.mark.parametrize("blocker", ["method", "queue"])
def test_blocked_writer_drives_zero_and_rolls_back_other_effects(tmp_path, blocker):
    resource = (
        "    @ac.method(guard=lambda: False)\n    def require() -> None:\n        pass\n"
        if blocker == "method"
        else "    tokens = ac.queue[ac.u8](depth=1, latency=1)\n"
    )
    deny = "require()" if blocker == "method" else "tokens.pop()"
    body = (
        resource
        + f"""    event: ac.u8 = ac.dwire()
    sent: ac.u8 = 0
    @ac.rule
    def produce() -> None:
        sent = sent + 10
        event = 7
        {deny}
    @ac.rule
    def consume() -> None:
        count = count + event
"""
    )
    status, final = _design(tmp_path, body, result="count + sent")
    _ok(status)
    _check_final(final, tmp_path, [3, 3, 3])


def test_method_write_is_bound_to_its_outer_rule(tmp_path):
    body = """    event: ac.u8 = ac.dwire()
    @ac.method
    def send(value: ac.u8) -> None:
        event = value
    @ac.rule
    def produce() -> None:
        send(4)
        send(7)
    @ac.rule
    def consume() -> None:
        count = count + event
"""
    status, final = _design(tmp_path, body)
    _ok(status)
    _check_final(final, tmp_path, [3, 10, 17])


def test_wire_output_has_no_register_delay(tmp_path):
    body = """    event: ac.u8 = ac.dwire()
    phase: ac.u1 = 0
    @ac.rule(guard=lambda: phase == 0)
    def produce() -> None:
        event = 7
    @ac.rule
    def advance() -> None:
        phase = phase + 1
"""
    status, final = _design(tmp_path, body, result="event")
    _ok(status)
    _check_final(final, tmp_path, [7, 0, 7, 0])


def test_no_writer_drives_zero(tmp_path):
    status, final = _design(tmp_path, "    event: ac.u8 = ac.dwire()\n", result="event")
    _ok(status)
    _check_final(final, tmp_path, [0, 0, 0])


def test_blocked_reader_does_not_rollback_or_buffer_writer(tmp_path):
    body = """    event: ac.u8 = ac.dwire()
    phase: ac.u2 = 0
    sent: ac.u8 = 0
    @ac.rule(guard=lambda: phase == 0)
    def produce() -> None:
        sent = sent + 1
        event = 7
    @ac.rule(guard=lambda: phase != 0)
    def consume() -> None:
        count = count + event
    @ac.rule
    def advance() -> None:
        phase = phase + 1
"""
    status, final = _design(tmp_path, body, result="count + sent")
    _ok(status)
    _check_final(final, tmp_path, [3, 4, 4, 4])


def test_guard_observes_same_cycle_wire(tmp_path):
    body = """    event: ac.u1 = ac.dwire()
    phase: ac.u2 = 0
    @ac.rule(guard=lambda: phase == 0)
    def produce() -> None:
        event = 1
    @ac.rule(guard=lambda: event)
    def consume() -> None:
        count = count + 1
    @ac.rule
    def advance() -> None:
        phase = phase + 1
"""
    status, final = _design(tmp_path, body)
    _ok(status)
    _check_final(final, tmp_path, [3, 4, 4, 4])


def test_wire_preserves_unknown_and_high_impedance_payload(tmp_path):
    body = """    event: ac.u8 = ac.dwire()
    @ac.rule
    def produce() -> None:
        event = ac.four_state("101010xz")
    @ac.rule
    def consume() -> None:
        count = event
"""
    status, final = _design(tmp_path, body)
    _ok(status)
    encoded = {"kind": "bits4", "width": 8, "value": "a8", "known": "fc", "z": "01"}
    _check_final(final, tmp_path, [3, encoded, encoded])


@pytest.mark.parametrize(
    ("body", "diagnostic"),
    [
        (
            "    event: ac.u8 = ac.dwire(7)\n",
            "takes no arguments",
        ),
        (
            """    event: ac.u8 = ac.dwire()
    @ac.rule
    def first() -> None:
        event = 1
    @ac.rule
    def second() -> None:
        event = 2
    ac.schedule(first, second)
""",
            "one atomic writer",
        ),
        (
            """    event: ac.u8 = ac.dwire()
    @ac.rule
    def feedback() -> None:
        event = event + 1
""",
            "separate atomic Rules",
        ),
        (
            """    left: ac.u8 = ac.dwire()
    right: ac.u8 = ac.dwire()
    @ac.rule
    def first() -> None:
        left = right + 1
    @ac.rule
    def second() -> None:
        right = left + 1
""",
            "cycle",
        ),
    ],
    ids=[
        "no-default-argument",
        "multiple-writers-even-when-ordered",
        "read-write-one-root",
        "combinational-cycle",
    ],
)
def test_invalid_wire_dependencies_reject_without_publication(
    tmp_path, body, diagnostic
):
    status, final = _design(tmp_path, body)
    assert status.returncode != 0
    assert diagnostic in status.stderr, status.stderr
    assert final is None or not final.exists()
