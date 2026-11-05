"""DWire domain metadata permits physical export without adding storage."""

from __future__ import annotations

import pytest
from test_dwires import _design
from test_physical_rtl_export import simulate
from test_source_system_execution import ROOT, _cli, _compile, _ok

pytestmark = pytest.mark.system


def _physical(final, tmp_path):
    output = tmp_path / "physical"
    _ok(
        _cli(
            "emit",
            str(final),
            "--target",
            "verilog",
            "--rtl-mode",
            "physical",
            "-o",
            str(output),
        )
    )
    return output


def test_counter_requests_cancel_and_update_on_the_same_edge(tmp_path):
    unit = tmp_path / "unit"
    _ok(_compile(ROOT / "examples/dwire_counter", "dwire_counter.py", unit))
    final = tmp_path / "counter.ac"
    _ok(
        _cli(
            "link",
            str(unit),
            "--top",
            "checks.dwire_counter.Counter",
            "-o",
            str(final),
        )
    )
    transcript = simulate(
        _physical(final, tmp_path),
        tmp_path,
        """
if(result_0!==8'd3)$fatal(1,"reset value");
inc_request=1;dec_request=1;edge_up();edge_down();
if(result_0!==8'd3)$fatal(1,"simultaneous requests must cancel");
dec_request=0;edge_up();edge_down();
if(result_0!==8'd4)$fatal(1,"increment must affect this edge");
inc_request=0;dec_request=1;edge_up();edge_down();
if(result_0!==8'd3)$fatal(1,"decrement must affect this edge");
dec_request=0;edge_up();edge_down();
if(result_0!==8'd3)$fatal(1,"inactive wires must not retain requests");
""",
        initialize="inc_request=0;dec_request=0;",
        verilator=True,
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript


def test_physical_wire_preserves_four_state_payload_and_returns_to_zero(tmp_path):
    status, final = _design(
        tmp_path,
        """    event: ac.u8 = ac.dwire()
    phase: ac.u1 = 0
    @ac.rule(guard=lambda: phase == 0)
    def produce() -> None:
        event = ac.four_state("101010xz")
    @ac.rule
    def advance() -> None:
        phase = phase + 1
""",
        top="Counter",
        result="event",
    )
    _ok(status)
    transcript = simulate(
        _physical(final, tmp_path),
        tmp_path,
        """
#1;if(result_0!==8'b101010xz)$fatal(1,"same-cycle X/Z payload");
edge_up();edge_down();
if(result_0!==8'd0)$fatal(1,"wire must return to zero without a write");
edge_up();edge_down();
if(result_0!==8'b101010xz)$fatal(1,"next write must be immediately visible");
""",
        initialize="",
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript
