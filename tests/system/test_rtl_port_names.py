"""Physical interfaces share an identity-based namespace with internal signals."""

from __future__ import annotations

import json
import re

import pytest
from test_dwire_physical import _physical
from test_physical_rtl_export import simulate
from test_rtl_presentation import _mapping, _source

pytestmark = pytest.mark.system


def _rtl(output):
    manifest = json.loads((output / "generated.json").read_text())
    return "\n".join(
        (output / item["path"]).read_text()
        for item in manifest["files"]
        if item["path"].endswith((".v", ".sv"))
    )


def test_domain_and_private_controls_do_not_shadow_authored_ports(tmp_path):
    final = _source(
        tmp_path,
        """import pycircuit as ac
@ac.module
def Child(clk: ac.u8, rst: ac.u8, root_commit_ok: ac.u8, reset_active: ac.u8,
          local_error: ac.u8, dut: ac.u8) -> ac.u8:
    saved: ac.u8 = 3
    @ac.rule
    def update() -> None:
        saved = clk + rst + root_commit_ok + reset_active + local_error + dut
    return saved
@ac.module
def Example(clk: ac.u8, rst: ac.u8, root_commit_ok: ac.u8, reset_active: ac.u8,
            local_error: ac.u8, dut: ac.u8) -> ac.u8:
    return Child(clk, rst, root_commit_ok, reset_active, local_error, dut)
""",
    )
    output = _physical(final, tmp_path)
    ports = json.loads((output / "ports.json").read_text())
    inputs = ports["inputs"]
    domains = ports["domains"]
    assert inputs[domains["clock"]]["wire"] == "clk_2"
    assert inputs[domains["reset"]]["wire"] == "rst_2"
    assert len({row["wire"] for row in inputs}) == len(inputs)
    assert {row["wire"] for row in inputs[:6]} == {
        "clk",
        "rst",
        "root_commit_ok",
        "reset_active",
        "local_error",
        "dut",
    }
    rtl = _rtl(output)
    assert not re.search(r"\bpyc_\w+", rtl)
    assert "input wire [7:0] clk" in rtl
    assert "input wire clk_2" in rtl
    assert ".clk_2(clk_2)" in rtl
    _mapping(output)
    transcript = simulate(
        output,
        tmp_path,
        """
if(result_0!==8'd3)$fatal(1,"startup");
edge_up();edge_down();if(result_0!==8'd63)$fatal(1,"data ports aliased to controls");
clk=2;rst=4;edge_up();edge_down();
if(result_0!==8'd66)$fatal(1,"hierarchical port wiring");
""",
        initialize="clk=1;rst=2;root_commit_ok=4;reset_active=8;local_error=16;dut=32;",
        domain_names=("domain_clock", "domain_reset"),
        instance_name="subject",
        verilator=True,
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript


def test_parameter_width_remains_symbolic_in_definition(tmp_path):
    final = _source(
        tmp_path,
        """import pycircuit as ac
@ac.module
def Example(incoming: ac.bits[W], flag: ac.u1, *, W: int = 8) -> tuple[ac.bits[W], ac.u1]:
    @ac.rule
    def compute() -> tuple[ac.bits[W], ac.u1]:
        return incoming | 0, flag | 0
    return compute
""",
    )
    output = _physical(final, tmp_path)
    rtl = _rtl(output)
    assert "parameter longint signed parameter_W" in rtl
    assert "[(parameter_W)-1:0]" in rtl
    assert "input wire flag" in rtl
    assert "input wire [7:0] incoming" in rtl
    assert "[(1)-1:0]" not in rtl
    assert not re.search(r"\bpyc_\w+", rtl)
    transcript = simulate(
        output,
        tmp_path,
        """
edge_up();edge_down();if(result_0!==8'd165 || result_1!==1'b1)$fatal(1,"parameterized data");
incoming=18;flag=0;edge_up();edge_down();
if(result_0!==8'd18 || result_1!==1'b0)$fatal(1,"scalar data");
""",
        initialize="incoming=165;flag=1;",
        verilator=True,
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript


def test_one_bit_packed_table_keeps_indexable_range(tmp_path):
    final = _source(
        tmp_path,
        """import pycircuit as ac
@ac.module
def Example(incoming: ac.u1) -> ac.table[1, ac.u1]:
    saved: ac.table[1, ac.u1] = 0
    @ac.rule
    def update() -> None:
        saved[0] = incoming
    return saved
""",
    )
    output = _physical(final, tmp_path)
    assert "output wire [0:0] result" in _rtl(output)
    transcript = simulate(
        output,
        tmp_path,
        """
edge_up();edge_down();if(result_0!==1'b1)$fatal(1,"packed scalar element");
incoming=0;edge_up();edge_down();if(result_0!==1'b0)$fatal(1,"packed scalar update");
""",
        initialize="incoming=1;",
        verilator=True,
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript


def test_private_check_scope_does_not_shadow_functional_values(tmp_path):
    final = _source(
        tmp_path,
        """import pycircuit as ac
@ac.module
def Example(value: ac.u8, error: ac.u8, checks: ac.u1,
            commit_ok: ac.u1, physical_fault: ac.u1) -> ac.u8:
    saved: ac.u8 = 1
    @ac.rule(guard=lambda: checks)
    def update() -> None:
        if commit_ok:
            saved = value + error
            if physical_fault:
                saved = saved + 1
    return saved
""",
    )
    output = _physical(final, tmp_path)
    transcript = simulate(
        output,
        tmp_path,
        """
edge_up();edge_down();if(result_0!==8'd17)$fatal(1,"private names shadow input data");
commit_ok=0;value=20;edge_up();edge_down();
if(result_0!==8'd17)$fatal(1,"authored guard lost");
commit_ok=1;checks=1'bx;edge_up();edge_down();
if(result_0!==8'd17)$fatal(1,"guard fault committed");
checks=1;edge_up();edge_down();if(result_0!==8'd17)$fatal(1,"fault was not sticky");
""",
        initialize="value=7;error=9;checks=1;commit_ok=1;physical_fault=1;",
    )
    assert transcript.count("PYCIRCUIT_PHYSICAL_FAULT") == 1
