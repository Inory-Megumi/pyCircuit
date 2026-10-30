"""Static selection of the installed Runtime's existing SYNTHESIS branches."""

import re
from pathlib import Path

import pytest
from pycircuit._rtl_runtime_profile import synthesis_runtime_source


def test_known_profile_selects_only_its_declared_branch():
    source = """module example;
`ifndef SYNTHESIS
initial $fatal;
`ifdef VERILATOR
initial $finish;
`endif
`else
always_ff @(posedge clk) count <= count + 1;
`endif
endmodule
"""
    assert (
        synthesis_runtime_source(source)
        == """module example;
always_ff @(posedge clk) count <= count + 1;
endmodule
"""
    )


def test_unknown_macro_is_preserved_for_the_systemverilog_preprocessor():
    source = """`ifdef TARGET_FPGA
(* ram_style = "block" *)
`else
(* ram_style = "registers" *)
`endif
logic [7:0] initial_state;
"""
    assert synthesis_runtime_source(source) == source


@pytest.mark.parametrize(
    "source",
    [
        "`endif\n",
        "`ifdef SYNTHESIS\n",
        "`ifdef SYNTHESIS\n`else\n`else\n`endif\n",
        "`define SYNTHESIS\n",
        "`define PYCIRCUIT_PLAIN_RTL\n",
        "`ifdef SYNTHESIS\n`elsif OTHER\n`endif\n",
    ],
)
def test_malformed_or_redefined_profile_is_rejected(source):
    with pytest.raises(ValueError):
        synthesis_runtime_source(source)


def test_strings_and_ordinary_code_are_not_searched_for_diagnostics():
    source = 'module x; string label = "initial SYNTHESIS $fatal"; endmodule\n'
    assert synthesis_runtime_source(source) == source


@pytest.mark.parametrize("name", ["fifo.v", "sync_mem.v"])
def test_plain_runtime_has_only_hardware_ports_and_no_startup_process(name):
    source = Path(__file__).resolve().parents[2] / "include/verilog" / name
    text = synthesis_runtime_source(source.read_text())
    assert "pyc_phase" not in text
    assert "pyc_root_commit_ok" not in text
    assert "pyc_local_error" not in text
    assert "pyc_managed" not in text
    assert not re.search(r"^\s*initial\b", text, re.M)
