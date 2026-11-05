"""Readable physical RTL retains arithmetic, four-state data and Rule ordering."""

from __future__ import annotations

import json

import pytest
from test_dwire_physical import _physical
from test_dwires import _design
from test_physical_rtl_export import simulate
from test_source_system_execution import ROOT, _cli, _compile, _ok

pytestmark = pytest.mark.system


def _source(tmp_path, text, top="Example"):
    source = tmp_path / "source"
    source.mkdir()
    (source / "design.py").write_text(text)
    unit = tmp_path / "unit"
    _ok(_compile(source, "design.py", unit))
    final = tmp_path / "design.ac"
    _ok(_cli("link", str(unit), "--top", "checks.design." + top, "-o", str(final)))
    return final


def _mapping(output):
    mapping = json.loads((output / "rtl-names.json").read_text())
    assert mapping["kind"] == "pycircuit.rtl-names"
    assert mapping["definitions"]
    for definition in mapping["definitions"]:
        values = definition["values"]
        ids = {value["id"] for value in values}
        assert len(ids) == len(values)
        signals = [
            value["name"] for value in values if value["disposition"] == "signal"
        ]
        assert len(signals) == len(set(signals))
        assert all(set(value["consumers"]) <= ids for value in values)
        assert all(value["source"] for value in values)
        by_id = {value["id"]: value for value in values}
        assert all(value["representative"] in ids for value in values)
        for value in values:
            if value["disposition"] == "alias":
                target = by_id[value["representative"]]
                assert target["representative"] == target["id"]
                assert value["rendering"] == target["rendering"]
        origins = definition["source_values"]
        assert len({origin["id"] for origin in origins}) == len(origins)
        assert all(origin["value"] in ids and origin["source"] for origin in origins)
        assert all(
            check["condition"] in ids and check["path"] in ids
            for check in definition["checks"]
        )
    return mapping["definitions"]


def test_counter_names_trace_actual_rules(tmp_path):
    unit = tmp_path / "unit"
    _ok(_compile(ROOT / "examples/dwire_counter", "dwire_counter.py", unit))
    final = tmp_path / "counter.ac"
    _ok(
        _cli(
            "link", str(unit), "--top", "checks.dwire_counter.Counter", "-o", str(final)
        )
    )
    output = _physical(final, tmp_path)
    definition = next(
        item for item in _mapping(output) if item["definition"].endswith(".Counter")
    )
    values = definition["values"]
    signals = {item["name"]: item for item in values if item["disposition"] == "signal"}
    assert {"count", "inc", "dec"} <= signals.keys()
    assert signals["inc"]["rule"] == "increment"
    assert signals["dec"]["rule"] == "decrement"
    assert "rule_occurrence" in signals["inc"]
    rtl = (output / definition["rtl_file"]).read_text()
    assert (
        "// Rule increment" in rtl
        and "// Rule decrement" in rtl
        and "// Rule update" in rtl
    )
    assert "pyc_" not in rtl
    assert "input wire clk," in rtl and "input wire rst," in rtl
    assert "output wire [7:0] result" in rtl
    header = rtl.split(");", 1)[0]
    assert all(
        name not in header for name in ("root_commit_ok", "reset_active", "local_error")
    )
    assert "[(1)-1:0]" not in rtl and "wire logic" not in rtl
    ports = json.loads((output / "ports.json").read_text())
    for role, spelling in (("clock", "clk"), ("reset", "rst")):
        assert ports["inputs"][ports["domains"][role]]["wire"] == spelling
    # The public source map is complementary to, not replaced by, the name map.
    assert list(output.rglob("*.source-map.json"))
    # Normalize before naming and use counting: all proof aliases share one net.
    assert "assign count_write = (inc != dec);" in rtl
    assert "update_ne" not in rtl and "update_select_3" not in rtl
    write = signals["count_write"]
    assert any(
        item["disposition"] == "alias" and item["representative"] == write["id"]
        for item in values
    )
    origins = definition["source_values"]
    assert len([origin for origin in origins if origin["value"] == write["id"]]) > 1
    assert rtl.count("localparam ") == 1
    assert "localparam logic [7:0] count_init = 8'd3;" in rtl
    assert {item["name"] for item in definition["initializers"]} == {"count_init"}
    assert any(check["disposition"] == "proven-zero" for check in definition["checks"])
    assert "$isunknown(1'b1)" not in rtl
    assert "$isunknown(inc_request)" in rtl and "$isunknown(dec_request)" in rtl
    wrapper = (output / "design_top.sv").read_text()
    assert "package " not in wrapper and "function " not in wrapper


def test_shared_value_and_name_collision_preserve_wrapping_arithmetic(tmp_path):
    final = _source(
        tmp_path,
        """import pycircuit as ac
@ac.module
def Example(incoming: ac.u8, other: ac.u8, count_next: ac.u8) -> tuple[ac.u8, ac.u8, ac.u8]:
    count: ac.u8 = 3
    shared = incoming * other
    @ac.rule
    def update() -> None:
        count = incoming + other
    return shared, shared + count, count
""",
    )
    output = _physical(final, tmp_path)
    values = _mapping(output)[0]["values"]
    products = [
        item
        for item in values
        if item.get("operation") == "ac.bits.binary"
        and item["uses"] > 1
        and item["disposition"] == "signal"
    ]
    assert products, "multi-consumer arithmetic must remain materialized"
    assert not any(
        item["name"] == "count_next" and item["disposition"] == "signal"
        for item in values
    )
    transcript = simulate(
        output,
        tmp_path,
        """
#1;if(result_0!==8'd196 || result_1!==8'd199 || result_2!==8'd3)$fatal(1,"initial shared result");
edge_up();edge_down();
if(result_0!==8'd196 || result_1!==8'd200 || result_2!==8'd4)$fatal(1,"wrapped result");
""",
        initialize="incoming=250;other=10;count_next=0;",
        verilator=True,
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript


def test_z_bitwise_data_is_not_replaced_with_a_wire_alias(tmp_path):
    final = _source(
        tmp_path,
        """import pycircuit as ac
@ac.module
def Example(incoming: ac.u1) -> tuple[ac.u1, ac.u1]:
    @ac.rule
    def compute() -> tuple[ac.u1, ac.u1]:
        return incoming & 1, incoming | 0
    return compute
""",
    )
    output = _physical(final, tmp_path)
    _mapping(output)
    transcript = simulate(
        output,
        tmp_path,
        """
#1;if(result_0!==1'b0 || result_1!==1'b0)$fatal(1,"zero data");
incoming=1;#1;if(result_0!==1'b1 || result_1!==1'b1)$fatal(1,"one data");
incoming=1'bx;#1;if(result_0!==1'bx || result_1!==1'bx)$fatal(1,"X data");
incoming=1'bz;#1;if(result_0!==1'bx || result_1!==1'bx)$fatal(1,"Z must normalize to X");
""",
        initialize="incoming=0;",
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript


def test_scheduled_versions_keep_both_rules_and_forward_state(tmp_path):
    status, final = _design(
        tmp_path,
        """    @ac.rule
    def first() -> None:
        count = count + 1
    @ac.rule
    def second() -> None:
        count = count * 2
    ac.schedule(first, second)
""",
        top="Counter",
    )
    _ok(status)
    output = _physical(final, tmp_path)
    definition = next(
        item for item in _mapping(output) if item["definition"].endswith(".Counter")
    )
    rtl = (output / definition["rtl_file"]).read_text()
    assert "// Rule first" in rtl and "// Rule second" in rtl
    transcript = simulate(
        output,
        tmp_path,
        """
if(result_0!==8'd3)$fatal(1,"initial state");
edge_up();edge_down();if(result_0!==8'd8)$fatal(1,"forward first addition");
edge_up();edge_down();if(result_0!==8'd18)$fatal(1,"forward second addition");
""",
        initialize="",
        verilator=True,
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript
