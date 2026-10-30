"""Compile/emit-only identifier and navigation checks; no circuit simulation."""

import json
import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """import pycircuit as ac
from enum import Enum
@ac.struct
class rand:
    cell: ac.u8
@ac.encoding(width=1)
class state(Enum):
    wire = 0
    cell = 1
@ac.module
def KeywordNominals(value: rand) -> tuple[rand, state]:
    return value, state.cell
@ac.struct
class Payload:
    wire: ac.u8
    packed: ac.u8
@ac.module
def cell(input: Payload, enable: ac.u1) -> Payload:
    wire: Payload = Payload()
    @ac.rule(guard=lambda: enable)
    def write() -> None:
        wire = input
    return wire
@ac.module
def Parent(input: Payload, enable: ac.u1) -> Payload:
    owned = cell(input, enable)
    return owned
@ac.module
def AnonymousParent(input: Payload, enable: ac.u1) -> Payload:
    return cell(input, enable)
@ac.module
def Maps(input: ac.table[4, ac.u8]) -> tuple[ac.table[4, ac.u8], ac.table[4, ac.u8]]:
    packed = input.map(lambda item: item + 1)
    packed_1 = packed.map(lambda item: item ^ 1)
    return packed, packed_1
@ac.module
def Route(index: ac.u1, input: Payload, enable: ac.u1) -> Payload:
    wire = ac.table[2, Payload](init=0)
    @ac.rule(guard=lambda: enable)
    def write() -> None:
        wire[index] = input
    return wire[index]
"""


@pytest.fixture(scope="module")
def structural_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("rtl-structural-names")
    source = root / "names.py"
    source.write_text(SOURCE)
    unit = root / "unit"
    _ok(
        _cli(
            "compile",
            "-c",
            str(source),
            "--source-root",
            str(root),
            "--package-prefix",
            "rtl_names",
            "-o",
            str(unit),
        )
    )
    views = {}
    for name in ("Parent", "AnonymousParent", "Maps", "Route", "KeywordNominals"):
        final = root / (name + ".ac")
        _ok(
            _cli(
                "link", str(unit), "--top", "rtl_names.names." + name, "-o", str(final)
            )
        )
        for mode in ("physical", "synthesis"):
            output = root / (name + "-" + mode)
            _ok(
                _cli(
                    "emit",
                    str(final),
                    "--target",
                    "verilog",
                    "--rtl-mode",
                    mode,
                    "-o",
                    str(output),
                )
            )
            text = (
                (output / "design_top.sv").read_text()
                + "\n"
                + "\n".join(
                    path.read_text() for path in (output / "sources").rglob("*.v")
                )
            )
            views[name, mode] = text, json.loads(
                (output / "rtl-names.json").read_text()
            )
    return views


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_authored_names_survive_ports_storage_fields_and_modules(
    structural_views, mode
):
    text, _ = structural_views["Parent", mode]
    assert "module \\cell " in text
    assert re.search(r"Payload_t \\wire ;", text)
    assert "logic [7:0] \\packed ;" in text
    assert ".\\input (" in text
    assert not re.search(r"pyc_(?:77697265|7061636b6564|63656c6c|696e707574)\b", text)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_keyword_nominals_and_members_use_source_compound_names(structural_views, mode):
    text, _ = structural_views["KeywordNominals", mode]
    assert "rand_t" in text and "state_t__cell" in text and "state_t__wire" in text
    assert not re.search(r"pyc_(?:72616e64|63656c6c|77697265)\b", text)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_anonymous_keyword_callee_uses_a_logical_identifier_stem(
    structural_views, mode
):
    text, _ = structural_views["AnonymousParent", mode]
    assert re.search(r"\\cell\s+cell_inst_[0-9]+\s*\(", text)
    assert not re.search(r"\bpyc_[0-9a-f]+\b", text)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_escaped_table_binding_has_legal_derived_generate_names(structural_views, mode):
    text, _ = structural_views["Maps", mode]
    assert "\\packed " in text
    assert "packed_rows" in text and "packed_1_rows" in text
    assert "pyc_index_" not in text and "pyc_lane_" not in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_table_routes_name_the_actual_storage_ancestor(structural_views, mode):
    text, _ = structural_views["Route", mode]
    assert (
        "begin : wire_update" in text if mode == "synthesis" else "wire_mapped_" in text
    )
    assert "pyc_lane_" not in text


@pytest.mark.parametrize("name", ["Parent", "AnonymousParent", "Maps", "Route"])
def test_navigation_ids_reference_actual_module_values(structural_views, name):
    _, mapping = structural_views[name, "synthesis"]
    assert mapping["modules"]
    for module in mapping["modules"]:
        assert module["kind"] == "hardware_module"
        assert module["source_symbol"].startswith("rtl_names.names.")
        assert module["rtl_file"].endswith("/names.v")
        ids = [value["optimized_value"] for value in module["values"]]
        assert len(ids) == len(set(ids))
        assert any(value["rtl_expression"] for value in module["values"])
        assert all(
            operand in ids
            for value in module["values"]
            for operand in value["operands"]
        )
        assert all(
            operand in ids
            for instance in module["allocations"]
            for operand in instance["inputs"] + instance["outputs"]
        )
        for binding in mapping["bindings"]:
            if binding["module"] == module["rtl_module"]:
                assert binding["optimized_value"] in ids
