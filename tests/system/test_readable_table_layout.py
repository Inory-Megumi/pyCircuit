"""Compile/emit-only packed Table layout checks; no circuit execution."""

import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """import pycircuit as ac
from enum import Enum
@ac.encoding(width=2)
class Mode(Enum):
    IDLE = 0
    RUN = 1
@ac.struct
class Item:
    tag: ac.u4
    data: ac.u8
@ac.struct
class Holder:
    rows: ac.table[2, Item]
    code: ac.u4
@ac.module
def ByteTable(values: ac.table[4, ac.u8]) -> ac.table[4, ac.u8]:
    return values
@ac.module
def ItemTable(values: ac.table[4, Item]) -> ac.table[4, Item]:
    return values
@ac.module
def ModeTable(values: ac.table[3, Mode]) -> ac.table[3, Mode]:
    return values
@ac.module
def HolderValue(value: Holder) -> Holder:
    return value
@ac.module
def ItemRead(values: ac.table[4, Item], index: ac.u2) -> Item:
    return values[index]
"""

NESTED_TABLE_SOURCE = """import pycircuit as ac
@ac.module
def Nested(values: ac.table[2, ac.table[3, ac.u4]]) -> ac.table[2, ac.table[3, ac.u4]]:
    return values
"""


@pytest.fixture(scope="module")
def table_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-table-layout")
    source = root / "tables.py"
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
            "readable_tables",
            "-o",
            str(unit),
        )
    )
    views = {}
    for name in ("ByteTable", "ItemTable", "ModeTable", "HolderValue", "ItemRead"):
        final = root / (name + ".ac")
        _ok(
            _cli(
                "link",
                str(unit),
                "--top",
                "readable_tables.tables." + name,
                "-o",
                str(final),
            )
        )
        modes = (
            ("managed", "physical", "synthesis")
            if name == "ByteTable"
            else ("physical", "synthesis")
        )
        for mode in modes:
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
            views[name, mode] = (
                (output / "design_top.sv").read_text()
                + "\n"
                + "\n".join(
                    path.read_text() for path in (output / "sources").rglob("*.v")
                )
            )
    return views


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
@pytest.mark.parametrize(
    "name,pattern",
    [
        ("ByteTable", r"logic \[0:3\] \[7:0\] values"),
        ("ItemTable", r"Item_t \[0:3\] values"),
        ("ModeTable", r"Mode_t \[0:2\] values"),
        ("HolderValue", r"Item_t \[0:1\] rows;"),
    ],
)
def test_closed_tables_keep_outer_to_inner_packed_dimensions(
    table_views, mode, name, pattern
):
    assert re.search(pattern, table_views[name, mode])


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_dynamic_record_selection_uses_one_typed_lane(table_views, mode):
    text = table_views["ItemRead", mode]
    assert "values[$unsigned(index)]" in text
    assert re.search(r"\(3\)\x27\(\$unsigned\(index\)\) < \(3\)\x27\(4\)", text)


def test_managed_layout_retains_its_original_flat_vector(table_views):
    assert re.search(
        r"logic \[\(32\)-1:0\] values", table_views["ByteTable", "managed"]
    )


def test_source_table_of_table_is_still_rejected(tmp_path):
    source = tmp_path / "nested.py"
    source.write_text(NESTED_TABLE_SOURCE)
    output = tmp_path / "unit"
    result = _cli(
        "compile",
        "-c",
        str(source),
        "--source-root",
        str(tmp_path),
        "--package-prefix",
        "nested_table",
        "-o",
        str(output),
    )
    assert result.returncode != 0
    assert (
        "table element requires explicitly unsigned bits or nominal struct/enum"
        in result.stdout + result.stderr
    )
    assert not output.exists()
