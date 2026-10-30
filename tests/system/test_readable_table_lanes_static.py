"""Typed table construction checks; compile/link/emit only, no simulation."""

import json
import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """import pycircuit as ac
from enum import Enum
@ac.encoding(width=3)
class Mode(Enum):
    EMPTY = 0
    READY = 5
@ac.struct
class Item:
    mode: Mode
    data: ac.u8
@ac.struct
class Envelope:
    payload: Item
    code: ac.u4
@ac.module
def Routed(index: ac.u2, incoming: ac.u8, enable: ac.u1) -> ac.u8:
    entries: ac.table[4, ac.u8] = (1, 2, 3, 4)
    @ac.rule(guard=lambda: enable)
    def write() -> None:
        entries[index] = incoming
    return entries[index]
@ac.module
def Partial(index: ac.u2, incoming: ac.u8, enable: ac.u1) -> Item:
    entries = ac.table[4, Item](init=0)
    @ac.rule(guard=lambda: enable)
    def write() -> None:
        entries[index].data = incoming
        if incoming != 0:
            entries[index].mode = Mode.READY
    return entries[index]
@ac.module
def Ordered(first: ac.u2, second: ac.u2, incoming: Item, enable: ac.u1) -> Item:
    entries = ac.table[4, Item](init=0)
    @ac.method
    def first_write() -> None:
        if enable:
            entries[first] = incoming
    @ac.method
    def second_write() -> Item:
        observed = entries[second]
        if enable:
            entries[second] = Item(mode=observed.mode, data=observed.data + 1)
        return observed
    @ac.rule
    def transact() -> Item:
        first_write()
        return second_write()
    return transact
@ac.module
def PrivateMaps(values: ac.table[3, ac.u8]) -> ac.table[3, ac.u8]:
    return values.map(lambda item: item + 1).map(lambda item: item ^ 3)
@ac.module
def SharedMaps(values: ac.table[3, ac.u8]) -> tuple[ac.table[3, ac.u8], ac.table[3, ac.u8]]:
    shared = values.map(lambda item: item + 1)
    return shared.map(lambda item: item ^ 3), shared.map(lambda item: item & 7)
@ac.module
def Captures(values: ac.table[3, ac.u8], first: ac.u8, second: ac.u8) -> ac.table[3, ac.u8]:
    increment = first + second
    return values.map(lambda item: item + increment)
@ac.module
def Wide(index: ac.u1, incoming: ac.bits[65], enable: ac.u1) -> ac.bits[65]:
    entries = ac.table[2, ac.bits[65]](init=0)
    @ac.rule(guard=lambda: enable)
    def write() -> None:
        entries[index] = incoming
    return entries[index]
@ac.module
def Enums(index: ac.u2, incoming: Mode, enable: ac.u1) -> Mode:
    entries = ac.table[4, Mode](init=0)
    @ac.rule(guard=lambda: enable)
    def write() -> None:
        entries[index] = incoming
    return entries[index]
@ac.module
def Nested(index: ac.u1, incoming: Envelope, enable: ac.u1) -> Envelope:
    entries = ac.table[2, Envelope](init=0)
    @ac.method
    def write() -> None:
        if enable:
            entries[index] = incoming
    @ac.rule
    def transact() -> None:
        write()
    return entries[index]
"""

ROOTS = (
    "Routed",
    "Partial",
    "Ordered",
    "PrivateMaps",
    "SharedMaps",
    "Captures",
    "Wide",
    "Enums",
    "Nested",
)


@pytest.fixture(scope="module")
def lane_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-table-lanes")
    source = root / "lanes.py"
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
            "readable_lanes",
            "-o",
            str(unit),
        )
    )
    views = {}
    for name in ROOTS:
        final = root / (name + ".ac")
        _ok(
            _cli(
                "link",
                str(unit),
                "--top",
                "readable_lanes.lanes." + name,
                "-o",
                str(final),
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
            text = "\n".join(
                path.read_text() for path in (output / "sources").rglob("*.v")
            )
            views[name, mode] = text, json.loads(
                (output / "rtl-names.json").read_text()
            )
    return views


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
@pytest.mark.parametrize(
    "name", ["Routed", "Partial", "Ordered", "Wide", "Enums", "Nested"]
)
def test_storage_uses_one_row_block_and_exact_scalar_domain(lane_views, name, mode):
    text, mapping = lane_views[name, mode]
    if mode == "synthesis":
        assert text.count("always_ff") == 1
        assert "begin : entries_update" in text and "always_ff @(posedge clk)" in text
        assert re.search(r"if \(rst\)", text)
        assert "entries[entries_lane] <=" in text
        assert not re.search(r"\b(?:splat|map_input|map_output)_[0-9]+", text)
        assert any(
            value.get("rtl_scope") == "entries_update"
            for module in mapping["modules"]
            for value in module["values"]
        )
        assert not re.search(r"\binitial\b|__checks|pyc_phase", text)
    else:
        assert ".pyc_root_commit_ok(__checks_allow)" in text
        assert "dffe #" in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_private_map_chain_has_one_loop_without_transport_arrays(lane_views, mode):
    text, _ = lane_views["PrivateMaps", mode]
    assert text.count("for (genvar") == 1
    assert (
        len(re.findall(r"\s\+\s", text)) == 1 and len(re.findall(r"\s\^\s", text)) == 1
    )
    assert not re.search(r"wire logic \[0:2\].*(?:map_input|mapped_.*mapped_)", text)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_authored_shared_map_is_materialized_once(lane_views, mode):
    text, _ = lane_views["SharedMaps", mode]
    assert "logic [0:2] [7:0] shared;" in text
    assert len(re.findall(r"\s\+\s", text)) == 1
    assert text.count("shared[") == 3


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_map_scalar_capture_is_computed_once_outside_lane_loop(lane_views, mode):
    text, _ = lane_views["Captures", mode]
    assert "increment" in text and text.index("assign increment") < text.index(
        "for (genvar"
    )
    assert len(re.findall(r"\s\+\s", text)) == 2
    assert not re.search(r"logic \[0:2\].*splat", text)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_packed_order_reset_values_bounds_and_wide_carrier_are_retained(
    lane_views, mode
):
    text, _ = lane_views["Routed", mode]
    assert "{8'd1, 8'd2, 8'd3, 8'd4}" in text
    assert re.search(r"entries[^\s]*\[\$unsigned\(index\)\]", text)
    assert re.search(r"\(3\)'\(\$unsigned\(index\)\) < \(3\)'\(4\)", text)
    wide, _ = lane_views["Wide", mode]
    assert re.search(r"\[64:0\] entries[^\s]*;", wide) and "65'd0" in wide
    enums, _ = lane_views["Enums", mode]
    assert (
        re.search(r"Mode_t \[0:3\] entries[^\s]*;", enums) and "Mode_t__EMPTY" in enums
    )


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_read_after_write_candidate_remains_one_shared_vector(lane_views, mode):
    text, mapping = lane_views["Ordered", mode]
    # The post-first-write table feeds the observed value and the second write.
    # It must stay materialized, with one route for each original write.
    assert text.count("for (genvar") == (2 if mode == "synthesis" else 3)
    assert text.count(" == first") == 1 and text.count(" == second") == 1
    assert len(re.findall(r"\s\+\s", text)) == 1
    assert "observed" in text and ".mode" in text and ".data" in text
    assert any(
        value.get("rtl_scope", "").endswith("_rows")
        for module in mapping["modules"]
        for value in module["values"]
    )


@pytest.mark.parametrize(
    "kind,stage,diagnostic",
    [
        ("extent", "compile", "table index complete width is not proven in range"),
        (
            "partial",
            "link",
            None,
        ),
    ],
)
def test_source_admission_matches_current_contract(tmp_path, kind, stage, diagnostic):
    body = (
        """import pycircuit as ac
@ac.module
def Bad(index: ac.u2, incoming: ac.u8) -> ac.u8:
    entries = ac.table[3, ac.u8](init=0)
    @ac.rule
    def access() -> None:
        entries[index] = incoming
    return entries[index]
"""
        if kind == "extent"
        else """import pycircuit as ac
@ac.module
def Bad(first: ac.u2, second: ac.u2, incoming: ac.u8, enable: ac.u1) -> ac.u8:
    entries = ac.table[4, ac.u8](init=0)
    @ac.rule(guard=lambda: enable)
    def access() -> ac.u8:
        entries[first] = incoming
        observed = entries[second]
        return observed
    return access
"""
    )
    source, unit, final = tmp_path / "bad.py", tmp_path / "unit", tmp_path / "bad.ac"
    source.write_text(body)
    compiled = _cli(
        "compile",
        "-c",
        str(source),
        "--source-root",
        str(tmp_path),
        "--package-prefix",
        "lane_rejections",
        "-o",
        str(unit),
    )
    if stage == "compile":
        rejected = compiled
        assert not unit.exists()
    else:
        _ok(compiled)
        rejected = _cli(
            "link", str(unit), "--top", "lane_rejections.bad.Bad", "-o", str(final)
        )
        # The current upstream verifier proves selected-row availability for
        # this guarded write/read. Preserve that admitted contract.
        _ok(rejected)
        assert final.is_file()
        return
    assert rejected.returncode != 0 and diagnostic in rejected.stdout + rejected.stderr
