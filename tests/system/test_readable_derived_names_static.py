"""Anonymous constructor and result-slot names; native compile/emit only."""

import json
import os
import re

import pytest
from test_source_system_execution import _cli, _ok, _run

SOURCE = """from enum import Enum
import pycircuit as ac
@ac.struct
class Cell:
    tag: ac.u4
    data: ac.u8
@ac.struct
class Envelope:
    payload: Cell
    code: ac.u4
@ac.encoding(width=3)
class Mode(Enum):
    IDLE = 0
    RUN = 3
    DONE = 5
@ac.module
def BulkRows(index: ac.u2, clear: ac.u1) -> Cell:
    bank = ac.table[5, Cell](init=0)
    @ac.method
    def wipe() -> None:
        if clear:
            bank = 0
    @ac.rule
    def transact() -> None:
        wipe()
    return bank[index]
@ac.module
def Nested(tag: ac.u4, data: ac.u8) -> Envelope:
    return Envelope(payload=Cell(tag=tag, data=data), code=tag)
@ac.module
def Shared(tag: ac.u4, first: ac.u8, second: ac.u8) -> tuple[Cell, Cell]:
    return Cell(tag=tag, data=first + second), Cell(tag=tag, data=first + second)
@ac.module
def Decode(raw: ac.u3) -> tuple[Mode, bool]:
    carrier, inside = ac.enum_from_bits[Mode](raw)
    return carrier, inside
@ac.module
def NamedDecode(raw: ac.u3) -> tuple[Mode, bool]:
    decoded, member = ac.enum_from_bits[Mode](raw)
    return decoded, member
@ac.module
def Collision(values: ac.table[3, Cell], index: ac.u1,
              first: ac.u8, second: ac.u8) -> tuple[Cell, ac.u8]:
    index_in_range = first + second
    return values[index], index_in_range
@ac.module
def SharedRead(values: ac.table[3, Cell], index: ac.u1) -> tuple[Cell, Cell]:
    return values[index], values[index]
@ac.module
def Choice(take: ac.u1, first: ac.u8, second: ac.u8) -> Cell:
    return Cell(tag=1, data=first) if take else Cell(tag=2, data=second)
@ac.module
def ShortNames(a: ac.u8, b: ac.u8, c: ac.u8, d: ac.u8) -> ac.u8:
    return ((a + b) ^ (c + d)) + ((a ^ b) & (c | d))
"""

SOURCE += (
    SOURCE[
        SOURCE.index("@ac.module\ndef BulkRows") : SOURCE.index(
            "@ac.module\ndef Nested"
        )
    ]
    .replace("BulkRows", "Relabeled")
    .replace("bank", "slots")
    .replace("wipe", "erase_all")
)
SOURCE += (
    SOURCE[
        SOURCE.index("@ac.module\ndef ShortNames") : SOURCE.index(
            "@ac.module\ndef Relabeled"
        )
    ]
    .replace("ShortNames", "LongNames")
    .replace("a:", "operand_with_long_name_a:")
    .replace("b:", "operand_with_long_name_b:")
    .replace("c:", "operand_with_long_name_c:")
    .replace("d:", "operand_with_long_name_d:")
    .replace("(a ", "(operand_with_long_name_a ")
    .replace(" b)", " operand_with_long_name_b)")
    .replace("(c ", "(operand_with_long_name_c ")
    .replace(" d)", " operand_with_long_name_d)")
)
ROOTS = (
    "BulkRows",
    "Relabeled",
    "Nested",
    "Shared",
    "Decode",
    "NamedDecode",
    "Collision",
    "SharedRead",
    "Choice",
    "ShortNames",
    "LongNames",
)


@pytest.fixture(scope="module")
def derived_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-derived-names")
    source = root / "derived.py"
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
            "readable_derived",
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
                "readable_derived.derived." + name,
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
    "name", ["BulkRows", "Relabeled", "Nested", "Shared", "Choice"]
)
def test_emitted_anonymous_constructors_do_not_use_opcode_numbers(
    derived_views, name, mode
):
    _, mapping = derived_views[name, mode]
    values = [
        value
        for module in mapping["modules"]
        for value in module["values"]
        if value["opcode"] in ("ac.struct.create", "ac.table.create", "ac.table.splat")
        and value["rtl_expression"]
    ]
    assert values
    assert all(
        not re.fullmatch(r"(?:create|splat)_[0-9]+", value["rtl_expression"])
        for value in values
    )


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
@pytest.mark.parametrize(
    "name,method,state",
    [("BulkRows", "wipe", "bank"), ("Relabeled", "erase_all", "slots")],
)
def test_broadcast_element_name_tracks_real_method_and_storage(
    derived_views, mode, name, method, state
):
    text, _ = derived_views[name, mode]
    assert method + "_" + state + "_element_value" in text
    assert "complete_" not in text and "flush_" not in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_nested_constructor_tracks_the_actual_output_field(derived_views, mode):
    text, _ = derived_views["Nested", mode]
    assert "result_payload_value" in text
    assert "result_value" in text and "payload" in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_original_independent_constructors_are_not_merged_for_names(
    derived_views, mode
):
    text, mapping = derived_views["Shared", mode]
    assert len(re.findall(r"\s\+\s", text)) == 2
    constructors = {
        value["rtl_expression"]
        for module in mapping["modules"]
        for value in module["values"]
        if value["opcode"] == "ac.struct.create" and value["rtl_expression"]
    }
    assert constructors == {"result_0_value", "result_1_value"}


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_membership_is_separate_from_payload_and_keeps_its_source_name(
    derived_views, mode
):
    text, _ = derived_views["Decode", mode]
    assert "inside" in text and "carrier" in text
    assert all(
        "raw == pycircuit_types::Mode_t__" + member in re.sub(r"\s+", " ", text)
        for member in ("IDLE", "RUN", "DONE")
    )


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_authored_decode_bindings_remain_authored(derived_views, mode):
    text, mapping = derived_views["NamedDecode", mode]
    assert "assign decoded = raw;" in text and "assign member =" in text
    assert {"decoded", "member"} <= {row["source_name"] for row in mapping["bindings"]}


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_derived_predicate_cannot_steal_a_later_authored_name(derived_views, mode):
    text, _ = derived_views["Collision", mode]
    assert re.search(r"assign index_in_range\s*=.*first \+ second", text)
    assert re.search(r"assign index_in_range_1\s*=.*\$unsigned\(index\).*<", text)
    assert "index_in_range_1 ?" in text
    assert len(re.findall(r"\s\+\s", text)) == 1


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_original_independent_reads_keep_bounds_predicates_and_unknown_branches(
    derived_views, mode
):
    text, _ = derived_views["SharedRead", mode]
    assert (
        text.count("assign index_in_range =") == 1
        and "assign index_in_range_1 =" in text
    )
    assert "(2)'($unsigned(index)) < (2)'(3)" in text
    assert text.count("values[$unsigned(index)]") == 2 and text.count(": 'x") == 2


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_constructor_names_do_not_force_choice_materialization(derived_views, mode):
    text, _ = derived_views["Choice", mode]
    assert "take ?" in text and "always_comb" not in text
    assert "always_ff" not in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_identifier_length_does_not_choose_wire_or_inline_boundaries(
    derived_views, mode
):
    texts = [derived_views[name, mode][0] for name in ("ShortNames", "LongNames")]
    signatures = [
        {
            "wires": len(re.findall(r"^\s*wire ", text, re.M)),
            "assigns": len(re.findall(r"\bassign\b", text)),
            "plus": len(re.findall(r"\s\+\s", text)),
            "xor": text.count(" ^ "),
            "bit_and": text.count(" & "),
            "bit_or": text.count(" | "),
        }
        for text in texts
    ]
    assert signatures[0] == signatures[1]
    assert signatures[0]["plus"] == 3 and signatures[0]["xor"] == 2


def test_out_of_range_index_source_contract_is_still_rejected(tmp_path):
    source = tmp_path / "bad_index.py"
    source.write_text(
        "import pycircuit as ac\n@ac.module\ndef Bad(values: ac.table[5, ac.u8], index: ac.u3) -> ac.u8:\n    return values[index]\n"
    )
    output = tmp_path / "unit"
    result = _cli(
        "compile",
        "-c",
        str(source),
        "--source-root",
        str(tmp_path),
        "--package-prefix",
        "bad_index",
        "-o",
        str(output),
    )
    assert result.returncode != 0
    assert (
        "table index complete width is not proven in range"
        in result.stdout + result.stderr
    )
    assert not output.exists()


@pytest.fixture(scope="module")
def native_slots(tmp_path_factory):
    # Dedicated native-IR conformance: source Enum decoding requires authored
    # unpack bindings, and TableChoose has no current source authoring spelling.
    root = tmp_path_factory.mktemp("readable-derived-native")
    preamble = ""
    for width in (1, 2, 3, 4, 8):
        preamble += (
            "#w"
            + str(width)
            + ' = #ac.static_expr<{kind = "literal", value = {kind = "integer", value = #ac.math_int<'
            + str(width)
            + '>}, origin = {site = {definition = @top, ast_path = []}, expansion = []}, location = {path = "top.py", line = 1 : i64, column = 1 : i64, end_line = 1 : i64, end_column = 2 : i64}}>\n'
        )
        preamble += "!b" + str(width) + " = !ac.bits<#w" + str(width) + ">\n"
    source = root / "slots.mlir"
    source.write_text(
        preamble
        + """!rows = !ac.table<[#w4], !b8>
!mode = !ac.enum<"Mode">
!cell = !ac.struct<"Cell">
module {
    ac.struct "Cell" fields [{name = "data", type = !b8}, {name = "tag", type = !b3}]
    "ac.enum"() {sym_name = "Mode", width = #ac.math_int<3>, encoding = "explicit", members = [{name = "IDLE", code = #ac.math_int<0>}, {name = "RUN", code = #ac.math_int<3>}]} : () -> ()
    "ac.module"() ({
    ^bb0(%rows: !rows, %raw: !b3, %guard: !b1, %candidate: !b8, %collision: !b4):
        %decoded, %member = "ac.enum.from_bits"(%raw) : (!b3) -> (!mode, !b1)
        %mask = "ac.table.match"(%rows, %candidate) ({
        ^bb0(%entry: !b8, %wanted: !b8):
            %hit = "ac.bits.compare"(%entry, %wanted) {predicate = "eq"} : (!b8, !b8) -> !b1
            "ac.yield"(%hit) : (!b1) -> ()
        }) : (!rows, !b8) -> !b4
        %index0, %index1, %valid0, %valid1 = "ac.table.choose"(%rows, %mask) {count = 2 : i64, policy = "first", order = "low"} : (!rows, !b4) -> (!b2, !b2, !b1, !b1)
        %read, %in_range = "ac.table.get"(%rows, %index0) : (!rows, !b2) -> (!b8, !b1)
        %changed, %enable = "ac.value.merge"(%read, %guard, %candidate) {paths = [[]], operandSegmentSizes = array<i32: 1, 1, 1>} : (!b8, !b1, !b8) -> (!b8, !b1)
        %shared = "ac.struct.create"(%candidate, %raw) : (!b8, !b3) -> !cell
        %shared_roles = "ac.struct.create"(%candidate, %raw) : (!b8, !b3) -> !cell loc(fused<{ac.rtl_role = {role = "write_value", scope = "first", state = "items"}, index = 0 : i64, result = true}>[fused<{ac.rtl_role = {role = "write_value", scope = "second", state = "items"}, index = 0 : i64, result = true}>[unknown]])
        "ac.yield"(%decoded, %member, %index0, %index1, %valid0, %valid1, %changed, %enable, %in_range, %shared, %shared, %collision, %shared_roles, %shared_roles) : (!mode, !b1, !b2, !b2, !b1, !b1, !b8, !b1, !b1, !cell, !cell, !b4, !cell, !cell) -> ()
    }) {sym_name = "top", source_owner = {package = "", path = "top.py"}, parameters = [], type_parameters = [], function_type = (!rows, !b3, !b1, !b8, !b4) -> (!mode, !b1, !b2, !b2, !b1, !b1, !b8, !b1, !b1, !cell, !cell, !b4, !cell, !cell), input_names = ["rows", "raw", "guard", "candidate", "choice_rows_match_mask_choice_0_index_mask"], output_names = ["decoded", "member", "index0", "index1", "valid0", "valid1", "changed", "enable", "in_range", "left", "right", "collision", "write_left", "write_right"]} : () -> ()
    "ac.system"() {entry = {callee = @top, parameters = [], type_arguments = []}, domain = "default"} : () -> ()
}
"""
    )
    views = {}
    for mode in ("physical", "synthesis"):
        command = [
            os.environ["PYCIRCUIT_EMITTER"],
            str(source),
            "--target",
            "verilog",
            "--format",
            "source",
            "--rtl-mode",
            mode,
        ]
        text = _ok(_run(command))
        (root / (mode + ".sv")).write_text(text)
        (root / (mode + ".command.json")).write_text(json.dumps(command))
        views[mode] = text
    return views


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_native_anonymous_auxiliary_slots_keep_distinct_meanings(native_slots, mode):
    text = native_slots[mode]
    assert "raw_is_member" in text and "update_has_write" in text
    assert all(
        "rows_match_mask_choice_" + str(index) + suffix in text
        for index in (0, 1)
        for suffix in ("_index", "_valid")
    )
    assert "rows_match_mask_choice_0_index_in_range" in text
    assert "raw == pycircuit_types::Mode_t__IDLE" in text
    assert "guard ? candidate" in text and "| guard" in text
    assert text.count("assign shared_Cell_value =") == 1
    assert "choice_rows_match_mask_choice_0_index_mask_1 [0:2]" in text
    assert (
        text.count("assign shared_write_value =") == 1
        and "shared_condition" not in text
    )
