"""Static aggregate/layout conformance; no circuit simulation is invoked."""

import json
import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """import pycircuit as ac
@ac.struct
class Payload:
    low: ac.u4
    high: ac.u8
@ac.module
def Projection(packet: Payload) -> Payload:
    @ac.rule
    def transform() -> Payload:
        widened: ac.u8 = packet.low
        return Payload(low=packet.low, high=packet.high + widened)
    return transform
@ac.module
def NamedProjection(packet: Payload) -> tuple[ac.u4, ac.u4]:
    @ac.rule
    def compute() -> tuple[ac.u4, ac.u4]:
        saved = packet.low
        return saved, saved
    return compute
@ac.module
def TableRead() -> tuple[Payload, Payload]:
    entries = ac.table[3, Payload](init=0)
    return entries[0], entries[2]
@ac.module
def SmallIndex(index: ac.u1) -> Payload:
    entries = ac.table[3, Payload](init=0)
    return entries[index]
@ac.module
def WideIndex(index: ac.u2) -> Payload:
    entries = ac.table[4, Payload](init=0)
    return entries[index]
@ac.module
def BranchBindings(take: ac.u1, packet: Payload) -> tuple[ac.u1, Payload]:
    held: Payload = Payload()
    @ac.rule
    def compute() -> tuple[ac.u1, Payload]:
        accepted: ac.u1 = 0
        selected = held
        if take:
            held = packet
            selected = packet
            accepted = 1
        return accepted, selected
    return compute
@ac.module
def LogicRoles(first_payload: ac.u8, second_payload: ac.u8,
               third_payload: ac.u8, fourth_payload: ac.u8) -> ac.u8:
    @ac.rule
    def compute() -> ac.u8:
        return ((first_payload & second_payload) | (third_payload & fourth_payload)) ^ ((first_payload & third_payload) | (second_payload & fourth_payload))
    return compute
@ac.module
def Leaf(value: ac.u8) -> ac.u8:
    return value
@ac.module
def Wrapper(value: ac.u8) -> ac.u8:
    return Leaf(value)
@ac.module
def KeywordBindings(first: ac.u8, second: ac.u8) -> tuple[ac.u8, ac.u8, ac.u8]:
    @ac.rule
    def compute() -> tuple[ac.u8, ac.u8, ac.u8]:
        packed_1 = first - second
        packed = first + second
        wire = packed ^ packed_1
        if first != 0:
            packed = packed + 1
        return packed, packed_1, wire
    return compute
@ac.module
def RecordChoice(take: ac.u1, first: Payload, second: Payload) -> Payload:
    @ac.rule
    def compute() -> Payload:
        selected = first if take else second
        return selected
    return compute
@ac.module
def RecordChoiceMixed(take_low: ac.u1, take_high: ac.u1,
                      first: Payload, second: Payload) -> Payload:
    @ac.rule
    def compute() -> Payload:
        return Payload(low=first.low if take_low else second.low,
                       high=first.high if take_high else second.high)
    return compute
@ac.module
def RecordChoiceShared(take: ac.u1, first: Payload, second: Payload) -> tuple[Payload, ac.u4]:
    @ac.rule
    def compute() -> tuple[Payload, ac.u4]:
        selected_low = first.low if take else second.low
        result = Payload(low=selected_low, high=first.high if take else second.high)
        return result, selected_low
    return compute
"""

BAD_SOURCE = """import pycircuit as ac
@ac.struct
class Payload:
    low: ac.u4
    high: ac.u8
@ac.module
def TableRead(index: ac.u3) -> tuple[Payload, Payload, Payload]:
    entries = ac.table[3, Payload](init=0)
    return entries[0], entries[2], entries[index]
"""


@pytest.fixture(scope="module")
def aggregate_designs(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-aggregate-layout")
    source = root / "aggregate.py"
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
            "readable_aggregate",
            "-o",
            str(unit),
        )
    )
    result = {}
    for name, modes in [
        ("Projection", ("physical", "synthesis")),
        ("NamedProjection", ("physical", "synthesis")),
        ("TableRead", ("managed",)),
        ("SmallIndex", ("managed",)),
        ("WideIndex", ("managed",)),
        ("BranchBindings", ("physical", "synthesis")),
        ("LogicRoles", ("synthesis",)),
        ("Wrapper", ("synthesis",)),
        ("KeywordBindings", ("managed", "physical", "synthesis")),
        ("RecordChoice", ("physical", "synthesis")),
        ("RecordChoiceMixed", ("synthesis",)),
        ("RecordChoiceShared", ("synthesis",)),
    ]:
        final = root / (name + ".ac")
        _ok(
            _cli(
                "link",
                str(unit),
                "--top",
                "readable_aggregate.aggregate." + name,
                "-o",
                str(final),
            )
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
            result[name, mode] = "\n".join(
                path.read_text() for path in (output / "sources").rglob("*.v")
            )
            result[name, mode, "mapping"] = json.loads(
                (output / "rtl-names.json").read_text()
            )
    return result


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_fields_are_direct_and_named_widening_is_retained(aggregate_designs, mode):
    text = aggregate_designs["Projection", mode]
    assert "packet.low" in text and "packet.high" in text
    assert re.search(r"logic \[7:0\] widened;", text)
    assert not re.search(r"assign (?:low|high)_\d+ = packet\.", text)
    assert len(re.findall(r"\s\+\s", text)) == 1


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_named_shared_field_has_one_declaration(aggregate_designs, mode):
    text = aggregate_designs["NamedProjection", mode]
    assert len(re.findall(r"logic \[3:0\] saved;", text)) == 1
    assert len(re.findall(r"assign saved = packet.low;", text)) == 1


def test_constant_packed_slots_keep_first_element_at_msb(aggregate_designs):
    text = aggregate_designs["TableRead", "managed"]
    assert re.search(r"logic\s+\[\(36\)-1:0\]", text)
    assert "[35:24]" in text and "[11:0]" in text
    assert "$clog2(64\x27(3)" not in text


def test_small_index_is_widened_to_represent_the_extent(aggregate_designs):
    text = aggregate_designs["SmallIndex", "managed"]
    assert re.search(r"\(2\)\x27\(\$unsigned\(index\)\) < \(2\)\x27\(3\)", text)


def test_power_of_two_extent_still_needs_an_extra_compare_bit(aggregate_designs):
    text = aggregate_designs["WideIndex", "managed"]
    assert re.search(r"\(3\)\x27\(\$unsigned\(index\)\) < \(3\)\x27\(4\)", text)


def test_unbounded_three_bit_index_into_three_entries_is_rejected(tmp_path):
    source = tmp_path / "unbounded.py"
    source.write_text(BAD_SOURCE)
    output = tmp_path / "unit"
    result = _cli(
        "compile",
        "-c",
        str(source),
        "--source-root",
        str(tmp_path),
        "--package-prefix",
        "unbounded_index",
        "-o",
        str(output),
    )
    assert result.returncode != 0
    assert (
        "table index complete width is not proven in range"
        in result.stdout + result.stderr
    )
    assert not output.exists()


def test_anonymous_child_uses_callee_identity_in_rtl(aggregate_designs):
    text = aggregate_designs["Wrapper", "synthesis"]
    assert re.search(r"Leaf\s+Leaf_inst_0\s*\(", text)
    assert "pyc_5f5f7079635f63616c6c" not in text


def test_generated_operation_names_do_not_escape_verilog_keywords(aggregate_designs):
    text = aggregate_designs["LogicRoles", "synthesis"]
    assert re.search(r"^\s*wire logic \[7:0\] [A-Za-z_][A-Za-z_0-9]*;", text, re.M)
    assert text.count(" & ") == 4 and text.count(" | ") == 2 and text.count(" ^ ") == 1
    assert not re.search(r"\bpyc_[0-9a-f]+_\d+\b", text)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_branch_bindings_do_not_name_derived_record_or_mask_values(
    aggregate_designs, mode
):
    mapping = aggregate_designs["BranchBindings", mode, "mapping"]["bindings"]
    accepted = [row for row in mapping if row["source_name"] == "accepted"]
    selected = [row for row in mapping if row["source_name"] == "selected"]
    assert accepted and selected
    assert len({row["optimized_value"] for row in accepted}) <= 3
    for row in accepted:
        assert row["type"].startswith("!ac.bits<")
        assert re.findall(r"#ac.math_int<([^>]+)>", row["type"]) == ["1"]
    assert all(row["type"].endswith('.Payload">') for row in selected)


@pytest.mark.parametrize("mode", ["managed", "physical", "synthesis"])
def test_keywords_keep_source_spelling_and_collision_identity(aggregate_designs, mode):
    text = aggregate_designs["KeywordBindings", mode]
    mapping = aggregate_designs["KeywordBindings", mode, "mapping"]["bindings"]
    # Managed retains symbolic-width formatting; the payload is eight bits in
    # all three modes. Test identity/escaping without imposing physical style.
    width = r"logic \[(?:7|\(8\)-1):0\] "
    assert re.search(width + r"\\packed\s+;", text)
    assert re.search(width + r"\\wire\s+;", text)
    assert re.search(width + r"packed_1(?:_\d+)?;", text)
    assert "pyc_7061636b6564" not in text
    assert "pyc_77697265" not in text
    names = {
        row["optimized_value"]: row["rtl_expression"]
        for row in mapping
        if row["source_name"] in ("packed", "packed_1", "wire")
    }
    logical = [
        name[1:-1] if name.startswith("\\") and name.endswith(" ") else name
        for name in names.values()
    ]
    assert len(logical) == len(set(logical))
    assert {"packed", "wire"} <= set(logical)
    assert any(name.startswith("packed_1") for name in logical)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_record_choice_is_one_typed_conditional(aggregate_designs, mode):
    text = aggregate_designs["RecordChoice", mode]
    assert re.search(r"assign selected = take \? first : second;", text)
    assert not re.search(r"\? first\.(?:low|high)", text)


def test_distinct_field_conditions_do_not_become_one_record_choice(aggregate_designs):
    text = aggregate_designs["RecordChoiceMixed", "synthesis"]
    assert "take_low" in text and "take_high" in text
    assert not re.search(r"\? first : second", text)


def test_named_shared_field_selector_remains_one_wire(aggregate_designs):
    text = aggregate_designs["RecordChoiceShared", "synthesis"]
    assert len(re.findall(r"logic \[3:0\] selected_low;", text)) == 1
    assert len(re.findall(r"assign selected_low = ", text)) == 1
    assert re.search(r"assign result(?:_\d+)? = \{selected_low,", text)
