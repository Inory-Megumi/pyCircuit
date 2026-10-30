"""Typed Enum readability conformance; compile/emit only, no circuit execution."""

import json
import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """from enum import Enum, auto
import pycircuit as ac
@ac.encoding(width=3)
class Color(Enum):
    RED = 0
    GREEN = 3
    BLUE = 5
@ac.encoding(width=1)
class Flag(Enum):
    OFF = 0
    ON = 1
@ac.encoding(width=72)
class Wide(Enum):
    ZERO = 0
    BIG = 2361183241434822606848
@ac.encoding(width=3, kind="binary_one_hot")
class Hot(Enum):
    A = auto()
    B = auto()
    C = auto()
@ac.encoding(width=2, kind="gray_sequential")
class Gray(Enum):
    A = auto()
    B = auto()
    C = auto()
@ac.struct
class Packet:
    color: Color
    tag: ac.u4
@ac.module
def SparseMachine(start: ac.u1, finish: ac.u1, ack: ac.u1) -> Color:
    current: Color = Color.RED
    @ac.rule
    def advance() -> None:
        if current == Color.RED:
            if start:
                current = Color.GREEN
        elif current == Color.GREEN:
            if finish:
                current = Color.BLUE
        elif current == Color.BLUE:
            if ack:
                current = Color.RED
    return current
@ac.module
def Choice(take: ac.u1, first: Color, second: Color) -> Color:
    return first if take else second
@ac.module
def TinyChoice(take: ac.u1, first: Flag, second: Flag) -> Flag:
    return first if take else second
@ac.module
def WideChoice(take: ac.u1, first: Wide, second: Wide) -> Wide:
    return first if take else second
@ac.module
def HotChoice(take: ac.u1, value: Hot) -> Hot:
    return Hot.C if take else value
@ac.module
def GrayChoice(take: ac.u1, value: Gray) -> Gray:
    return Gray.C if take else value
@ac.module
def Decode(raw: ac.u3) -> tuple[Color, bool]:
    decoded, member = ac.enum_from_bits[Color](raw)
    return decoded, member
@ac.module
def RoundTrip(raw: ac.u3) -> tuple[ac.u3, bool]:
    decoded, member = ac.enum_from_bits[Color](raw)
    encoded = ac.enum_to_bits(decoded)
    return encoded, member
@ac.module
def SharedDecode(first: ac.u3, second: ac.u3) -> tuple[Color, bool, ac.u3]:
    common = first + second
    decoded, member = ac.enum_from_bits[Color](common)
    return decoded, member, common
@ac.module
def Widen(first: ac.u3, second: ac.u3) -> ac.u8:
    @ac.rule
    def compute() -> ac.u8:
        narrow: ac.u3 = first + second
        decoded, unused = ac.enum_from_bits[Color](narrow)
        encoded = ac.enum_to_bits(decoded)
        wide: ac.u8 = encoded
        return wide
    return compute
@ac.module
def PayloadChoice(take: ac.u1, first: Packet, second: Packet) -> Packet:
    return Packet(color=first.color if take else second.color, tag=first.tag)
@ac.module
def TableRead(index: ac.u1, entries: ac.table[2, Color]) -> Color:
    return entries[index]
@ac.module
def IgnoreMembership(raw: ac.u3) -> Color:
    decoded, unused = ac.enum_from_bits[Color](raw)
    return decoded
"""

ROOTS = (
    "SparseMachine",
    "Choice",
    "TinyChoice",
    "WideChoice",
    "HotChoice",
    "GrayChoice",
    "Decode",
    "RoundTrip",
    "SharedDecode",
    "Widen",
    "PayloadChoice",
    "TableRead",
    "IgnoreMembership",
)


@pytest.fixture(scope="module")
def enum_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-enums")
    source = root / "enums.py"
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
            "readable_enums",
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
                "readable_enums.enums." + name,
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
            views[name, mode] = (
                text,
                json.loads((output / "rtl-names.json").read_text()),
                output,
            )
    return views


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
@pytest.mark.parametrize("name", ROOTS)
def test_enum_representation_does_not_materialize_opcode_wires(enum_views, name, mode):
    text, mapping, _ = enum_views[name, mode]
    assert not re.search(r"\b(?:to_bits|from_bits)_[0-9]+\b", text)
    # Struct creation is a different operation even though its fallback also
    # starts with create_. Check typed nodes rather than banning that spelling.
    for module in mapping["modules"]:
        for value in module["values"]:
            if value["opcode"] in (
                "ac.enum.create",
                "ac.enum.to_bits",
                "ac.enum.from_bits",
            ):
                assert not re.fullmatch(
                    r"(?:to_bits|from_bits|create)_[0-9]+",
                    value["rtl_expression"] or "",
                )


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_sparse_machine_keeps_encoding_state_and_enable(enum_views, mode):
    text, _, output = enum_views["SparseMachine", mode]
    types = (output / "design_top.sv").read_text()
    assert "Color_t__GREEN = 3'd3" in types and "Color_t__BLUE = 3'd5" in types
    assert "Color_t current;" in text and text.count("always_ff") == 1
    assert (
        "current_is_RED" in text
        and "current_is_GREEN" in text
        and "current_is_BLUE" in text
    )
    assert "else if (" in text and "current <=" in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
@pytest.mark.parametrize(
    "name", ["Choice", "TinyChoice", "WideChoice", "PayloadChoice"]
)
def test_unknown_selector_keeps_original_four_state_ternary(enum_views, name, mode):
    text, _, _ = enum_views[name, mode]
    assert "take ?" in text
    assert "always_comb" not in text and not re.search(r"\bcase[zx]?\b", text)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_membership_keeps_sparse_four_state_equality_separate_from_data(
    enum_views, mode
):
    text, _, _ = enum_views["Decode", mode]
    assert "Color_t decoded;" in text and "assign decoded = raw;" in text
    assert all(
        "raw == pycircuit_types::Color_t__" + member in re.sub(r"\s+", " ", text)
        for member in ("RED", "GREEN", "BLUE")
    )
    assert "member" in text and " | " in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_shared_decode_does_not_duplicate_arithmetic_or_erase_aliases(enum_views, mode):
    text, mapping, _ = enum_views["SharedDecode", mode]
    assert len(re.findall(r"\s\+\s", text)) == 1
    assert "logic [2:0] common;" in text
    assert {row["source_name"] for row in mapping["bindings"]} >= {
        "common",
        "decoded",
        "member",
    }


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_encoding_conversion_does_not_widen_narrow_arithmetic(enum_views, mode):
    text, _, _ = enum_views["Widen", mode]
    assert len(re.findall(r"\s\+\s", text)) == 1
    assert "logic [2:0] narrow;" in text and "logic [7:0] wide;" in text
    assert "$unsigned(encoded)" in text


def test_ignored_membership_does_not_add_a_guard_or_reject_invalid_carriers(enum_views):
    text, _, _ = enum_views["IgnoreMembership", "synthesis"]
    assert "assign decoded = raw;" in text
    assert not re.search(r"\bif\b|\balways\w*\b|\$error|__checks|Color_t__", text)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_derived_encoding_codes_are_not_renumbered(enum_views, mode):
    for name, symbol, code in [
        ("HotChoice", "Hot_t__C", "3'd4"),
        ("GrayChoice", "Gray_t__C", "2'd3"),
    ]:
        text, _, output = enum_views[name, mode]
        assert (
            symbol in text
            and (symbol + " = " + code) in (output / "design_top.sv").read_text()
        )
