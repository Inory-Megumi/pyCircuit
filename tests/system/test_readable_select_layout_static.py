"""Single-use select layout, retained sharing and width boundaries; no simulation."""

import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """import pycircuit as ac
@ac.module
def Chain(a: ac.u1, b: ac.u1, c: ac.u1, first: ac.u8, second: ac.u8,
          third: ac.u8, fallback: ac.u8) -> ac.u8:
    return first if a else (second if b else (third if c else fallback))
@ac.module
def BothArms(a: ac.u1, b: ac.u1, c: ac.u1, first: ac.u8, second: ac.u8,
             third: ac.u8, fallback: ac.u8) -> ac.u8:
    return (first if b else second) if a else (third if c else fallback)
@ac.module
def Shared(a: ac.u1, first: ac.u8, second: ac.u8) -> tuple[ac.u8, ac.u8]:
    chosen = first if a else second
    return chosen, chosen + 1
@ac.module
def Narrow(a: ac.u1, first: ac.u3, second: ac.u3) -> ac.u8:
    @ac.rule
    def compute() -> ac.u8:
        chosen: ac.u3 = (first + second) if a else first
        wide: ac.u8 = chosen
        return wide
    return compute
@ac.module
def MixedWidth(a: ac.u1, first: ac.u4, second: ac.u4, other: ac.u8) -> ac.u8:
    @ac.rule
    def compute() -> ac.u8:
        wrapped: ac.u4 = first + second
        widened: ac.u8 = wrapped
        return widened if a else other
    return compute
"""

deep = "data"
for index in range(40):
    deep = "(" + str(index) + " if flags[" + str(index) + "] else " + deep + ")"
SOURCE += (
    "@ac.module\ndef Deep(flags: ac.table[40, ac.u1], data: ac.u8) -> ac.u8:\n"
    "    return " + deep + "\n"
)
ROOTS = ("Chain", "BothArms", "Shared", "Narrow", "MixedWidth", "Deep")


@pytest.fixture(scope="module")
def select_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-select-layout")
    source = root / "selects.py"
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
            "readable_select",
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
                "readable_select.selects." + name,
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
            views[name, mode] = "\n".join(
                path.read_text() for path in (output / "sources").rglob("*.v")
            )
    return views


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_chain_prints_one_typed_tree_without_anonymous_cuts(select_views, mode):
    text = select_views["Chain", mode]
    assert text.count("?") == 3
    assert re.search(r"8'\(\n", text)
    assert not re.search(r"\bselect_[0-9]+\b|always_comb|\bcase[zx]?\b", text)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_both_arms_retain_the_original_three_ternaries(select_views, mode):
    text = select_views["BothArms", mode]
    assert text.count("?") == 3
    compact = re.sub(r"\s+", " ", text)
    assert "b ? first : second" in compact and "c ? third : fallback" in compact
    assert not re.search(r"\bselect_[0-9]+\b|always_comb", text)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_shared_source_choice_remains_one_named_wire(select_views, mode):
    text = select_views["Shared", mode]
    assert text.count("?") == 1 and len(re.findall(r"\s\+\s", text)) == 1
    assert "logic [7:0] chosen;" in text
    assert "assign result_0 = chosen;" in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_narrow_choice_and_arithmetic_still_wrap_before_widening(select_views, mode):
    text = select_views["Narrow", mode]
    assert "logic [2:0] chosen;" in text and "logic [7:0] wide;" in text
    assert len(re.findall(r"\s\+\s", text)) == 1 and "$unsigned(chosen)" in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_mixed_width_arm_keeps_its_resize_and_arithmetic_boundary(select_views, mode):
    text = select_views["MixedWidth", mode]
    assert "logic [3:0] wrapped;" in text and "logic [7:0] widened;" in text
    assert len(re.findall(r"\s\+\s", text)) == 1 and "$unsigned(wrapped)" in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_layout_bound_emits_wire_boundaries_instead_of_unbounded_expansion(
    select_views, mode
):
    text = select_views["Deep", mode]
    assignments = re.findall(r"assign\s+\S+\s*=\s*(.*?);", text, re.S)
    assert sum(item.count("?") for item in assignments) == 40
    assert max(item.count("?") for item in assignments) <= 32
    assert "selected_value" in text
