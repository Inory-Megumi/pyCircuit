"""Declaration placement, functional sections and original scope; static only."""

import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """import pycircuit as ac
from enum import Enum
@ac.struct
class Item:
    data: ac.u8
    tag: ac.u3
@ac.encoding(width=2)
class Mode(Enum):
    IDLE = 0
    RUN = 2
@ac.module
def Stages(enable: ac.u1, send: ac.u1, done: ac.u1, step: ac.u8) -> tuple[ac.u8, ac.u8]:
    first: ac.u8 = 0
    second: ac.u8 = 0
    @ac.method
    def advance() -> None:
        if send:
            first = first + step
    @ac.method
    def consume() -> None:
        if done:
            second = second - 1
    @ac.rule(guard=lambda: enable)
    def transact() -> None:
        advance()
        consume()
    return first, second
@ac.module
def Routed(index: ac.u2, incoming: Item, enable: ac.u1, clear: ac.u1) -> Item:
    entries = ac.table[4, Item](init=0)
    @ac.method
    def install() -> None:
        entries[index] = incoming
    @ac.method
    def erase() -> None:
        if clear:
            entries[index] = Item()
    @ac.rule(guard=lambda: enable)
    def transact() -> None:
        install()
        erase()
    return entries[index]
@ac.module
def Maps(values: ac.table[4, ac.u8]) -> ac.table[4, ac.u8]:
    return values.map(lambda item: item + 1).map(lambda item: item ^ 3)
@ac.module
def State(start: ac.u1, finish: ac.u1) -> Mode:
    current: Mode = Mode.IDLE
    @ac.rule
    def advance() -> None:
        if current == Mode.IDLE:
            if start:
                current = Mode.RUN
        elif finish:
            current = Mode.IDLE
    return current
"""

ROOTS = ("Stages", "Routed", "Maps", "State")


@pytest.fixture(scope="module")
def section_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-sections")
    source = root / "sections.py"
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
            "readable_sections",
            "-o",
            str(unit),
        )
    )
    result = {}
    for name in ROOTS:
        final, output = root / (name + ".ac"), root / (name + "-synthesis")
        _ok(
            _cli(
                "link",
                str(unit),
                "--top",
                "readable_sections.sections." + name,
                "-o",
                str(final),
            )
        )
        _ok(
            _cli(
                "emit",
                str(final),
                "--target",
                "verilog",
                "--rtl-mode",
                "synthesis",
                "-o",
                str(output),
            )
        )
        result[name] = "\n".join(
            path.read_text() for path in (output / "sources").rglob("*.v")
        )
    return result


@pytest.mark.parametrize("name", ROOTS)
def test_module_signals_precede_logic_and_outputs_have_their_own_section(
    section_views, name
):
    text = section_views[name]
    assert text.index("// Signals") < text.index("assign ")
    assert "// Output connections." in text
    assert text.rindex("// Output connections.") < text.rindex("assign result")


@pytest.mark.parametrize("name", ["Stages", "Routed", "State"])
def test_persistent_state_is_declared_separately_from_signals(section_views, name):
    text = section_views[name]
    assert text.index("// State registers") < text.index("// Signals")
    assert "// State update:" in text
    assert text.count("always_ff") == (2 if name == "Stages" else 1)


def test_lane_signals_stay_inside_the_original_generate_scope(section_views):
    text = section_views["Routed"]
    assert text.count("for (genvar") == 1
    start = text.index("begin : entries_update")
    body = text[start:]
    first_assignment = body.index("assign ")
    for match in re.finditer(r"^\s*wire\b", body, re.M):
        assert match.start() < first_assignment
    assert text.index("// Source method: install.", start) < text.index(
        "// Source method: erase.", start
    )
    assert text.index("// Source method: erase.", start) < text.index(
        "// Register update.", start
    )
    assert "entries[entries_lane] <=" in body


def test_inlined_methods_keep_call_order_and_separate_state_sections(section_views):
    text = section_views["Stages"]
    assert text.index("//   transact -> advance") < text.index(
        "//   transact -> consume"
    )
    assert text.index("// State update: first.") < text.index(
        "// State update: second."
    )
    assert len(re.findall(r"\s\+\s", text)) == len(re.findall(r"\s-\s", text)) == 1


def test_net_initializers_are_continuous_assignments_not_variable_initialization(
    section_views,
):
    text = section_views["Stages"]
    assert "enable_active" in text and "assign enable_active =" in text
    assert not any(
        " = " in line for line in text.splitlines() if line.strip().startswith("wire ")
    )


@pytest.mark.parametrize("name", ROOTS)
def test_sections_add_no_simulation_scaffolding(section_views, name):
    assert not re.search(r"\binitial\b|__checks|pyc_phase", section_views[name])
