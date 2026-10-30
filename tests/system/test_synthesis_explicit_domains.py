"""Direct-primitive conformance only; ordinary sources do not expose pins."""

import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """import pycircuit as ac
from pycircuit import dff
@ac.struct
class Domain:
    clock: ac.u1
    reset: ac.u1
@ac.module
def Lane(domain: Domain) -> ac.u8:
    cell = dff(T=ac.u8)
    cell(clk=domain.clock, rst=domain.reset, d=cell.q + 1, init=0)
    return cell.q
@ac.module
def TwoDomains(first: Domain, second: Domain) -> tuple[ac.u8, ac.u8]:
    return Lane(first), Lane(second)
@ac.module
def ComputedClock(clock: ac.u1, reset: ac.u1, enable: ac.u1) -> ac.u1:
    cell = dff(T=ac.u1)
    cell(clk=clock & enable, rst=reset, d=1, init=0)
    return cell.q
@ac.module
def ClockData(clock: ac.u1, reset: ac.u1) -> ac.u1:
    cell = dff(T=ac.u1)
    cell(clk=clock, rst=reset, d=clock, init=0)
    return cell.q
@ac.module
def SameClockReset(clock: ac.u1) -> ac.u1:
    cell = dff(T=ac.u1)
    cell(clk=clock, rst=clock, d=1, init=0)
    return cell.q
@ac.module
def ExportClockRecord(clock: ac.u1, reset: ac.u1) -> tuple[ac.u1, Domain]:
    cell = dff(T=ac.u1)
    cell(clk=clock, rst=reset, d=1, init=0)
    return cell.q, Domain(clock=clock, reset=reset)
"""


@pytest.fixture(scope="module")
def explicit_units(tmp_path_factory):
    root = tmp_path_factory.mktemp("synthesis-explicit-domains")
    source = root / "domains.py"
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
            "explicit_domains",
            "-o",
            str(unit),
        )
    )
    return root, unit


def test_two_independent_explicit_domains_export_without_a_fake_root_clock(
    explicit_units,
):
    root, unit = explicit_units
    final, output = root / "good.ac", root / "good"
    _ok(
        _cli(
            "link",
            str(unit),
            "--top",
            "explicit_domains.domains.TwoDomains",
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
    text = "\n".join(path.read_text() for path in (output / "sources").rglob("*.v"))
    assert "posedge domain.clock" in text
    assert not re.search(r"\binitial\b|__checks|pyc_phase", text)


@pytest.mark.parametrize(
    "name,diagnostic",
    [
        ("ComputedClock", "actual root clock/reset pair"),
        ("ClockData", "clock use as data"),
        ("SameClockReset", "actual root clock/reset pair"),
        ("ExportClockRecord", "clock use as data"),
    ],
)
def test_explicit_domains_keep_identity_and_data_use_rejections(
    explicit_units, name, diagnostic
):
    root, unit = explicit_units
    final, output = root / (name + ".ac"), root / name
    _ok(
        _cli(
            "link",
            str(unit),
            "--top",
            "explicit_domains.domains." + name,
            "-o",
            str(final),
        )
    )
    result = _cli(
        "emit",
        str(final),
        "--target",
        "verilog",
        "--rtl-mode",
        "synthesis",
        "-o",
        str(output),
    )
    assert result.returncode != 0
    assert diagnostic in result.stdout + result.stderr
    assert not output.exists()
