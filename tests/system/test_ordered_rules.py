"""Ordered autonomous roots retain separate commit decisions and state versions."""

from __future__ import annotations

import json
import shutil
import textwrap

import pytest
from test_source_system_execution import _bundle, _cli, _compile, _ok, _records, _run

pytestmark = pytest.mark.system


@pytest.mark.parametrize(
    ("order", "second_decorator", "expected"),
    [
        ("first, second", "@ac.rule", 8),
        ("second, first", "@ac.rule", 7),
        ("first, second", "@ac.rule(guard=lambda: count == 4)", 8),
        ("first, second", "@ac.rule(guard=lambda: count == 3)", 4),
    ],
    ids=["add-double", "double-add", "guard-sees-forwarded", "guard-rejects-old-q"],
)
def test_ordered_state_and_guard(tmp_path, order, second_decorator, expected):
    _exercise(
        tmp_path,
        f"""    @ac.rule
    def first() -> None:
        count = count + 1

    {second_decorator}
    def second() -> None:
        count = count * 2

    ac.schedule({order})
""",
        [3, expected],
    )


@pytest.mark.parametrize("blocked", ["first", "second"])
@pytest.mark.parametrize("blocker", ["method", "queue"])
def test_failed_root_keeps_other_root_commit(tmp_path, blocked, blocker):
    prelude = (
        "    @ac.method(guard=lambda allow: allow)\n"
        "    def require(allow: ac.u1) -> None:\n"
        "        pass\n"
        if blocker == "method"
        else "    tokens = ac.queue[ac.u8](depth=1, latency=1)\n"
    )
    deny = "        require(0)\n" if blocker == "method" else "        tokens.pop()\n"
    body = (
        prelude
        + "    @ac.rule\n    def first() -> None:\n        count = count + 1\n"
        + (deny if blocked == "first" else "")
        + "    @ac.rule\n    def second() -> None:\n        count = count * 2\n"
        + (deny if blocked == "second" else "")
        + "    ac.schedule(first, second)\n"
    )
    # A failed Method or empty Queue rolls back its whole root, including the
    # earlier write. The other root remains eligible and commits independently.
    _exercise(tmp_path, body, [3, 6, 12] if blocked == "first" else [3, 4, 5])


@pytest.mark.parametrize("middle_writes", [True, False])
def test_three_rule_chain_forwards_through_middle_root(tmp_path, middle_writes):
    middle = "count = count * 2" if middle_writes else "pass"
    body = f"""    @ac.rule
    def first() -> None:
        count = count + 1

    @ac.rule
    def middle() -> None:
        {middle}

    @ac.rule
    def last() -> None:
        count = count - 3

    ac.schedule(first, middle, last)
"""
    _exercise(tmp_path, body, [3, 5, 9] if middle_writes else [3, 1, 255])


def test_disabled_first_root_does_not_disable_successor(tmp_path):
    body = textwrap.indent(
        textwrap.dedent(
            """\
            @ac.rule(guard=lambda: count == 0)
            def first() -> None:
                count = count + 1

            @ac.rule
            def second() -> None:
                count = count * 2

            ac.schedule(first, second)
            """
        ),
        "    ",
    )
    _exercise(tmp_path, body, [3, 6, 12])


def test_forwarding_preserves_unknown_and_high_impedance_data(tmp_path):
    body = """    @ac.rule
    def first() -> None:
        count = ac.four_state("101010xz")

    @ac.rule
    def second() -> None:
        count = count

    ac.schedule(first, second)
"""
    encoded = {"kind": "bits4", "width": 8, "value": "a8", "known": "fc", "z": "01"}
    _exercise(tmp_path, body, [3, encoded, encoded])


@pytest.mark.parametrize(
    ("order", "diagnostic"),
    [
        ("first, second, first", "repeat a Rule"),
        ("first, missing", "autonomous Rule names"),
        ("first, first.other", "autonomous Rule names"),
    ],
    ids=["repeated-rule", "unknown-rule", "cross-instance"],
)
def test_invalid_order_preserves_existing_publication(tmp_path, order, diagnostic):
    source = tmp_path / "source"
    source.mkdir()
    path = source / "invalid.py"
    path.write_text(
        "import pycircuit as ac\n@ac.module\ndef Counter() -> ac.u8:\n    return 3\n"
    )
    unit = tmp_path / "unit"
    _ok(_compile(source, "invalid.py", unit))
    original = {
        p.relative_to(unit): p.read_bytes() for p in unit.rglob("*") if p.is_file()
    }
    path.write_text(
        f"""import pycircuit as ac
@ac.module
def Counter() -> ac.u8:
    count: ac.u8 = 3
    @ac.rule
    def first() -> None:
        count = count + 1
    @ac.rule
    def second() -> None:
        count = count * 2
    ac.schedule({order})
    return count
"""
    )
    result = _cli(
        "compile",
        "-c",
        str(path),
        "--source-root",
        str(source),
        "--package-prefix",
        "checks",
        "-o",
        str(unit),
        "--replace",
    )
    assert result.returncode != 0
    assert diagnostic in result.stderr, result.stderr
    assert {
        p.relative_to(unit): p.read_bytes() for p in unit.rglob("*") if p.is_file()
    } == original


def test_omitted_rule_still_runs_and_reads_committed_state(tmp_path):
    body = """    saved: ac.u8 = 0

    @ac.rule
    def first() -> None:
        count = count + 1

    @ac.rule
    def second() -> None:
        count = count * 2

    @ac.rule
    def remember() -> None:
        saved = count

    ac.schedule(first, second)
"""
    # Unlisted remember still fires, but sees 3 then 8 rather than 8 then 18.
    _exercise(tmp_path, body, [3, 11, 26], result="count + saved")


def _exercise(tmp_path, body, expected, *, result="count"):
    source = tmp_path / "source"
    source.mkdir()
    (source / "ordered.py").write_text(
        f"""import pycircuit as ac

@ac.module
def Counter() -> ac.u8:
    count: ac.u8 = 3

{body}
    return {result}

@ac.system
def Exercise():
    value = Counter()

    @ac.rule
    def observe() -> None:
        ac.log("info", "ordered count", value)
"""
    )
    unit = tmp_path / "unit"
    _ok(_compile(source, "ordered.py", unit))
    final = tmp_path / "ordered.ac"
    _ok(_cli("link", str(unit), "--top", "checks.ordered.Exercise", "-o", str(final)))
    _check_final(final, tmp_path, expected)


def test_order_survives_header_only_import_and_saved_anchor(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    provider_source = source / "counter.py"
    provider_source.write_text(
        """import pycircuit as ac
from pycircuit import schedule as run_rules
@ac.module
def Counter(delta: ac.u8) -> ac.u8:
    count: ac.u8 = 3
    @ac.rule
    def first() -> None:
        count = count + delta
    @ac.rule
    def second() -> None:
        count = count * 2
    run_rules(first, second)
    return count
"""
    )
    (source / "bench.py").write_text(
        """import pycircuit as ac
from checks.counter import Counter
@ac.system
def Exercise():
    left = Counter(1)
    right = Counter(2)
    @ac.rule
    def observe() -> None:
        ac.log("info", "ordered instances", left + right)
"""
    )
    provider, consumer = tmp_path / "provider", tmp_path / "consumer"
    _ok(_compile(source, "counter.py", provider))
    receipt = json.loads((provider / "unit.json").read_text())
    body = provider / receipt["files"]["body"]
    hidden = tmp_path / "hidden-provider.ac"
    provider_source.unlink()
    body.rename(hidden)
    try:
        _ok(_compile(source, "bench.py", consumer, [provider]))
    finally:
        hidden.rename(body)
    anchor = tmp_path / "anchor"
    _ok(
        _cli(
            "link",
            str(provider),
            str(consumer),
            "--top",
            "checks.bench.Exercise",
            "--target",
            "anchor",
            "-o",
            str(anchor),
        )
    )
    for directory in (source, provider, consumer):
        shutil.rmtree(directory)
    final = tmp_path / "reloaded.ac"
    _ok(
        _cli(
            "link", "--from-anchor", str(anchor), "--target", "final", "-o", str(final)
        )
    )
    _check_final(final, tmp_path, [6, 18, 42])


def _check_final(final, tmp_path, expected):
    original = final.read_bytes()
    transcripts = []
    for target in ("cpp", "verilog"):
        destination = tmp_path / target
        destination.mkdir()
        binary = _bundle(final, destination, target)
        for workers in (1, 2) if target == "cpp" else (1,):
            arguments = (
                ["--cycles", str(len(expected)), "--workers", str(workers)]
                if target == "cpp"
                else [f"+cycles={len(expected)}"]
            )
            rows = _records(_ok(_run([str(binary), *arguments], timeout=30)))
            logs = [row for row in rows if row["kind"] == "log"]
            values = [
                (
                    int(row["values"][0]["value"])
                    if row["values"][0]["kind"] == "integer"
                    else row["values"][0]
                )
                for row in logs
            ]
            assert values == [value for value in expected for _ in range(2)]
            transcripts.append([row for row in rows if row["kind"] != "result"])
    assert transcripts[0] == transcripts[1] == transcripts[2]
    assert final.read_bytes() == original
