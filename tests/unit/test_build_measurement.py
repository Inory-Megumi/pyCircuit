"""Guard the numeric shape of real build reliability measurement helpers without thresholds."""

from __future__ import annotations

import importlib.util
import json
import math
import os
import sys
from collections import Counter
from pathlib import Path

import pytest

pytestmark = pytest.mark.unit
ROOT = Path(__file__).resolve().parents[2]
MEASUREMENT_TOOL = ROOT / "tools/measure_source_build.py"


def _measurement_tool():
    spec = importlib.util.spec_from_file_location(
        "measurement_build_measurement", MEASUREMENT_TOOL
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(
            f"cannot load build reliability measurement helper: {MEASUREMENT_TOOL}"
        )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _assert_nonnegative_number(value: object) -> None:
    assert type(value) in {int, float}
    assert math.isfinite(value)
    assert value >= 0


def test_phase_measurements_report_nonnegative_numeric_values(
    tmp_path: Path,
) -> None:
    tool = _measurement_tool()
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()
    before = tool._artifacts(artifacts)
    result = tool._run(
        [
            sys.executable,
            "-c",
            "from pathlib import Path; import sys; Path(sys.argv[1]).write_bytes(b'probe')",
            str(artifacts / "probe.bin"),
        ],
        cwd=tmp_path,
        env=os.environ.copy(),
    )
    after = tool._artifacts(artifacts)
    phase = tool._phase("numeric_probe", result, before, after, tmp_path / "logs")

    for key in (
        "wall_seconds",
        "exit_status",
        "artifact_bytes_before",
        "artifact_bytes_after",
    ):
        _assert_nonnegative_number(phase[key])
    assert phase["exit_status"] == 0
    assert phase["artifact_bytes_before"] == 0
    assert phase["artifact_bytes_after"] == len(b"probe")
    assert phase["executed_command_counts"] == {}
    assert phase["executed_command_counts"] == dict(
        Counter(command["kind"] for command in phase["executed_commands"])
    )

    for artifact in after:
        _assert_nonnegative_number(artifact["size_bytes"])
        _assert_nonnegative_number(artifact["mtime_ns"])
    assert phase["artifact_changes"] == [
        {
            "path": "probe.bin",
            "kind": "created",
            "bytes_before": None,
            "bytes_after": len(b"probe"),
            "mtime_changed": True,
            "content_changed": True,
        }
    ]
    for change in phase["artifact_changes"]:
        for key in ("bytes_before", "bytes_after"):
            if change[key] is not None:
                _assert_nonnegative_number(change[key])


def test_failed_phase_preserves_diagnostics_and_measurements(tmp_path: Path) -> None:
    tool = _measurement_tool()
    result = tool._run(
        [
            sys.executable,
            "-c",
            "import sys; sys.stderr.write('link failed'); sys.exit(3)",
        ],
        cwd=tmp_path,
        env=os.environ.copy(),
    )
    with pytest.raises(RuntimeError, match="link failed"):
        tool._phase("compile_link", result, [], [], tmp_path)
    assert (tmp_path / "compile_link.stderr.txt").read_text() == "link failed"
    receipt = json.loads((tmp_path / "compile_link.measurement.json").read_text())
    assert receipt["exit_status"] == 3
    assert receipt["timed_out"] is False
    _assert_nonnegative_number(receipt["wall_seconds"])
    assert receipt["rss"]["unit"] == "KiB"


def test_prefixed_cpp_compiler_is_counted_as_module_compilation() -> None:
    tool = _measurement_tool()
    commands = tool._executed_commands(
        "[1/2] /deps/bin/x86_64-conda-linux-gnu-c++ -O3 "
        "-o CMakeFiles/pycircuit_modules.dir/sources/leaf.cpp.o "
        "-c /generated/sources/leaf.cpp"
    )
    assert len(commands) == 1
    assert commands[0]["kind"] == "cpp_module_target_compile"
    assert commands[0]["source"] == "/generated/sources/leaf.cpp"
