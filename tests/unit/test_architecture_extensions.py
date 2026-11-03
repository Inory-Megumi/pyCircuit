"""Retirement of the expansion command and its SDK packaging boundary."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import sys
from pathlib import Path

import pytest
from pycircuit.cli import main

ROOT = Path(__file__).resolve().parents[2]
pytestmark = pytest.mark.unit


def test_elaborate_is_not_a_compiler_command(tmp_path: Path) -> None:
    source = tmp_path / "author.py"
    output = tmp_path / "expanded.py"
    source.write_text("# author source\n", encoding="ascii")
    output.write_text("# preserved output\n", encoding="ascii")
    with contextlib.redirect_stderr(io.StringIO()):
        with pytest.raises(SystemExit) as failure:
            main(["elaborate", str(source), "-o", str(output), "--replace"])
    assert failure.value.code == 2
    assert source.read_text() == "# author source\n"
    assert output.read_text() == "# preserved output\n"


def test_wheel_stages_only_the_native_installed_package(tmp_path: Path) -> None:
    sys.path.insert(0, str(ROOT / "packaging/wheel"))
    try:
        spec = importlib.util.spec_from_file_location(
            "architecture_wheel_packager", ROOT / "packaging/wheel/create_wheel.py"
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    finally:
        sys.path.pop(0)
    prefix = tmp_path / "sdk"
    python_root = prefix / "share/pycircuit/python"
    native = python_root / "pycircuit"
    native.mkdir(parents=True)
    (native / "cli.py").write_text("# installed compiler driver\n", encoding="ascii")
    # Stale contents of an older install must not reintroduce the retired stage.
    retired = python_root / "arch_primitives"
    retired.mkdir()
    (retired / "__init__.py").write_text("# old expansion package\n", encoding="ascii")
    stage = tmp_path / "wheel"
    module._stage_installed_python(prefix, stage / "pycircuit")
    assert (stage / "pycircuit/cli.py").read_text() == "# installed compiler driver\n"
    assert not (stage / "arch_primitives").exists()
