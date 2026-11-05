"""Validate actual RTL against a reference generated from its exported Lean AST."""

from __future__ import annotations

import importlib.metadata
import json
import os
import shutil
import sys
from pathlib import Path

import pytest
from formal_rule_validation import RuleRtlValidation, ValidationProfileError
from test_formal_rule_export import (
    FIXTURES,
    LEAN_ROOT,
    ORIGINAL,
    ExportRun,
    _obligations,
    _sha256,
)
from test_source_system_execution import ROOT, _cli

pytestmark = pytest.mark.system
FIXTURE = ROOT / "formal/artifact"


def _harness(root):
    harness = ExportRun(root)
    harness.receipt["scope"] = "automatic known-two-state reset-inactive RTL validation"
    harness.receipt["inputs"].update(
        {
            str(path.relative_to(ROOT)): _sha256(path)
            for path in (
                Path(__file__),
                Path(__file__).with_name("formal_rule_validation.py"),
                FIXTURE / "checked_tb.sv",
            )
        }
    )
    yosys = os.environ.get("YOSYS", "yosys")
    assert shutil.which(yosys), "automatic RTL validation requires Yosys"
    executable = Path(shutil.which(yosys)).resolve()
    harness.receipt["tools"]["yosys"] = {
        "path": str(executable),
        "sha256": _sha256(executable),
    }
    if "yowasp" in executable.name:
        distribution = importlib.metadata.distribution("yowasp-yosys")
        wasm = [
            Path(distribution.locate_file(path))
            for path in distribution.files
            if str(path).endswith(".wasm")
        ]
        assert wasm, "record the actual Yosys implementation, not only its launcher"
        harness.receipt["yosys_wasm"] = {str(path): _sha256(path) for path in wasm}
        harness.receipt["yowasp_versions"] = {
            name: importlib.metadata.version(name)
            for name in ("yowasp-yosys", "yowasp-runtime", "wasmtime")
        }
    harness.run("yosys-version", [yosys, "-V"])
    return harness


def _cli_checked(harness, label, *arguments):
    return harness.record(
        label,
        [sys.executable, "-m", "pycircuit.cli", *arguments],
        _cli(*arguments),
    )


def _emit(harness, *, cpp=False):
    final = harness.root / "final.ac"
    _cli_checked(
        harness,
        "link",
        "link",
        str(harness.root / "unit"),
        "--top",
        harness.receipt["selected_top"],
        "-o",
        str(final),
    )
    rtl = harness.root / "rtl"
    _cli_checked(
        harness,
        "emit-rtl",
        "emit",
        str(final),
        "--target",
        "verilog",
        "--rtl-mode",
        "physical",
        "-o",
        str(rtl),
    )
    if cpp:
        _cli_checked(
            harness,
            "emit-cpp",
            "emit",
            str(final),
            "--target",
            "cpp",
            "-o",
            str(harness.root / "cpp"),
        )
    return rtl


def _serialize(harness, body):
    model = harness.root / "Exported.lean"
    harness.export("export-model", body, model)
    driver = harness.root / "SerializeModel.lean"
    driver.write_text(
        "import RuleSemantics.SymbolicSerialize\n"
        + model.read_text()
        + """
def main : IO Unit := do
  match RuleSemantics.SymbolicSerialize.serialize
      PycircuitExport.signature PycircuitExport.rules PycircuitExport.initialState
      PycircuitExport.definitionName PycircuitExport.inputNames PycircuitExport.registerNames
      PycircuitExport.registerKeys PycircuitExport.outputNames PycircuitExport.outputExpressions with
  | .ok encoded => IO.print encoded
  | .error reason => throw (IO.userError reason)
"""
    )
    result = harness.run(
        "serialize-model",
        [*harness.lean, "-DwarningAsError=true", "--run", str(driver)],
        cwd=LEAN_ROOT,
    )
    json.loads(result.stdout)
    formula = harness.root / "formula.json"
    formula.write_text(result.stdout)
    return model, formula


def _validation(harness, formula, rtl):
    def run(label, arguments, *, cwd):
        result = harness.run(label, arguments, cwd=cwd)
        return result.stdout + result.stderr

    return RuleRtlValidation(
        formula, rtl, harness.root, run, os.environ.get("YOSYS", "yosys")
    )


def _prove(harness, case, width):
    harness.receipt["state_audit"] = case.prepare()
    case.prove()
    witness = case.witness()
    maximum = (1 << width) - 1
    assert witness[1, "dut_r0"] == witness[1, "ref_r0"] == maximum
    assert witness[1, "related"] == 1
    harness.receipt["verdict"] = "proved"


def _checked_simulation(harness, case):
    assert shutil.which("verilator"), "checked physical RTL requires Verilator"
    for tool in ("verilator", "verilator_bin", "clang++", "g++", "make"):
        if shutil.which(tool):
            path = Path(shutil.which(tool)).resolve()
            harness.receipt["tools"][tool] = {
                "path": str(path),
                "sha256": _sha256(path),
            }
    harness.run("verilator-version", ["verilator", "--version"])
    bench = harness.root / "checked_tb.sv"
    shutil.copyfile(FIXTURE / "checked_tb.sv", bench)
    adapter = harness.root / "observed_counter.sv"
    adapter.write_text(
        "module observed_counter(input wire clk, rst, inc_request, dec_request,\n"
        "output wire [2:0] count);\n"
        "observed_dut dut(.clk(clk),.rst(rst),.i0(inc_request),"
        ".i1(dec_request),.o0(count));\nendmodule\n"
    )
    binary = harness.root / "verilated"
    harness.run(
        "checked-rtl-build",
        [
            "verilator",
            "--binary",
            "--timing",
            "-Wno-fatal",
            "--top-module",
            "checked_tb",
            "--Mdir",
            str(binary),
            *map(str, case.rtl_files),
            str(harness.root / "observed_dut.sv"),
            str(adapter),
            str(bench),
        ],
    )
    result = harness.run("checked-rtl-simulation", [str(binary / "Vchecked_tb")])
    transcript = result.stdout + result.stderr
    assert "PYC_FORMAL_CHECKED_RTL_PASS" in transcript
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript


@pytest.fixture(scope="module")
def baseline(tmp_path_factory):
    harness = _harness(tmp_path_factory.mktemp("automatic-original"))
    try:
        body = harness.compile(ORIGINAL, "GuardedCounter")
        model, formula = _serialize(harness, body)
        harness.check(
            model,
            _obligations(3, ["inc_request", "dec_request"], "count", "original")
            + """
namespace ExportAcceptance
theorem mutation_baseline_literals :
    execute ⟨true, false⟩ 4 = 5 ∧ execute ⟨true, false⟩ 0 = 1 ∧
    execute RuleSemantics.Counter.both 0 = 0 := by
  decide
#print axioms mutation_baseline_literals
end ExportAcceptance
""",
        )
        rtl = _emit(harness, cpp=True)
        case = _validation(harness, formula, rtl)
        _prove(harness, case, 3)
        _checked_simulation(harness, case)
        paths = {
            "source": harness.root / "source" / ORIGINAL.name,
            "model": model,
            "formula": formula,
            "reference": case.reference_path,
        }
        frozen = {name: _sha256(path) for name, path in paths.items()}
        harness.receipt["frozen_reference"] = frozen
        harness.receipt["status"] = "passed"
        yield formula, paths, frozen
    finally:
        harness.finish()


@pytest.fixture
def artifact(tmp_path):
    harness = _harness(tmp_path)
    try:
        yield harness
    finally:
        harness.finish()


def test_original_automatic_model_proves_and_checked_rtl_runs(baseline):
    _, paths, frozen = baseline
    assert {name: _sha256(path) for name, path in paths.items()} == frozen


def test_renamed_automatic_model_proves(artifact):
    body = artifact.compile(FIXTURES / "renamed_counter.py", "RenamedCounter")
    _, formula = _serialize(artifact, body)
    case = _validation(artifact, formula, _emit(artifact))
    _prove(artifact, case, 4)
    artifact.receipt["status"] = "passed"


@pytest.mark.parametrize(
    "name,before,after,current,requests,dut_next,reference_next",
    [
        ("guard", "count < 5", "count < 4", 4, [1, 0], 4, 5),
        ("arithmetic", "count = count + 1", "count = count + 2", 0, [1, 0], 2, 1),
        (
            "order",
            "ac.schedule(increment, decrement)",
            "ac.schedule(decrement, increment)",
            0,
            [1, 1],
            1,
            0,
        ),
    ],
)
def test_mutated_dut_has_semantic_counterexample(
    artifact, baseline, name, before, after, current, requests, dut_next, reference_next
):
    formula, paths, frozen = baseline
    assert {key: _sha256(path) for key, path in paths.items()} == frozen
    source = paths["source"].read_text()
    assert source.count(before) == 1
    mutated = artifact.root / "mutation"
    mutated.mkdir()
    fixture = mutated / ORIGINAL.name
    fixture.write_text(source.replace(before, after))
    assert _sha256(fixture) != frozen["source"]
    artifact.compile(fixture, "GuardedCounter")
    case = _validation(artifact, formula, _emit(artifact))
    artifact.receipt["state_audit"] = case.prepare()
    assert _sha256(case.reference_path) == frozen["reference"]
    values = case.counterexample([current], requests)
    assert values[2, "dut_r0"] == values[2, "dut_o0"] == dut_next
    assert values[2, "ref_r0"] == values[2, "ref_o0"] == reference_next
    assert values[2, "matched"] == 0
    assert {key: _sha256(path) for key, path in paths.items()} == frozen
    artifact.receipt["fixed_reference"] = frozen
    artifact.receipt["counterexample"] = {
        "mutation": name,
        "current": current,
        "inputs": requests,
        "dut_next": dut_next,
        "reference_next": reference_next,
    }
    artifact.receipt["verdict"] = "counterexample"
    artifact.receipt["status"] = "passed"


def test_hidden_register_automatic_model_proves(artifact):
    body = artifact.compile(FIXTURES / "hidden_register.py", "HiddenRegister")
    _, formula = _serialize(artifact, body)
    data = json.loads(formula.read_text())
    assert len(data["registers"]) == 2
    case = _validation(artifact, formula, _emit(artifact))
    _prove(artifact, case, 3)
    artifact.receipt["status"] = "passed"


def test_incomplete_state_map_is_rejected_before_proof(artifact):
    body = artifact.compile(FIXTURES / "hidden_register.py", "HiddenRegister")
    _, formula = _serialize(artifact, body)
    rtl = _emit(artifact)
    mapping_path = rtl / "rtl-names.json"
    mapping = json.loads(mapping_path.read_text())
    definition = next(
        row
        for row in mapping["definitions"]
        if row["definition"] == artifact.receipt["selected_top"]
    )
    assert len(definition["storage"]) == 2
    definition["storage"].pop()
    mapping_path.write_text(json.dumps(mapping))
    case = _validation(artifact, formula, rtl)
    with pytest.raises(ValidationProfileError, match="cover|mapping"):
        case.prepare()
    artifact.receipt["verdict"] = "unsupported-profile"
    artifact.receipt["status"] = "passed"
