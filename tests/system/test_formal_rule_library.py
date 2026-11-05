"""Independent source-library model, hardware and protocol acceptance."""

from __future__ import annotations

import re
import shutil
import sys
from pathlib import Path

import pytest
import test_source_system_execution as system
from test_formal_counter_artifact import (
    _cli_checked,
    _emit,
    _harness,
    _prove,
    _serialize,
    _validation,
)
from test_formal_rule_export import LEAN_ROOT, _obligations, _sha256
from test_source_system_execution import ROOT, _compile, _records

pytestmark = pytest.mark.system
LIBRARY = ROOT / "formal/library"
HIDDEN = ROOT / "tests/system/fixtures/formal_export/hidden_pair.py"


def _library_harness(root):
    harness = _harness(root)
    harness.receipt["inputs"].update(
        {
            str(path.relative_to(ROOT)): _sha256(path)
            for path in (
                Path(__file__),
                LIBRARY / "basic.py",
                LIBRARY / "consumer.py",
                HIDDEN,
                Path(system.__file__),
            )
        }
    )
    return harness


@pytest.fixture
def library_case(tmp_path):
    harness = _library_harness(tmp_path)
    try:
        yield harness
    finally:
        harness.finish()


def _kernel_check(harness, model, label, imports, obligations):
    path = harness.root / f"{label}.lean"
    path.write_text(imports + model.read_text() + "\n" + obligations)
    result = harness.run(
        label,
        [*harness.lean, "-DwarningAsError=true", str(path)],
        cwd=LEAN_ROOT,
    )
    transcript = result.stdout + result.stderr
    assert "sorryAx" not in transcript
    for dependencies in re.findall(r"depends on axioms:\s*\[([^]]*)\]", transcript):
        parsed = {
            dependency.strip()
            for dependency in dependencies.split(",")
            if dependency.strip()
        }
        assert parsed <= {
            "propext",
            "Quot.sound",
            "Classical.choice",
        }


def _source_connection(harness, model, name):
    if name == "Counter3":
        _kernel_check(
            harness,
            model,
            "source-model-connection",
            "import RuleSemantics.Library\n",
            _obligations(3, ["increment", "decrement"], "count", "original")
            + """
namespace SourceConnection
open RuleSemantics
theorem actual_counter_model_agrees (request : Counter.Requests) (count : BitVec 3) :
    ExportAcceptance.execute request count =
      Library.cycle Library.Counter3.rules (Library.Counter3.inputs request) (fun _ => count) 0 := by
  rw [Library.Counter3.cycle_correct]
  exact ExportAcceptance.all_states_and_requests request count
#print axioms actual_counter_model_agrees
end SourceConnection
""",
        )
        return
    registers = {"Register8": 1, "Slot8": 2, "Fifo2x8": 3}[name]
    alternatives = " ∨ ".join(f"index = {index}" for index in range(registers))
    cases = " | ".join("rfl" for _ in range(registers))
    _kernel_check(
        harness,
        model,
        "source-model-connection",
        "import RuleSemantics.Library\n",
        f"""
namespace SourceConnection
open RuleSemantics RuleSemantics.Syntax

theorem signatures_agree :
    PycircuitExport.signature = Library.{name}.signature := by rfl

theorem initial_states_agree :
    PycircuitExport.initialState = Library.{name}.initialState := by
  funext register
  rcases register with ⟨index, bound⟩
  have alternatives : {alternatives} := by
    change index < {registers} at bound
    omega
  rcases alternatives with {cases}
  all_goals rfl

theorem actual_rules_agree :
    PycircuitExport.rules = Library.{name}.rules := by rfl

theorem output_widths_agree :
    PycircuitExport.outputExpressions.map Output.width =
      Library.{name}.outputExpressions.map Output.width := by rfl

theorem actual_outputs_agree (input : Inputs PycircuitExport.signature)
    (state : State PycircuitExport.signature) :
    PycircuitExport.outputExpressions.map
        (fun (output : Output PycircuitExport.signature) =>
          BitVec.toNat (evalExpr (type := .bits output.width) output.expression input state)) =
      Library.{name}.outputExpressions.map
        (fun (output : Output Library.{name}.signature) =>
          BitVec.toNat (evalExpr (type := .bits output.width) output.expression input state)) := by rfl

#print axioms actual_rules_agree
#print axioms actual_outputs_agree
end SourceConnection
""",
    )


@pytest.mark.parametrize(
    "name,first_width",
    [("Register8", 8), ("Counter3", 3), ("Slot8", 1), ("Fifo2x8", 2)],
)
def test_actual_library_models_and_rtl_agree(library_case, name, first_width):
    body = library_case.compile(LIBRARY / "basic.py", name)
    model, formula = _serialize(library_case, body)
    _source_connection(library_case, model, name)
    case = _validation(library_case, formula, _emit(library_case))
    _prove(library_case, case, first_width)
    library_case.receipt["library_module"] = name
    library_case.receipt["model_connection"] = "kernel-checked"
    library_case.receipt["status"] = "passed"


@pytest.fixture(scope="module")
def hidden_pair(tmp_path_factory):
    harness = _library_harness(tmp_path_factory.mktemp("hidden-pair"))
    try:
        body = harness.compile(HIDDEN, "HiddenPair")
        model, formula = _serialize(harness, body)
        _kernel_check(
            harness,
            model,
            "hidden-pair-literal",
            "",
            """
namespace HiddenPairAcceptance
open RuleSemantics RuleSemantics.Syntax PycircuitExport

theorem unequal_initial_values : initialState 0 = 0 ∧ initialState 1 = 1 := by
  decide

def requests : Inputs signature := fun i =>
  match i with
  | ⟨0, _⟩ => (1 : BitVec 1)
  | ⟨1, _⟩ => (1 : BitVec 1)
  | ⟨2, _⟩ => (2 : BitVec 3)
  | ⟨n + 3, bound⟩ => False.elim (by change n + 3 < 3 at bound; omega)

def unequalState : State signature := fun r =>
  match r with
  | ⟨0, _⟩ => (0 : BitVec 3)
  | ⟨1, _⟩ => (1 : BitVec 3)
  | ⟨n + 2, bound⟩ => False.elim (by change n + 2 < 2 at bound; omega)

theorem forwarded_hidden_literal :
    let next := (runSchedule (rules.map interpretRule) requests unequalState).1
    next 0 = 3 ∧ next 1 = 3 := by
  decide
#print axioms forwarded_hidden_literal
end HiddenPairAcceptance
""",
        )
        case = _validation(harness, formula, _emit(harness))
        _prove(harness, case, 3)
        paths = {
            "source": harness.root / "source" / HIDDEN.name,
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


def test_hidden_pair_full_state_equivalence(hidden_pair):
    _, paths, frozen = hidden_pair
    assert {name: _sha256(path) for name, path in paths.items()} == frozen


def test_hidden_update_changes_later_root_and_public_output(library_case, hidden_pair):
    formula, paths, frozen = hidden_pair
    assert {name: _sha256(path) for name, path in paths.items()} == frozen
    text = paths["source"].read_text()
    before = "hidden = hidden + incoming"
    assert text.count(before) == 1
    directory = library_case.root / "mutated"
    directory.mkdir()
    fixture = directory / HIDDEN.name
    fixture.write_text(text.replace(before, before + " + 1"))
    library_case.compile(fixture, "HiddenPair")
    case = _validation(library_case, formula, _emit(library_case))
    library_case.receipt["state_audit"] = case.prepare()
    assert _sha256(case.reference_path) == frozen["reference"]
    values = case.counterexample([0, 1], [1, 1, 2])
    assert values[1, "dut_o0"] == values[1, "ref_o0"] == 0
    assert values[1, "matched"] == 1
    for register in (0, 1):
        assert values[2, f"dut_r{register}"] == 4
        assert values[2, f"ref_r{register}"] == 3
    assert values[2, "dut_o0"] == 4 and values[2, "ref_o0"] == 3
    assert {name: _sha256(path) for name, path in paths.items()} == frozen
    library_case.receipt["fixed_reference"] = frozen
    library_case.receipt["verdict"] = "counterexample"
    library_case.receipt["counterexample"] = {
        "state": [0, 1],
        "inputs": [1, 1, 2],
        "dut_next": [4, 4],
        "reference_next": [3, 3],
        "dut_output": 4,
        "reference_output": 3,
    }
    library_case.receipt["status"] = "passed"


def _expected_samples():
    """List queues specify protocol behavior independently of head/tail registers."""
    queues = {1: [], 2: []}
    consumed = {1: [], 2: []}
    stored = count = 0
    samples = []
    for phase in range(12):
        put = phase in {0, 1, 2, 3, 4, 5, 8}
        take = phase in {0, 3, 4, 6, 7, 9, 10}
        data = phase + 10
        row = [phase, int(put), data, int(take), stored, count]
        for capacity, queue in queues.items():
            ready = len(queue) < capacity or (take and bool(queue))
            row.extend((int(ready), int(bool(queue)), queue[0] if queue else 0))
        samples.append(tuple(row))
        if put:
            stored = data
        count = max(0, min(5, count + int(put)) - int(take))
        for capacity, queue in queues.items():
            if take and queue:
                consumed[capacity].append(queue.pop(0))
            if put and len(queue) < capacity:
                queue.append(data)
    assert consumed == {1: [10, 13, 14, 18], 2: [10, 11, 13, 14, 18]}
    return [sample for sample in samples for _ in range(2)]


def test_separate_importer_generated_cpp_and_rtl_protocol(library_case, monkeypatch):
    library_case.receipt["scope"] = "generated System library protocol on C++ and RTL"
    provider = library_case.compile(LIBRARY / "basic.py", "Register8")
    source = library_case.root / "consumer-source"
    source.mkdir()
    shutil.copyfile(LIBRARY / "consumer.py", source / "consumer.py")
    consumer = library_case.root / "consumer-unit"
    library_case.record(
        "consumer-compile",
        [
            sys.executable,
            "-m",
            "pycircuit.cli",
            "compile",
            "-c",
            str(source / "consumer.py"),
            "--source-root",
            str(source),
            "--package-prefix",
            "checks",
            "-o",
            str(consumer),
            "-I",
            str(provider.parent),
        ],
        _compile(source, "consumer.py", consumer, [provider.parent]),
    )
    library_case.receipt["selected_top"] = "checks.consumer.ExerciseLibrary"
    library_case.receipt["provider_unit"] = str(provider.parent)
    library_case.receipt["consumer_unit"] = str(consumer)
    final = library_case.root / "consumer.ac"
    _cli_checked(
        library_case,
        "consumer-link",
        "link",
        str(provider.parent),
        str(consumer),
        "--top",
        "checks.consumer.ExerciseLibrary",
        "-o",
        str(final),
    )
    expected = _expected_samples()
    runs = []
    for target in ("cpp", "verilog"):
        original_run = system._run
        ordinal = 0

        def record_run(
            arguments, *, timeout=120, cwd=None, _run=original_run, _target=target
        ):
            nonlocal ordinal
            ordinal += 1
            result = _run(arguments, timeout=timeout, cwd=cwd)
            return library_case.record(f"{_target}-build-{ordinal}", arguments, result)

        # Record the existing generated-System helper's real subprocesses.
        with monkeypatch.context() as capture:
            capture.setattr(system, "_run", record_run)
            binary = system._bundle(final, library_case.root, target)
        for workers in (1, 2) if target == "cpp" else (1,):
            arguments = (
                ["--cycles", "12", "--workers", str(workers)]
                if target == "cpp"
                else ["+cycles=12"]
            )
            result = library_case.run(
                f"{target}-{workers}-execute", [str(binary), *arguments]
            )
            rows = _records(result.stdout)
            observed = [
                tuple(int(value["value"]) for value in row["values"])
                for row in rows
                if row["kind"] == "log" and row["spec"]["event"] == "library sample"
            ]
            assert observed == expected
            assert "PYCIRCUIT_PHYSICAL_FAULT" not in result.stdout + result.stderr
            runs.append(
                {"target": target, "workers": workers, "samples": len(observed)}
            )
    library_case.receipt["protocol_runs"] = runs
    library_case.receipt["status"] = "passed"
