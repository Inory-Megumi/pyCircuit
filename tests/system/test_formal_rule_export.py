"""Check native typed-source Rule exports with independent Lean obligations."""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import sys
from pathlib import Path

import pytest
from test_source_system_execution import ROOT, _compile, _ok, _run

pytestmark = pytest.mark.system
FIXTURES = Path(__file__).parent / "fixtures/formal_export"
LEAN_ROOT = ROOT / "formal/lean"
ORIGINAL = ROOT / "formal/artifact/guarded_counter.py"


def _sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class ExportRun:
    def __init__(self, root):
        self.root = root
        toolchain = Path(os.environ["PYC_TOOLCHAIN_ROOT"]).resolve()
        self.opt = Path(
            os.environ.get("PYCIRCUIT_OPT", str(toolchain / "bin/pycircuit-opt"))
        ).resolve()
        assert self.opt.is_file(), "native pycircuit-opt is required"
        configured = os.environ.get("PYC_LEAN")
        self.lean = (
            [configured]
            if configured
            else [os.environ.get("PYC_LAKE", "lake"), "env", "lean"]
        )
        assert shutil.which(self.lean[0]), "Lean checking executable is required"
        self.receipt = {
            "status": "incomplete",
            "scope": "typed-unit extraction; known-two-state reset-inactive state only",
            "commands": [],
            "inputs": {
                str(path.relative_to(ROOT)): _sha256(path)
                for path in [
                    Path(__file__),
                    ORIGINAL,
                    *sorted(FIXTURES.glob("*.py")),
                    *sorted(LEAN_ROOT.rglob("*.lean")),
                    LEAN_ROOT / "lean-toolchain",
                ]
                if path.is_file()
            },
        }
        metadata = toolchain / "share/pycircuit/toolchain-metadata.json"
        self.receipt["toolchain_metadata"] = {
            "path": str(metadata),
            "sha256": _sha256(metadata),
            "content": json.loads(metadata.read_text()),
        }
        tools = {
            "opt": self.opt,
            "python": Path(sys.executable).resolve(),
            "lean_command": Path(shutil.which(self.lean[0])).resolve(),
            **{
                variable: Path(os.environ[variable]).resolve()
                for variable in (
                    "PYCIRCUIT_SOURCE_COMPILER",
                    "PYCIRCUIT_LINKER",
                    "PYCIRCUIT_EMITTER",
                )
            },
        }
        self.receipt["tools"] = {
            name: {"path": str(path), "sha256": _sha256(path)}
            for name, path in tools.items()
        }
        self.run("opt-version", [str(self.opt), "--version"])
        self.run("lean-version", [*self.lean, "--version"], cwd=LEAN_ROOT)
        self.receipt["revision"] = self.run(
            "revision", ["git", "-C", str(ROOT), "rev-parse", "HEAD"]
        ).stdout.strip()

    def record(self, label, arguments, result, *, failure=False):
        (self.root / f"{label}.log").write_text(result.stdout + result.stderr)
        self.receipt["commands"].append(
            {"label": label, "argv": arguments, "exit": result.returncode}
        )
        (self.root / "commands.json").write_text(
            json.dumps(self.receipt["commands"], indent=2) + "\n"
        )
        if not failure:
            _ok(result)
        return result

    def run(self, label, arguments, *, failure=False, cwd=None):
        return self.record(
            label,
            arguments,
            _run(arguments, timeout=180, cwd=cwd or self.root),
            failure=failure,
        )

    def compile(self, fixture, top, *, reversed_order=False):
        source = self.root / "source"
        source.mkdir()
        text = fixture.read_text()
        if reversed_order:
            before = "ac.schedule(increment, decrement)"
            assert text.count(before) == 1
            text = text.replace(before, "ac.schedule(decrement, increment)")
        (source / fixture.name).write_text(text)
        unit = self.root / "unit"
        self.record(
            "compile",
            [
                sys.executable,
                "-m",
                "pycircuit.cli",
                "compile",
                "-c",
                str(source / fixture.name),
                "--source-root",
                str(source),
                "--package-prefix",
                "checks",
                "-o",
                str(unit),
            ],
            _compile(source, fixture.name, unit),
        )
        manifest = json.loads((unit / "unit.json").read_text())
        body = unit / manifest["files"]["body"]
        self.receipt["selected_top"] = f"checks.{fixture.stem}.{top}"
        return body

    def export(self, label, body, destination, *, failure=False, ir_output=None):
        return self.run(
            label,
            [
                str(self.opt),
                str(body),
                "--ac-export-rule-lean="
                + f"top={self.receipt['selected_top']} output={json.dumps(str(destination))}",
                "-o",
                str(ir_output or os.devnull),
            ],
            failure=failure,
        )

    def check(self, model, obligations):
        check = self.root / "CheckedExport.lean"
        check.write_text(
            "import RuleSemantics.CounterReference\n"
            + model.read_text()
            + "\n"
            + obligations
        )
        checked = self.run(
            "lean-check",
            [*self.lean, "-DwarningAsError=true", str(check)],
            cwd=LEAN_ROOT,
        )
        transcript = checked.stdout + checked.stderr
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
            }

    def finish(self):
        self.receipt["artifacts"] = {
            str(path.relative_to(self.root)): _sha256(path)
            for path in sorted(self.root.rglob("*"))
            if path.is_file() and path.name != "receipt.json"
        }
        (self.root / "receipt.json").write_text(
            json.dumps(self.receipt, indent=2) + "\n"
        )


@pytest.fixture
def exported(tmp_path):
    harness = ExportRun(tmp_path)
    try:
        yield harness
    finally:
        harness.finish()


def _obligations(width, input_names, register_name, mode):
    common = f"""
namespace ExportAcceptance
open RuleSemantics RuleSemantics.Syntax PycircuitExport

theorem exported_interface :
    signature.nr = 1 ∧ signature.ni = 2 ∧ signature.regWidth 0 = {width} ∧
    inputNames = {json.dumps(input_names)} ∧ registerNames = ["{register_name}"] ∧
    outputNames = ["result"] ∧ outputExpressions.length = 1 ∧
    registerKeys.length = 1 ∧ initialState 0 = 0 := by
  decide

def bindRequests (request : Counter.Requests) : Inputs signature :=
  Fin.cases
    (motive := fun index => (signature.inputType index).denote)
    (if request.increment then (1 : BitVec 1) else (0 : BitVec 1))
    (fun index => by
      have same : index = 0 := Subsingleton.elim _ _
      subst index
      exact if request.decrement then (1 : BitVec 1) else (0 : BitVec 1))

def state (count : BitVec {width}) : State signature :=
  fun register => by
    have same : register = 0 := Subsingleton.elim _ _
    subst register
    exact count

def execute (request : Counter.Requests) (count : BitVec {width}) : BitVec {width} :=
  (runSchedule (rules.map interpretRule) (bindRequests request) (state count)).1 0

#print axioms exported_interface

theorem exported_observation (input : Inputs signature) (current : State signature) :
    (evalExpr (outputExpressions[0]'(by decide)).expression input current).toNat =
      (current 0).toNat := by rfl
#print axioms exported_observation
"""
    if mode == "reversed":
        return (
            common
            + """
theorem reversed_counterexample :
    execute Counter.both 0 = 1 ∧ CounterReference.step Counter.both 0 = 0 := by
  decide
#print axioms reversed_counterexample
end ExportAcceptance
"""
        )
    reference = (
        "CounterReference.step request count"
        if mode == "original"
        else "(BitVecCounter.execute 4 9 [.increment, .decrement] request count).1"
    )
    checks = f"""
def reference (request : Counter.Requests) (count : BitVec {width}) : BitVec {width} :=
  {reference}

private theorem finite_states : ∀ inc dec : Bool, ∀ count : Fin (2 ^ {width}),
    execute ⟨inc, dec⟩ (BitVec.ofFin count) = reference ⟨inc, dec⟩ (BitVec.ofFin count) := by
  decide

theorem all_states_and_requests (request : Counter.Requests) (count : BitVec {width}) :
    execute request count = reference request count := by
  rcases request with ⟨inc, dec⟩
  simpa only [BitVec.ofFin_toFin] using finite_states inc dec count.toFin

#check all_states_and_requests
#print axioms all_states_and_requests
"""
    if mode == "variant":
        checks += """
theorem capacity_nine_literals :
    execute ⟨true, false⟩ 8 = 9 ∧ execute ⟨true, false⟩ 9 = 9 := by
  decide
#print axioms capacity_nine_literals
"""
    return common + checks + "end ExportAcceptance\n"


@pytest.mark.parametrize("mode", ["original", "variant", "reversed"])
def test_exported_counter_semantics(exported, mode):
    variant = mode == "variant"
    fixture = FIXTURES / "renamed_counter.py" if variant else ORIGINAL
    top = "RenamedCounter" if variant else "GuardedCounter"
    body = exported.compile(fixture, top, reversed_order=mode == "reversed")
    body_hash = _sha256(body)
    model = exported.root / "Exported.lean"
    before, after = exported.root / "before.ac", exported.root / "after.ac"
    if mode == "original":
        exported.run("parse-print", [str(exported.opt), str(body), "-o", str(before)])
    exported.export("export", body, model, ir_output=after)
    assert _sha256(body) == body_hash
    if mode == "original":
        assert before.read_bytes() == after.read_bytes(), "export pass mutated typed IR"
    exported.check(
        model,
        _obligations(
            4 if variant else 3,
            (
                ["raise_request", "lower_request"]
                if variant
                else ["inc_request", "dec_request"]
            ),
            "occupancy" if variant else "count",
            mode,
        ),
    )
    exported.receipt["status"] = "passed"


def test_stale_snapshot_rejection_preserves_publication(exported):
    body = exported.compile(FIXTURES / "saved_snapshot.py", "SavedSnapshot")
    destination = exported.root / "publication"
    destination.mkdir()
    output = destination / "Rejected.lean"
    result = exported.export("reject-fresh", body, output, failure=True)
    assert result.returncode == 1
    assert (
        result.stderr.strip()
    ), "unsupported-profile rejection must explain the failure"
    assert re.search(
        r"\b(snapshot|snapshots|stale|version|versions)\b", result.stderr, re.IGNORECASE
    )
    assert list(destination.iterdir()) == [], "rejection left a partial publication"
    sentinel = b"existing independently owned output\n"
    output.write_bytes(sentinel)
    result = exported.export("reject-existing", body, output, failure=True)
    assert result.returncode == 1
    assert re.search(
        r"\b(snapshot|snapshots|stale|version|versions)\b", result.stderr, re.IGNORECASE
    )
    assert {path.name: path.read_bytes() for path in destination.iterdir()} == {
        output.name: sentinel
    }
    exported.receipt["status"] = "passed"
