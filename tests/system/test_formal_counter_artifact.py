"""Bind the fixed counter reference to an actual public physical RTL artifact."""

from __future__ import annotations

import hashlib
import importlib.metadata
import json
import os
import re
import shutil
import sys
from pathlib import Path

import pytest
from test_source_system_execution import ROOT, _cli, _compile, _ok, _run

pytestmark = pytest.mark.system
FIXTURE = ROOT / "formal/artifact"
SIGNALS = ("dut_count", "ref_count", "matched", "inc_request", "dec_request")


def _sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _wrapper(generated, destination):
    manifest = json.loads((generated / "generated.json").read_text())
    ports = json.loads((generated / "ports.json").read_text())
    assert manifest["rtl_mode"] == "physical"
    assert ports["controls"] == []
    assert len(ports["inputs"]) == 4
    bindings = []
    names = set()
    for row in ports["inputs"]:
        assert row["width"] == 1
        if row["ordinal"] == ports["domains"]["clock"]:
            name = "clk"
        elif row["ordinal"] == ports["domains"]["reset"]:
            name = "rst"
        else:
            name = row["name"]
        names.add(name)
        bindings.append(f".{row['wire']}({name})")
    assert names == {"clk", "rst", "inc_request", "dec_request"}
    assert len(ports["outputs"]) == 1
    output = ports["outputs"][0]
    assert output["width"] == 3 and output["availability"] is None
    bindings.append(f".{output['wire']}(count)")
    destination.write_text(
        "module observed_counter(input wire clk, rst, inc_request, dec_request,\n"
        "output wire [2:0] count);\n"
        + manifest["root_rtl_name"]
        + " raw_dut("
        + ", ".join(bindings)
        + ");\nendmodule\n"
    )
    return [
        generated / row["path"] for row in manifest["files"] if row["role"] == "rtl"
    ]


def _audit_state(path):
    design = json.loads(path.read_text())
    assert set(design["modules"]) == {"equivalence"}
    top = design["modules"]["equivalence"]
    assert top.get("memories", {}) == {}
    for obj in [top, *top["netnames"].values(), *top["cells"].values()]:
        assert "init" not in obj.get("attributes", {}), "initial constraint survived"
    allowed = {
        "$dff",
        "$mux",
        "$add",
        "$sub",
        "$lt",
        "$gt",
        "$eq",
        "$eqx",
        "$and",
        "$or",
        "$logic_and",
        "$logic_not",
        "$not",
        "$reduce_bool",
    }
    assert {cell["type"] for cell in top["cells"].values()} <= allowed
    banks = [cell for cell in top["cells"].values() if cell["type"] == "$dff"]
    assert len(banks) == 2
    state = []
    for bank in banks:
        assert int(bank["parameters"]["WIDTH"], 2) == 3
        assert int(bank["parameters"]["CLK_POLARITY"], 2) == 1
        assert bank["connections"]["CLK"] == top["ports"]["clk"]["bits"]
        state.extend(bank["connections"]["Q"])
    expected = top["ports"]["dut_count"]["bits"] + top["ports"]["ref_count"]["bits"]
    assert len(set(state)) == 6 and sorted(state) == sorted(expected)
    return {"positive_edge_banks": 2, "state_bits": 6, "clock": "clk", "init": []}


def _sat_values(transcript):
    values = {}
    for line in transcript.splitlines():
        match = re.fullmatch(
            r"\s*([12])\s+\\(dut_count|ref_count|matched|inc_request|dec_request)"
            r"\s+(\d+)\s+\S+\s+[01]+\s*",
            line,
        )
        if match:
            frame, name, value = match.groups()
            values[int(frame), name] = int(value)
    return values


def test_fixed_counter_artifact_refines_independent_reference(tmp_path):
    yosys_tool = os.environ.get("YOSYS", "yosys")
    for tool in (yosys_tool, "verilator"):
        assert shutil.which(tool), f"formal counter artifact test requires {tool}"
    commands = []
    receipt = {
        "scope": "known-two-state fixed-width3 capacity5 state-only physical RTL",
        "status": "incomplete",
        "commands": commands,
    }

    def record(label, arguments, result):
        (tmp_path / f"{label}.log").write_text(result.stdout + result.stderr)
        commands.append({"label": label, "argv": arguments, "exit": result.returncode})
        (tmp_path / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        return _ok(result)

    def run(label, arguments, timeout=120):
        return record(label, arguments, _run(arguments, timeout=timeout, cwd=tmp_path))

    def cli(label, *arguments):
        return record(
            label,
            [sys.executable, "-m", "pycircuit.cli", *arguments],
            _cli(*arguments),
        )

    def yosys(label, script):
        path = tmp_path / f"{label}.ys"
        path.write_text(script + "\n")
        return run(label, [yosys_tool, "-s", path.name])

    def yosys_path(path):
        # YoWASP reserves absolute /tmp for its own temporary directory.
        return json.dumps(str(path.relative_to(tmp_path)))

    try:
        tools = {
            name: Path(os.environ[variable]).resolve()
            for name, variable in (
                ("source_compiler", "PYCIRCUIT_SOURCE_COMPILER"),
                ("linker", "PYCIRCUIT_LINKER"),
                ("emitter", "PYCIRCUIT_EMITTER"),
            )
        }
        tools.update(
            {
                "yosys": Path(shutil.which(yosys_tool)).resolve(),
                "verilator": Path(shutil.which("verilator")).resolve(),
            }
        )
        tools["python"] = Path(sys.executable).resolve()
        for name in ("verilator_bin", "clang++", "g++", "make"):
            if shutil.which(name):
                tools[name] = Path(shutil.which(name)).resolve()
        receipt["tools"] = {
            name: {"path": str(path), "sha256": _sha256(path)}
            for name, path in tools.items()
        }
        toolchain = Path(os.environ["PYC_TOOLCHAIN_ROOT"]).resolve()
        receipt["toolchain_root"] = str(toolchain)
        metadata = toolchain / "share/pycircuit/toolchain-metadata.json"
        receipt["toolchain_metadata"] = {
            "path": str(metadata),
            "sha256": _sha256(metadata),
            "content": json.loads(metadata.read_text()),
        }
        if "yowasp" in tools["yosys"].name:
            distribution = importlib.metadata.distribution("yowasp-yosys")
            wasm = [
                Path(distribution.locate_file(path))
                for path in distribution.files
                if str(path).endswith(".wasm")
            ]
            assert wasm, "yowasp executable must bind its actual WASM implementation"
            receipt["yosys_wasm"] = {str(path): _sha256(path) for path in wasm}
            receipt["yowasp_versions"] = {
                name: importlib.metadata.version(name)
                for name in ("yowasp-yosys", "yowasp-runtime", "wasmtime")
            }
        run("yosys-version", [yosys_tool, "-V"])
        run("verilator-version", ["verilator", "--version"])
        receipt["revision"] = run(
            "revision", ["git", "-C", str(ROOT), "rev-parse", "HEAD"]
        ).strip()
        receipt["inputs"] = {
            str(path.relative_to(ROOT)): _sha256(path)
            for path in [
                Path(__file__),
                *sorted(FIXTURE.glob("*")),
                *sorted((ROOT / "formal/lean").rglob("*.lean")),
                ROOT / "formal/lean/lean-toolchain",
            ]
            if path.is_file()
        }
        for name in ("counter_reference.sv", "checked_tb.sv"):
            shutil.copyfile(FIXTURE / name, tmp_path / name)
        source_text = (FIXTURE / "guarded_counter.py").read_text()
        forward = "ac.schedule(increment, decrement)"
        assert source_text.count(forward) == 1
        normalized = {}
        for name, text in (
            ("positive", source_text),
            (
                "reversed",
                source_text.replace(forward, "ac.schedule(decrement, increment)"),
            ),
        ):
            directory = tmp_path / name
            source = directory / "source"
            source.mkdir(parents=True)
            (source / "guarded_counter.py").write_text(text)
            unit = directory / "unit"
            record(
                name + "-compile",
                [
                    sys.executable,
                    "-m",
                    "pycircuit.cli",
                    "compile",
                    "-c",
                    str(source / "guarded_counter.py"),
                    "--source-root",
                    str(source),
                    "--package-prefix",
                    "checks",
                    "-o",
                    str(unit),
                ],
                _compile(source, "guarded_counter.py", unit),
            )
            final = directory / "final.ac"
            cli(
                name + "-link",
                "link",
                str(unit),
                "--top",
                "checks.guarded_counter.GuardedCounter",
                "-o",
                str(final),
            )
            rtl = directory / "rtl"
            cli(
                name + "-emit-rtl",
                "emit",
                str(final),
                "--target",
                "verilog",
                "--rtl-mode",
                "physical",
                "-o",
                str(rtl),
            )
            if name == "positive":
                cli(
                    name + "-emit-cpp",
                    "emit",
                    str(final),
                    "--target",
                    "cpp",
                    "-o",
                    str(directory / "cpp"),
                )
            wrapper = directory / "observed_counter.sv"
            closure = _wrapper(rtl, wrapper)
            miter = directory / "equivalence.sv"
            miter.write_text(
                "module equivalence(input wire clk, rst, inc_request, dec_request,\n"
                "output wire [2:0] dut_count, ref_count, output wire matched);\n"
                "observed_counter dut(clk, rst, inc_request, dec_request, dut_count);\n"
                "counter_reference ref_model(clk, rst, inc_request, dec_request, ref_count);\n"
                "assign matched = (dut_count == ref_count);\nendmodule\n"
            )
            il, netlist = directory / "normalized.il", directory / "normalized.json"
            quoted = " ".join(
                yosys_path(path)
                for path in [
                    *closure,
                    wrapper,
                    tmp_path / "counter_reference.sv",
                    miter,
                ]
            )
            yosys(
                name + "-normalize",
                f"read_verilog -sv -D SYNTHESIS {quoted}\n"
                "hierarchy -check -top equivalence\nproc -noopt\nflatten -noscopeinfo\n"
                "setattr -unset init\nsetattr -mod -unset init\n"
                "opt_clean\ndffunmap\nopt_clean\n"
                f"write_rtlil {yosys_path(il)}\nwrite_json {yosys_path(netlist)}",
            )
            receipt[name + "_state_audit"] = _audit_state(netlist)
            normalized[name] = il
            if name == "positive":
                binary = directory / "verilated"
                run(
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
                        *map(str, closure),
                        str(wrapper),
                        str(tmp_path / "checked_tb.sv"),
                    ],
                    timeout=180,
                )
                simulation = run(
                    "checked-rtl-simulation", [str(binary / "Vchecked_tb")]
                )
                assert "PYC_FORMAL_CHECKED_RTL_PASS" in simulation
                assert "PYCIRCUIT_PHYSICAL_FAULT" not in simulation
        show = " ".join("-show " + signal for signal in SIGNALS)
        positive = f"read_rtlil {yosys_path(normalized['positive'])}\n"
        proof = yosys(
            "positive-step-sat",
            positive + "sat -seq 2 -set rst 0 -set-at 1 matched 1 "
            f"-prove matched 1 -prove-skip 1 -verify {show}",
        )
        assert "SAT proof finished - no model found: SUCCESS!" in proof
        witness = yosys(
            "unconstrained-initial-seven",
            positive
            + f"sat -seq 1 -set rst 0 -set dut_count 7 -set ref_count 7 {show}",
        )
        values = _sat_values(witness)
        assert values[1, "dut_count"] == values[1, "ref_count"] == 7
        assert values[1, "matched"] == 1
        mutant = yosys(
            "reversed-schedule-counterexample",
            f"read_rtlil {yosys_path(normalized['reversed'])}\n"
            "sat -seq 2 -set rst 0 -set-at 1 dut_count 0 -set-at 1 ref_count 0 "
            "-set-at 1 inc_request 1 -set-at 1 dec_request 1 "
            f"-prove matched 1 -prove-skip 1 {show}",
        )
        assert "SAT proof finished - model found: FAIL!" in mutant
        values = _sat_values(mutant)
        assert values[1, "dut_count"] == values[1, "ref_count"] == 0
        assert values[1, "inc_request"] == values[1, "dec_request"] == 1
        assert values[2, "dut_count"] == 1 and values[2, "ref_count"] == 0
        assert values[2, "matched"] == 0
        receipt["mutant_counterexample"] = {
            "initial": 0,
            "increment": 1,
            "decrement": 1,
            "dut_next": 1,
            "reference_next": 0,
        }
        receipt["status"] = "passed"
    finally:
        receipt["artifacts"] = {
            str(path.relative_to(tmp_path)): _sha256(path)
            for path in sorted(tmp_path.rglob("*"))
            if path.is_file() and path.name != "receipt.json"
        }
        (tmp_path / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
