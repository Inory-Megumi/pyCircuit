"""Replay a checked concrete case through generated C++ and physical RTL."""

from __future__ import annotations

import json
import os
import re
from pathlib import Path

from formal_counterexample import validate_case
from formal_rule_model import RuleFormula, ValidationProfileError


def _require(condition, message):
    if not condition:
        raise ValidationProfileError(message)


def _identifier(value):
    _require(
        isinstance(value, str) and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", value),
        "replay requires ordinary emitted port identifiers",
    )
    return value


def _interface(directory, model, target):
    manifest = json.loads((directory / "generated.json").read_text())
    ports = json.loads((directory / "ports.json").read_text())
    _require(manifest.get("target") == target, "replay target mismatch")
    _require(
        manifest.get("entry", {}).get("definition")
        in (
            "@" + model.definition,
            "@" + json.dumps(model.definition, ensure_ascii=False),
        ),
        "replay definition differs from the checked model",
    )
    _require(
        ports.get("schema_version") == 1
        and ports.get("target") == target
        and ports.get("controls") == [],
        "unsupported replay port schema or controls",
    )
    incoming = ports["inputs"]
    ordinals = {row["ordinal"]: row for row in incoming}
    _require(len(ordinals) == len(incoming), "duplicate replay input ordinal")
    clock, reset = ports["domains"]["clock"], ports["domains"]["reset"]
    _require(
        clock != reset
        and clock in ordinals
        and reset in ordinals
        and ordinals[clock]["width"] == ordinals[reset]["width"] == 1,
        "replay requires distinct one-bit clock and reset inputs",
    )
    data = [row for row in incoming if row["ordinal"] not in (clock, reset)]
    inputs = {row["name"]: row for row in data}
    outputs = {row["name"]: row for row in ports["outputs"]}
    _require(
        len(inputs) == len(data) == len(model.inputs)
        and set(inputs) == {row["name"] for row in model.inputs},
        "replay input inventory differs from the checked model",
    )
    _require(
        len(outputs) == len(ports["outputs"]) == len(model.outputs)
        and set(outputs) == {row["name"] for row in model.outputs},
        "replay output inventory differs from the checked model",
    )
    ordered_inputs = [inputs[row["name"]] for row in model.inputs]
    ordered_outputs = [outputs[row["name"]] for row in model.outputs]
    for actual, type_ in zip(ordered_inputs, model.input_types, strict=True):
        _require(
            type_[0] == "bits" and actual["width"] == type_[1],
            "replay input width/type mismatch",
        )
    for actual, width in zip(ordered_outputs, model.output_widths, strict=True):
        _require(
            actual["width"] == width and actual["availability"] is None,
            "replay output width/availability mismatch",
        )
    for row in [*incoming, *ordered_outputs]:
        _identifier(row["wire"])
    return manifest, ordinals[clock], ordinals[reset], ordered_inputs, ordered_outputs


def _state_outputs(model):
    result = []
    for register, width in enumerate(model.widths):
        matches = [
            index
            for index, output in enumerate(model.outputs)
            if output["term"].get("op") == "read"
            and output["term"].get("index") == register
            and model.output_widths[index] == width
        ]
        _require(
            matches, "replay requires a direct public observation of every register"
        )
        result.append(matches[0])
    return result


def _rows(case, model):
    validate_case(model, case)
    rows = case["rows"]
    _require(
        rows[0]["state"] == model.initials,
        "replay must start at declared storage values",
    )
    return rows


def _rtl_state_paths(directory, model):
    mapping = json.loads((directory / "rtl-names.json").read_text())
    _require(
        mapping.get("kind") == "pycircuit.rtl-names" and mapping.get("version") == 1,
        "unsupported replay RTL state mapping",
    )
    entry = mapping.get("state_mapping", {})
    _require(
        entry.get("version") == 1 and entry.get("definition") == model.definition,
        "replay state mapping definition/version mismatch",
    )
    definitions = [
        row for row in mapping["definitions"] if row["definition"] == model.definition
    ]
    _require(
        len(definitions) == 1, "missing or duplicate replay state mapping definition"
    )
    rows = definitions[0].get("storage", [])
    owners = {row["owner"]: row for row in rows}
    _require(
        len(owners) == len(rows) == len(model.registers)
        and set(owners) == set(model.owner_keys),
        "replay state mapping must cover each source owner exactly once",
    )
    paths = []
    for register in model.registers:
        row = owners[register["owner"]]
        _require(
            row["name"] == register["name"]
            and row["width"] == register["width"]
            and row["kind"] in ("dff", "dffe"),
            "replay state mapping name/width/kind mismatch",
        )
        _require(
            isinstance(row["path"], list) and len(row["path"]) == 2,
            "unsupported replay state path",
        )
        components = [entry["root_instance"], *row["path"]]
        _require(
            all(
                isinstance(part, str) and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", part)
                for part in components
            ),
            "unsupported replay state path identifier",
        )
        paths.append("dut." + ".".join(components))
    _require(len(set(paths)) == len(paths), "duplicate replay physical state path")
    return paths


def _cpp_bits(width, value):
    words = [
        str((value >> offset) & ((1 << 64) - 1)) + "ULL"
        for offset in range(0, width, 64)
    ]
    return f"gfsim::Bits<{width}>{{" + ", ".join(words) + "}"


def _cpp_driver(model, rows, state_outputs, clock, reset, inputs, outputs):
    declarations = [
        '#include "pycircuit_system.hpp"',
        "#include <iomanip>",
        "#include <iostream>",
        "#include <stdexcept>",
        "#include <type_traits>",
        "class ReplaySystem final : public gfsim::SimSystem {",
        "public:",
        "  explicit ReplaySystem(pyc_root &root) : root_(root) {",
        '    if (!AddModule(root)) throw std::runtime_error("replay root registration");',
        "  }",
        "protected:",
        "  bool Precheck() noexcept override { return root_.pyc_validate_checks(failure_); }",
        "  gfsim::SimFailureInfo DescribeFailure(gfsim::SimFailurePhase) const noexcept override {",
        "    return failure_;",
        "  }",
        "private:",
        "  pyc_root &root_;",
        "  gfsim::SimFailureInfo failure_{};",
        "};",
        "template<class Wire> void printValue(const Wire &wire) {",
        '  if (!wire.isFullyKnown()) throw std::runtime_error("unknown replay observation");',
        "  const auto bits = wire.packed().value();",
        "  using Bits = std::remove_cvref_t<decltype(bits)>;",
        "  std::cout << ' ' << std::hex << std::setfill('0');",
        "  for (unsigned word = Bits::kWords; word > 0; --word)",
        "    std::cout << std::setw(16) << bits.word(word - 1);",
        "  std::cout << std::dec;",
        "}",
        "int main() {",
        "  try {",
        '    pyc_root dut("replay");',
        "    ReplaySystem system(dut);",
        "    auto epoch = [&]() {",
        "      if (system.Step() != gfsim::SimStepResult::Running)",
        '        throw std::runtime_error(std::string("replay check failed ") +',
        "          std::string(system.failureInfo().code) + std::string(system.failureInfo().message));",
        "    };",
    ]

    def drive(values, clock_value):
        assignments = []
        for port, (_, width), value in zip(
            inputs, model.input_types, values, strict=True
        ):
            wire = port["wire"]
            assignments.append(
                f"    dut.{wire} = decltype(dut.{wire})::known({_cpp_bits(width, value)});"
            )
        for port, value in ((clock, clock_value), (reset, 0)):
            wire = port["wire"]
            assignments.append(
                f"    dut.{wire} = decltype(dut.{wire})::known(gfsim::Bits<1>{{{value}ULL}});"
            )
        return assignments

    declarations += drive(rows[0]["inputs"], 0)
    declarations += ["    system.Build();", "    system.Reset();"]
    for index, row in enumerate(rows):
        declarations += drive(row["inputs"], 0)
        declarations += ["    epoch();", f'    std::cout << "PYC_REPLAY {index}";']
        for port in inputs:
            declarations.append(f"    printValue(dut.{port['wire']});")
        for output in [*state_outputs, *range(len(outputs))]:
            declarations.append(f"    printValue(dut.{outputs[output]['wire']});")
        declarations.append("    std::cout << '\\n';")
        if index + 1 < len(rows):
            declarations += drive(row["inputs"], 1)
            declarations.append("    epoch();")
    declarations += [
        "  } catch (const std::exception &error) {",
        "    std::cerr << error.what() << '\\n';",
        "    return 1;",
        "  }",
        "}",
        "",
    ]
    return "\n".join(declarations)


def _rtl_bench(model, rows, state_paths, manifest, clock, reset, inputs, outputs):
    lines = ["`timescale 1ns/1ps", "module replay_tb;", "  reg clk = 0, rst = 0;"]
    lines += [
        f"  reg [{type_[1] - 1}:0] i{index} = 0;"
        for index, type_ in enumerate(model.input_types)
    ]
    lines += [
        f"  wire [{width - 1}:0] o{index};"
        for index, width in enumerate(model.output_widths)
    ]
    lines += [
        f"  wire [{width - 1}:0] r{index} = {path};"
        for index, (width, path) in enumerate(
            zip(model.widths, state_paths, strict=True)
        )
    ]
    bindings = [f".{clock['wire']}(clk)", f".{reset['wire']}(rst)"]
    bindings += [f".{port['wire']}(i{index})" for index, port in enumerate(inputs)]
    bindings += [f".{port['wire']}(o{index})" for index, port in enumerate(outputs)]
    lines.append(
        f"  {_identifier(manifest['root_rtl_name'])} dut(" + ", ".join(bindings) + ");"
    )
    lines += [
        "  initial begin",
        '    $dumpfile("replay.vcd");',
        "    $dumpvars(0, replay_tb);",
    ]
    signals = [f"i{index}" for index in range(len(inputs))]
    signals += [f"r{index}" for index in range(len(model.widths))]
    signals += [f"o{index}" for index in range(len(outputs))]
    for index, row in enumerate(rows):
        for ordinal, (value, (_, width)) in enumerate(
            zip(row["inputs"], model.input_types, strict=True)
        ):
            lines.append(f"    i{ordinal} = {width}'d{value};")
        lines.append("    #2;")
        for signal in signals:
            lines.append(
                f'    if ($isunknown({signal})) $fatal(1, "unknown replay observation {signal}");'
            )
        format_ = " ".join(["PYC_REPLAY", str(index), *("%h" for _ in signals)])
        lines.append(f'    $display("{format_}", ' + ", ".join(signals) + ");")
        if index + 1 < len(rows):
            lines += ["    #1; clk = 1;", "    #1; clk = 0;"]
    lines += ["    #1; $finish;", "  end", "endmodule", ""]
    return "\n".join(lines)


def _readback(result, rows, input_count, register_count, output_count):
    transcript = result.stdout + result.stderr
    _require(result.returncode == 0, "replay executable failed\n" + transcript)
    _require(
        "PYCIRCUIT_PHYSICAL_FAULT" not in transcript, "physical replay reported a fault"
    )
    observations = []
    for line in result.stdout.splitlines():
        if not line.startswith("PYC_REPLAY "):
            continue
        tokens = line.split()
        _require(
            len(tokens) == 2 + input_count + register_count + output_count
            and tokens[1] == str(len(observations))
            and all(re.fullmatch(r"[0-9a-fA-F]+", token) for token in tokens[2:]),
            "replay trace contains malformed, unknown, or reordered observations",
        )
        values = [int(token, 16) for token in tokens[2:]]
        _require(len(observations) < len(rows), "replay performed an extra observation")
        observations.append(
            {
                "inputs": values[:input_count],
                "state": values[input_count : input_count + register_count],
                "outputs": values[input_count + register_count :],
            }
        )
    _require(
        observations == rows, "backend replay observations differ from checked witness"
    )
    return observations


def replay(case, formula_path, cpp_dir, rtl_dir, run, work_dir):
    """Observe k transitions and a final observation using each actual backend."""
    model = RuleFormula.load(formula_path)
    rows = _rows(case, model)
    state_outputs = _state_outputs(model)
    cpp_dir = Path(cpp_dir).resolve()
    rtl_dir = Path(rtl_dir).resolve()
    work_dir = Path(work_dir).resolve()
    work_dir.mkdir(parents=True, exist_ok=True)
    _, cpp_clock, cpp_reset, cpp_inputs, cpp_outputs = _interface(cpp_dir, model, "cpp")
    rtl_manifest, rtl_clock, rtl_reset, rtl_inputs, rtl_outputs = _interface(
        rtl_dir, model, "verilog"
    )
    _require(
        rtl_manifest.get("rtl_mode") == "physical",
        "replay requires physical checked RTL",
    )
    state_paths = _rtl_state_paths(rtl_dir, model)

    driver = work_dir / "cpp-driver"
    driver.mkdir(exist_ok=True)
    (driver / "replay.cpp").write_text(
        _cpp_driver(
            model, rows, state_outputs, cpp_clock, cpp_reset, cpp_inputs, cpp_outputs
        )
    )
    (driver / "CMakeLists.txt").write_text(
        "cmake_minimum_required(VERSION 3.25)\nproject(CheckedReplay LANGUAGES C CXX)\n"
        + f'add_subdirectory("{cpp_dir.as_posix()}" generated)\n'
        + "add_executable(pyc_replay replay.cpp)\n"
        + "target_compile_features(pyc_replay PRIVATE cxx_std_20)\n"
        + "target_link_libraries(pyc_replay PRIVATE pycircuit_modules)\n"
    )
    build = work_dir / "cpp-build"
    run(
        "replay-cpp-configure",
        [
            "cmake",
            "-S",
            str(driver),
            "-B",
            str(build),
            "-G",
            "Ninja",
            f"-DCMAKE_PREFIX_PATH={os.environ['PYC_TOOLCHAIN_ROOT']}",
        ],
        cwd=work_dir,
    )
    run(
        "replay-cpp-build",
        ["cmake", "--build", str(build), "--target", "pyc_replay", "--parallel", "3"],
        cwd=work_dir,
    )
    binary = build / ("pyc_replay.exe" if os.name == "nt" else "pyc_replay")
    cpp_result = run("replay-cpp-run", [str(binary)], cwd=work_dir)
    cpp_rows = _readback(
        cpp_result, rows, len(model.inputs), len(model.widths), len(model.outputs)
    )

    bench = work_dir / "replay_tb.sv"
    bench.write_text(
        _rtl_bench(
            model,
            rows,
            state_paths,
            rtl_manifest,
            rtl_clock,
            rtl_reset,
            rtl_inputs,
            rtl_outputs,
        )
    )
    sources = []
    for entry in rtl_manifest["files"]:
        if entry["role"] == "rtl":
            source = (rtl_dir / entry["path"]).resolve()
            _require(
                source.is_relative_to(rtl_dir) and source.is_file(),
                "invalid replay RTL closure path",
            )
            sources.append(source)
    _require(
        sources and len(set(sources)) == len(sources),
        "empty/duplicate replay RTL closure",
    )
    image = work_dir / "replay.vvp"
    run(
        "replay-rtl-build",
        [
            "iverilog",
            "-g2012",
            "-s",
            "replay_tb",
            "-o",
            str(image),
            *map(str, sources),
            str(bench),
        ],
        cwd=work_dir,
    )
    rtl_result = run("replay-rtl-run", ["vvp", str(image)], cwd=work_dir)
    rtl_rows = _readback(
        rtl_result, rows, len(model.inputs), len(model.widths), len(model.outputs)
    )
    vcd = work_dir / "replay.vcd"
    _require(
        vcd.is_file() and vcd.stat().st_size > 0, "physical replay produced no VCD"
    )
    cpp_trace, rtl_trace = work_dir / "cpp-trace.json", work_dir / "rtl-trace.json"
    cpp_trace.write_text(json.dumps(cpp_rows, indent=2) + "\n")
    rtl_trace.write_text(json.dumps(rtl_rows, indent=2) + "\n")
    metadata = work_dir / "replay-metadata.json"
    metadata.write_text(
        json.dumps(
            {
                "cpp_state_basis": "direct public output observations of logical state",
                "cpp_state_output_indices": state_outputs,
                "rtl_state_basis": "mapped physical storage observations",
                "rtl_state_paths": state_paths,
                "inputs_basis": "actual backend input port observations",
            },
            indent=2,
        )
        + "\n"
    )
    return {
        "cpp_trace": cpp_trace,
        "rtl_trace": rtl_trace,
        "vcd": vcd,
        "rows": len(rows),
        "metadata": metadata,
    }
