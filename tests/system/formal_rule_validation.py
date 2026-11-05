"""Verification-only encoding of serialized Lean terms and emitted physical RTL."""

from __future__ import annotations

import json
import re
from pathlib import Path

from formal_rule_model import (
    RuleFormula,
    _natural,
    _require,
)
from formal_rule_model import (
    ValidationProfileError as ValidationProfileError,
)


def _identifier(value):
    _require(
        isinstance(value, str)
        and bool(value)
        and not any(character.isspace() or ord(character) < 32 for character in value),
        "invalid emitted RTL identifier",
    )
    return "\\" + value + " "


def _declaration(width, name, kind="wire"):
    return f"{kind} [{width - 1}:0] {name}"


def _sat_values(transcript):
    result = {}
    for line in transcript.splitlines():
        match = re.fullmatch(
            r"\s*([12])\s+\\([A-Za-z0-9_]+)\s+\S+\s+\S+\s+([01]+)\s*", line
        )
        if match:
            frame, name, bits = match.groups()
            result[int(frame), name] = int(bits, 2)
    return result


class RuleRtlValidation:
    """Check all observed state and outputs, without interpreting Rule syntax."""

    def __init__(self, formula_path, rtl_dir, work_dir, run, yosys_tool):
        self.formula_path = Path(formula_path)
        self.rtl_dir = Path(rtl_dir).resolve()
        self.work_dir = Path(work_dir).resolve()
        self.run = run
        self.yosys_tool = str(yosys_tool)
        self.reference_path = self.work_dir / "reference.sv"
        self.normalized_path = self.work_dir / "normalized.il"
        self.rtl_files = []
        self._wires = []

    def _load_model(self):
        self.formula = RuleFormula.load(self.formula_path)
        for name in (
            "definition",
            "inputs",
            "registers",
            "outputs",
            "input_types",
            "widths",
            "initials",
            "owner_keys",
            "output_widths",
        ):
            setattr(self, name, getattr(self.formula, name))
        self.next_wires = [self._term(node)[1] for node in self.formula.data["next"]]
        self.output_wires = [self._term(row["term"])[1] for row in self.outputs]

    def _term(self, node):
        return self.formula.fold(node, self._render)

    def _render(self, node, type_, values):
        op = node["op"]
        if op in ("input", "read"):
            return f"i{node['index']}" if op == "input" else f"r{node['index']}"
        if op == "boolLit":
            expression = "1'b1" if node["value"] else "1'b0"
        elif op == "bitsLit":
            expression = f"{type_[1]}'d{node['value']}"
        elif op == "bit":
            expression = values[0]
        elif op == "concat":
            expression = "{" + ", ".join(values) + "}"
        elif op == "not":
            expression = f"(!{values[0]})"
        elif op == "ite":
            expression = f"({values[0]} ? {values[1]} : {values[2]})"
        else:
            operator = {"add": "+", "sub": "-", "ult": "<", "eq": "==", "and": "&&"}[op]
            expression = f"({values[0]} {operator} {values[1]})"
        name = f"n{len(self._wires)}"
        self._wires.append(f"  {_declaration(type_[1], name)} = {expression};")
        return name

    def _bind_ports(self):
        manifest = json.loads((self.rtl_dir / "generated.json").read_text())
        ports = json.loads((self.rtl_dir / "ports.json").read_text())
        _require(
            manifest.get("target") == "verilog"
            and manifest.get("rtl_mode") == "physical",
            "physical RTL required",
        )
        _require(
            ports.get("schema_version") == 1 and ports.get("controls") == [],
            "unsupported RTL interface",
        )
        incoming = ports["inputs"]
        ordinals = {row["ordinal"]: row for row in incoming}
        _require(len(ordinals) == len(incoming), "duplicate input ordinals")
        clock, reset = ports["domains"]["clock"], ports["domains"]["reset"]
        _require(
            clock != reset and clock in ordinals and reset in ordinals,
            "missing distinct clock/reset domain",
        )
        bindings = []
        for ordinal, signal in ((clock, "clk"), (reset, "rst")):
            _require(ordinals[ordinal]["width"] == 1, "domain port must be one bit")
            bindings.append(f".{_identifier(ordinals[ordinal]['wire'])}({signal})")
        data = [row for row in incoming if row["ordinal"] not in (clock, reset)]
        by_name = {row["name"]: row for row in data}
        _require(
            len(data) == len(by_name) == len(self.inputs), "input inventory mismatch"
        )
        _require(
            set(by_name) == {row["name"] for row in self.inputs}, "input names mismatch"
        )
        for index, (row, type_) in enumerate(
            zip(self.inputs, self.input_types, strict=True)
        ):
            actual = by_name[row["name"]]
            _require(actual["width"] == type_[1], "input width mismatch")
            bindings.append(f".{_identifier(actual['wire'])}(i{index})")
        by_name = {row["name"]: row for row in ports["outputs"]}
        _require(
            len(by_name) == len(ports["outputs"]) == len(self.outputs),
            "output inventory mismatch",
        )
        _require(
            set(by_name) == {row["name"] for row in self.outputs},
            "output names mismatch",
        )
        for index, row in enumerate(self.outputs):
            actual = by_name[row["name"]]
            _require(
                actual["width"] == self.output_widths[index]
                and actual["availability"] is None,
                "output width/availability mismatch",
            )
            bindings.append(f".{_identifier(actual['wire'])}(o{index})")
        self.rtl_files = []
        for row in manifest["files"]:
            if row["role"] == "rtl":
                path = (self.rtl_dir / row["path"]).resolve()
                _require(
                    path.is_relative_to(self.rtl_dir) and path.is_file(),
                    "invalid RTL closure path",
                )
                self.rtl_files.append(path)
        _require(
            bool(self.rtl_files) and len(set(self.rtl_files)) == len(self.rtl_files),
            "empty or duplicate RTL closure",
        )
        ports_text = ["input wire clk, rst"]
        ports_text += [
            "input " + _declaration(t[1], f"i{i}")
            for i, t in enumerate(self.input_types)
        ]
        ports_text += [
            "output " + _declaration(width, f"o{i}")
            for i, width in enumerate(self.output_widths)
        ]
        self.wrapper_path = self.work_dir / "observed_dut.sv"
        self.wrapper_path.write_text(
            "module observed_dut("
            + ", ".join(ports_text)
            + ");\n  "
            + _identifier(manifest["root_rtl_name"])
            + "raw_dut("
            + ", ".join(bindings)
            + ");\nendmodule\n"
        )
        self._bind_state()

    def _bind_state(self):
        mapping = json.loads((self.rtl_dir / "rtl-names.json").read_text())
        _require(
            mapping.get("kind") == "pycircuit.rtl-names"
            and mapping.get("version") == 1,
            "unsupported RTL state mapping",
        )
        entry = mapping.get("state_mapping", {})
        _require(
            entry.get("version") == 1 and entry.get("definition") == self.definition,
            "state mapping definition/version mismatch",
        )
        definitions = [
            row
            for row in mapping["definitions"]
            if row["definition"] == self.definition
        ]
        _require(len(definitions) == 1, "missing or duplicate state mapping definition")
        rows = definitions[0].get("storage", [])
        owners = {row["owner"]: row for row in rows}
        _require(
            len(owners) == len(rows) == len(self.registers)
            and set(owners) == set(self.owner_keys),
            "state mapping must cover each source owner exactly once",
        )
        self.state_paths = []
        for register, key in zip(self.registers, self.owner_keys, strict=True):
            row = owners[key]
            _require(
                row["name"] == register["name"]
                and row["width"] == register["width"]
                and row["kind"] in ("dff", "dffe"),
                "state mapping name/width/kind mismatch",
            )
            _require(
                isinstance(row["path"], list) and len(row["path"]) == 2,
                "unsupported state path",
            )
            components = [entry["root_instance"], *row["path"]]
            _require(
                all(
                    isinstance(part, str)
                    and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", part)
                    for part in components
                ),
                "unsupported state path identifier",
            )
            self.state_paths.append("dut.raw_dut." + ".".join(components))
        _require(
            len(set(self.state_paths)) == len(self.state_paths),
            "duplicate physical state path",
        )

    def _reference(self):
        ports = ["input wire clk, rst"]
        ports += [
            "input " + _declaration(t[1], f"i{i}")
            for i, t in enumerate(self.input_types)
        ]
        ports += [
            "output " + _declaration(width, f"o{i}")
            for i, width in enumerate(self.output_widths)
        ]
        lines = ["module rule_reference(" + ", ".join(ports) + ");"]
        lines += [
            "  " + _declaration(w, f"r{i}", "reg") + ";"
            for i, w in enumerate(self.widths)
        ]
        lines += self._wires
        lines += [
            f"  assign o{i} = {wire};" for i, wire in enumerate(self.output_wires)
        ]
        lines += ["  always @(posedge clk) begin"]
        for i, (width, initial, next_wire) in enumerate(
            zip(self.widths, self.initials, self.next_wires, strict=True)
        ):
            lines.append(
                f"    if (rst) r{i} <= {width}'d{initial}; else r{i} <= {next_wire};"
            )
        lines += ["  end", "endmodule", ""]
        self.reference_path.write_text("\n".join(lines))

    def _miter(self):
        ports = ["input wire clk, rst"]
        ports += [
            "input " + _declaration(t[1], f"i{i}")
            for i, t in enumerate(self.input_types)
        ]
        for side in ("dut", "ref"):
            ports += [
                "output " + _declaration(w, f"{side}_r{i}")
                for i, w in enumerate(self.widths)
            ]
            ports += [
                "output " + _declaration(width, f"{side}_o{i}")
                for i, width in enumerate(self.output_widths)
            ]
        ports += ["output wire related, matched"]
        lines = ["module equivalence(" + ", ".join(ports) + ");"]
        for side, module in (("dut", "observed_dut"), ("ref", "rule_reference")):
            bindings = [".clk(clk)", ".rst(rst)"]
            bindings += [f".i{i}(i{i})" for i in range(len(self.inputs))]
            bindings += [f".o{i}({side}_o{i})" for i in range(len(self.outputs))]
            lines.append(f"  {module} {side}(" + ", ".join(bindings) + ");")
        state_checks = [f"(dut_r{i} == ref_r{i})" for i in range(len(self.registers))]
        output_checks = [f"(dut_o{i} == ref_o{i})" for i in range(len(self.outputs))]
        lines += [
            "  assign related = " + " && ".join(state_checks) + ";",
            "  assign matched = related && " + " && ".join(output_checks) + ";",
            "endmodule",
            "",
        ]
        self.miter_path = self.work_dir / "equivalence.sv"
        self.miter_path.write_text("\n".join(lines))

    def _path(self, path):
        return json.dumps(Path(path).resolve().relative_to(self.work_dir).as_posix())

    def _yosys(self, label, script):
        path = self.work_dir / f"{label}.ys"
        path.write_text(script + "\n")
        return self.run(label, [self.yosys_tool, "-s", path.name], cwd=self.work_dir)

    def _audit(self, path):
        modules = json.loads(path.read_text())["modules"]
        _require(
            set(modules) == {"equivalence"}, "normalization did not close hierarchy"
        )
        top = modules["equivalence"]
        _require(
            not top.get("memories") and not top.get("processes"),
            "unlowered memory/process",
        )
        for obj in [top, *top["netnames"].values(), *top["cells"].values()]:
            _require(
                "init" not in obj.get("attributes", {}), "initial constraint survived"
            )
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
        banks = []
        for cell in top["cells"].values():
            _require(cell["type"] in allowed, "unsupported normalized cell")
            for bits in cell["connections"].values():
                _require(
                    all(type(bit) is int or bit in ("0", "1") for bit in bits),
                    "unknown constant in normalized circuit",
                )
            if cell["type"] == "$dff":
                _require(
                    int(cell["parameters"]["CLK_POLARITY"], 2) == 1,
                    "non-positive clock",
                )
                _require(
                    cell["connections"]["CLK"] == top["ports"]["clk"]["bits"],
                    "alternate clock",
                )
                _require(
                    int(cell["parameters"]["WIDTH"], 2)
                    == len(cell["connections"]["Q"]),
                    "DFF width mismatch",
                )
                banks.append(tuple(cell["connections"]["Q"]))
        expected_banks = []
        for side in ("dut", "ref"):
            for register, width in enumerate(self.widths):
                bits = tuple(top["ports"][f"{side}_r{register}"]["bits"])
                _require(
                    len(bits) == width and all(type(bit) is int for bit in bits),
                    "state observation width/constant mismatch",
                )
                _require(
                    banks.count(bits) == 1,
                    "ordered mapped state bits must equal one DFF Q bank",
                )
                path = (
                    self.state_paths[register] if side == "dut" else f"ref.r{register}"
                )
                _require(
                    path in top["netnames"]
                    and tuple(top["netnames"][path]["bits"]) == bits,
                    "state observation differs from mapped physical net",
                )
                expected_banks.append(bits)
            for index, width in enumerate(self.output_widths):
                output_bits = top["ports"][f"{side}_o{index}"]["bits"]
                _require(
                    len(output_bits) == width
                    and all(
                        type(bit) is int or bit in ("0", "1") for bit in output_bits
                    ),
                    "public output has invalid width or unknown bits",
                )
        bits = [bit for bank in expected_banks for bit in bank]
        _require(
            len(set(bits)) == len(bits) and sorted(banks) == sorted(expected_banks),
            "extra or overlapping state",
        )
        return {
            "banks": len(banks),
            "state_bits": len(bits),
            "clock": "positive clk",
            "initial_constraints": [],
            "public_outputs": len(self.outputs),
        }

    def prepare(self):
        self._load_model()
        self._bind_ports()
        self._reference()
        self._miter()
        sources = [
            *self.rtl_files,
            self.wrapper_path,
            self.reference_path,
            self.miter_path,
        ]
        netlist = self.work_dir / "normalized.json"
        observations = "cd equivalence\n"
        for register, path in enumerate(self.state_paths):
            observations += f"connect -set dut_r{register} \\{path}\n"
            observations += f"connect -set ref_r{register} \\ref.r{register}\n"
        observations += "cd ..\n"
        self._yosys(
            "normalize",
            "read_verilog -sv -D SYNTHESIS "
            + " ".join(self._path(path) for path in sources)
            + "\nhierarchy -check -top equivalence\nproc -noopt\nflatten -noscopeinfo\n"
            + observations
            + "setattr -unset init\nsetattr -mod -unset init\nopt_clean\ndffunmap\nopt_clean\ncheck -assert\n"
            + f"write_rtlil {self._path(self.normalized_path)}\nwrite_json {self._path(netlist)}",
        )
        return self._audit(netlist)

    def _show(self):
        signals = ["related", "matched"] + [f"i{i}" for i in range(len(self.inputs))]
        for side in ("dut", "ref"):
            signals += [f"{side}_r{i}" for i in range(len(self.registers))]
            signals += [f"{side}_o{i}" for i in range(len(self.outputs))]
        return " ".join("-show " + signal for signal in signals)

    def _read(self):
        return f"read_rtlil {self._path(self.normalized_path)}\n"

    def prove(self):
        result = self._yosys(
            "step-proof",
            self._read()
            + "sat -seq 2 -set rst 0 -set-at 1 related 1 -prove matched 1 -verify "
            + self._show(),
        )
        assert "SAT proof finished - no model found: SUCCESS!" in result
        return result

    def witness(self):
        constraints = ""
        for index, width in enumerate(self.widths):
            value = (1 << width) - 1
            constraints += f" -set dut_r{index} {value} -set ref_r{index} {value}"
        transcript = self._yosys(
            "arbitrary-state-witness",
            self._read()
            + "sat -seq 1 -set rst 0 -set related 1"
            + constraints
            + " "
            + self._show(),
        )
        values = _sat_values(transcript)
        for index, width in enumerate(self.widths):
            assert (
                values[1, f"dut_r{index}"]
                == values[1, f"ref_r{index}"]
                == (1 << width) - 1
            )
        assert values[1, "related"] == values[1, "matched"] == 1
        return values

    def counterexample(self, states, inputs):
        _require(
            len(states) == len(self.registers) and len(inputs) == len(self.inputs),
            "counterexample binding arity",
        )
        constraints = ""
        for index, (value, width) in enumerate(zip(states, self.widths, strict=True)):
            _require(
                _natural(value) and value.bit_length() <= width,
                "counterexample state width",
            )
            constraints += (
                f" -set-at 1 dut_r{index} {value} -set-at 1 ref_r{index} {value}"
            )
        for index, (value, type_) in enumerate(
            zip(inputs, self.input_types, strict=True)
        ):
            _require(
                _natural(value) and value.bit_length() <= type_[1],
                "counterexample input width",
            )
            constraints += f" -set-at 1 i{index} {value}"
        transcript = self._yosys(
            "semantic-counterexample",
            self._read()
            + "sat -seq 2 -set rst 0 -set-at 1 related 1"
            + constraints
            + " -prove matched 1 -prove-skip 1 "
            + self._show(),
        )
        assert "SAT proof finished - model found: FAIL!" in transcript
        values = _sat_values(transcript)
        assert values[1, "related"] == 1 and values[2, "matched"] == 0
        for index, value in enumerate(states):
            assert values[1, f"dut_r{index}"] == values[1, f"ref_r{index}"] == value
        for index, value in enumerate(inputs):
            assert values[1, f"i{index}"] == value
        return values
