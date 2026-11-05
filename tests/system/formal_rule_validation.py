"""Verification-only encoding of serialized Lean terms and emitted physical RTL."""

from __future__ import annotations

import json
import re
from pathlib import Path


class ValidationProfileError(ValueError):
    """The artifact cannot be checked by this explicitly bounded profile."""


def _require(condition, message):
    if not condition:
        raise ValidationProfileError(message)


def _natural(value):
    return type(value) is int and value >= 0


def _type(value):
    _require(isinstance(value, dict), "term type must be an object")
    if value == {"kind": "bool"}:
        return ("bool", 1)
    _require(set(value) == {"kind", "width"}, "unsupported term type")
    width = value["width"]
    _require(
        value["kind"] == "bits" and _natural(width) and 0 < width <= 4096,
        "Bits width outside validation profile",
    )
    return ("bits", width)


def _decimal(value, width):
    _require(
        isinstance(value, str) and re.fullmatch(r"0|[1-9][0-9]*", value),
        "unsigned literals must be canonical decimal strings",
    )
    _require(len(value) <= 1234, "literal outside validation width limit")
    integer = int(value)
    _require(integer.bit_length() <= width, "literal does not fit its width")
    return integer


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
        self._nodes = 0
        self._bit_work = 0
        self._wires = []

    def _load_model(self):
        _require(
            self.formula_path.stat().st_size <= 8 * 1024 * 1024, "formula too large"
        )
        model = json.loads(self.formula_path.read_text())
        _require(
            set(model)
            == {"schema", "definition", "inputs", "registers", "outputs", "next"}
            and model["schema"] == "pycircuit-rule-transition-v2"
            and isinstance(model["definition"], str)
            and bool(model["definition"]),
            "unsupported formula schema",
        )
        self.definition = model["definition"]
        self.inputs, self.registers, self.outputs = (
            model["inputs"],
            model["registers"],
            model["outputs"],
        )
        _require(
            isinstance(self.inputs, list)
            and isinstance(self.registers, list)
            and isinstance(self.outputs, list)
            and len(self.inputs) <= 64
            and 0 < len(self.registers) <= 64,
            "invalid finite interface inventory",
        )
        for rows in (self.inputs, self.registers, self.outputs):
            _require(
                all(
                    isinstance(row, dict) and isinstance(row.get("name"), str)
                    for row in rows
                ),
                "invalid named interface row",
            )
            names = [row["name"] for row in rows]
            _require(
                all(names) and len(set(names)) == len(names), "duplicate or empty names"
            )
        self.input_types = []
        for row in self.inputs:
            _require(set(row) == {"name", "type"}, "invalid input row")
            self.input_types.append(_type(row["type"]))
        self.widths, self.initials = [], []
        for row in self.registers:
            _require(
                set(row) == {"name", "owner", "width", "initial"},
                "invalid register row",
            )
            _require(
                isinstance(row["owner"], str) and bool(row["owner"]),
                "missing register owner",
            )
            width = _type({"kind": "bits", "width": row["width"]})[1]
            self.widths.append(width)
            self.initials.append(_decimal(row["initial"], width))
        self.owner_keys = [row["owner"] for row in self.registers]
        _require(
            len(set(self.owner_keys)) == len(self.owner_keys),
            "duplicate register owner",
        )
        self.output_widths = []
        for row in self.outputs:
            _require(
                set(row) == {"name", "type", "term"},
                "invalid output expression row",
            )
            type_ = _type(row["type"])
            _require(type_[0] == "bits", "public output must be packed Bits")
            self.output_widths.append(type_[1])
        _require(
            0 < len(self.outputs) <= 64 and sum(self.output_widths) <= 4096,
            "public output expansion exceeds validation profile",
        )
        _require(
            sum(self.widths) + sum(width for _, width in self.input_types) <= 4096,
            "combined state/input width exceeds validation profile",
        )
        _require(
            isinstance(model["next"], list)
            and len(model["next"]) == len(self.registers),
            "incomplete next-state vector",
        )
        terms = [self._term(node, 0) for node in model["next"]]
        for (type_, _), width in zip(terms, self.widths, strict=True):
            _require(type_ == ("bits", width), "next-state type differs from register")
        self.next_wires = [wire for _, wire in terms]
        self.output_wires = []
        for row, width in zip(self.outputs, self.output_widths, strict=True):
            type_, wire = self._term(row["term"], 0)
            _require(type_ == ("bits", width), "public output term type mismatch")
            self.output_wires.append(wire)

    def _term(self, node, depth):
        self._nodes += 1
        _require(
            self._nodes <= 100000 and depth <= 256, "formula expansion limit exceeded"
        )
        _require(
            isinstance(node, dict) and "op" in node and "type" in node, "invalid term"
        )
        result_type = _type(node["type"])
        self._bit_work += result_type[1]
        _require(self._bit_work <= 1000000, "formula bit-work limit exceeded")
        op = node["op"]
        if op in ("boolLit", "bitsLit"):
            _require(set(node) == {"op", "type", "value"}, "invalid literal term")
            if op == "boolLit":
                _require(
                    result_type == ("bool", 1) and type(node["value"]) is bool,
                    "invalid Bool literal",
                )
                expression = "1'b1" if node["value"] else "1'b0"
            else:
                _require(result_type[0] == "bits", "invalid Bits literal type")
                expression = (
                    f"{result_type[1]}'d{_decimal(node['value'], result_type[1])}"
                )
        elif op in ("input", "read"):
            _require(
                set(node) == {"op", "type", "index"} and _natural(node["index"]),
                "invalid variable term",
            )
            index = node["index"]
            types = (
                self.input_types
                if op == "input"
                else [("bits", width) for width in self.widths]
            )
            _require(
                index < len(types) and types[index] == result_type,
                "variable type/index mismatch",
            )
            return result_type, f"i{index}" if op == "input" else f"r{index}"
        else:
            arity = {
                "add": 2,
                "sub": 2,
                "ult": 2,
                "eq": 2,
                "and": 2,
                "not": 1,
                "ite": 3,
                "bit": 1,
                "concat": 2,
            }
            _require(
                op in arity and set(node) == {"op", "type", "args"},
                "unsupported term operation",
            )
            _require(
                isinstance(node["args"], list) and len(node["args"]) == arity[op],
                "term arity mismatch",
            )
            children = [self._term(child, depth + 1) for child in node["args"]]
            types, values = zip(*children, strict=True)
            if op == "bit":
                _require(
                    result_type == ("bits", 1) and types == (("bool", 1),),
                    "Boolean payload type mismatch",
                )
                expression = values[0]
            elif op == "concat":
                _require(
                    all(t[0] == "bits" for t in types)
                    and result_type == ("bits", sum(t[1] for t in types)),
                    "concatenation width/type mismatch",
                )
                expression = "{" + ", ".join(values) + "}"
            elif op in ("add", "sub"):
                _require(
                    result_type[0] == "bits" and all(t == result_type for t in types),
                    "arithmetic type mismatch",
                )
                expression = f"({values[0]} {'+' if op == 'add' else '-'} {values[1]})"
            elif op in ("ult", "eq"):
                _require(
                    result_type == ("bool", 1) and types[0] == types[1],
                    "comparison type mismatch",
                )
                _require(
                    op == "eq" or types[0][0] == "bits",
                    "unsigned comparison requires Bits",
                )
                expression = f"({values[0]} {'<' if op == 'ult' else '=='} {values[1]})"
            elif op in ("and", "not"):
                _require(
                    result_type == ("bool", 1) and all(t == result_type for t in types),
                    "Boolean type mismatch",
                )
                expression = (
                    f"({values[0]} && {values[1]})"
                    if op == "and"
                    else f"(!{values[0]})"
                )
            else:
                _require(
                    types[0] == ("bool", 1) and types[1] == types[2] == result_type,
                    "conditional type mismatch",
                )
                expression = f"({values[0]} ? {values[1]} : {values[2]})"
        name = f"n{len(self._wires)}"
        self._wires.append(f"  {_declaration(result_type[1], name)} = {expression};")
        return result_type, name

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
