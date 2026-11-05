"""Shared, bounded validation of the exported typed Rule transition format."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


class ValidationProfileError(ValueError):
    """The artifact is outside the supported verification profile."""


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


class RuleFormula:
    """One format/type checker shared by SV, SMT and witness emission."""

    @classmethod
    def load(cls, path):
        path = Path(path)
        _require(path.stat().st_size <= 8 * 1024 * 1024, "formula too large")
        raw = path.read_bytes()
        result = cls(json.loads(raw))
        result.sha256 = hashlib.sha256(raw).hexdigest()
        return result

    def __init__(self, model):
        _require(
            isinstance(model, dict)
            and set(model)
            == {"schema", "definition", "inputs", "registers", "outputs", "next"}
            and model["schema"] == "pycircuit-rule-transition-v2"
            and isinstance(model["definition"], str)
            and bool(model["definition"]),
            "unsupported formula schema",
        )
        self.data = model
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
                set(row) == {"name", "type", "term"}, "invalid output expression row"
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
        budget = [0, 0]
        for node, width in zip(model["next"], self.widths, strict=True):
            _require(
                self.fold(node, budget=budget)[0] == ("bits", width),
                "next-state type differs from register",
            )
        for row, width in zip(self.outputs, self.output_widths, strict=True):
            _require(
                self.fold(row["term"], budget=budget)[0] == ("bits", width),
                "public output term type mismatch",
            )
        self.term_visits, self.bit_work = budget

    def fold(self, node, render=None, *, allow_inputs=True, budget=None):
        """Validate once per fold, then render checked nodes bottom-up."""
        budget = [0, 0] if budget is None else budget

        def visit(node, depth):
            budget[0] += 1
            _require(
                budget[0] <= 100000 and depth <= 256, "formula expansion limit exceeded"
            )
            _require(
                isinstance(node, dict) and "op" in node and "type" in node,
                "invalid term",
            )
            result = _type(node["type"])
            budget[1] += result[1]
            _require(budget[1] <= 1000000, "formula bit-work limit exceeded")
            op = node["op"]
            values = []
            if op in ("boolLit", "bitsLit"):
                _require(set(node) == {"op", "type", "value"}, "invalid literal term")
                if op == "boolLit":
                    _require(
                        result == ("bool", 1) and type(node["value"]) is bool,
                        "invalid Bool literal",
                    )
                else:
                    _require(result[0] == "bits", "invalid Bits literal type")
                    _decimal(node["value"], result[1])
            elif op in ("input", "read"):
                _require(
                    set(node) == {"op", "type", "index"} and _natural(node["index"]),
                    "invalid variable term",
                )
                _require(
                    op != "input" or allow_inputs, "state property cannot read inputs"
                )
                types = (
                    self.input_types
                    if op == "input"
                    else [("bits", w) for w in self.widths]
                )
                _require(
                    node["index"] < len(types) and types[node["index"]] == result,
                    "variable type/index mismatch",
                )
            else:
                arities = {
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
                    op in arities and set(node) == {"op", "type", "args"},
                    "unsupported term operation",
                )
                _require(
                    isinstance(node["args"], list) and len(node["args"]) == arities[op],
                    "term arity mismatch",
                )
                children = [visit(child, depth + 1) for child in node["args"]]
                types, values = zip(*children, strict=True)
                if op == "bit":
                    valid = result == ("bits", 1) and types == (("bool", 1),)
                elif op == "concat":
                    valid = all(t[0] == "bits" for t in types) and result == (
                        "bits",
                        sum(t[1] for t in types),
                    )
                elif op in ("add", "sub"):
                    valid = result[0] == "bits" and all(t == result for t in types)
                elif op in ("ult", "eq"):
                    valid = (
                        result == ("bool", 1)
                        and types[0] == types[1]
                        and (op == "eq" or types[0][0] == "bits")
                    )
                elif op in ("and", "not"):
                    valid = result == ("bool", 1) and all(t == result for t in types)
                else:
                    valid = types[0] == ("bool", 1) and types[1] == types[2] == result
                _require(valid, "term operand/result type mismatch")
            return result, render(node, result, values) if render is not None else None

        return visit(node, 0)
