"""Pairwise least-recently-served order, expanded to ordinary native methods."""

import ast


def lru_definition(config):
    """Keep a triangular age matrix and move a committed winner to youngest."""
    name, count, index_type = config.name, config.inputs, config.index_type
    mask_type = f"ac.bits[{count}]"
    pairs = [(left, right) for left in range(count) for right in range(left + 1, count)]
    positions = {pair: bit for bit, pair in enumerate(pairs)}
    width = len(pairs)
    age_type = f"ac.bits[{width}]"
    choose, update = name + "_select", name + "_served"
    age_argument = f", age: {age_type}" if width else ""
    lines = [f"def {choose}(candidates: {mask_type}{age_argument}) -> {mask_type}:"]
    for index in range(count):
        conditions = [f"candidates[{index}:{index + 1}]"]
        for other in range(count):
            if other == index:
                continue
            bit = positions[min(index, other), max(index, other)]
            older = (
                f"age[{bit}:{bit + 1}]" if index < other else f"~age[{bit}:{bit + 1}]"
            )
            conditions.append(f"(~candidates[{other}:{other + 1}] | {older})")
        lines += [f"    selected{index}: ac.u1 = " + " & ".join(conditions)]
    selected_bits = ", ".join(f"selected{index}" for index in reversed(range(count)))
    lines += [f"    return ac.concat({selected_bits})", ""]
    if width:
        lines += [
            f"def {update}(age: {age_type}, selected: {mask_type}) -> {age_type}:"
        ]
        for bit, (left, right) in enumerate(pairs):
            # Winner on the left clears this relation; winner on the right sets
            # it. Otherwise the old relation survives unchanged.
            lines += [
                f"    older{left}_{right}: ac.u1 = "
                f"(age[{bit}:{bit + 1}] | selected[{right}:{right + 1}]) & ~selected[{left}:{left + 1}]"
            ]
        age_bits = ", ".join(f"older{left}_{right}" for left, right in reversed(pairs))
        lines += [f"    return ac.concat({age_bits})", ""]
    lines += ["@ac.module", f"def {name}():"]
    if width:
        # All queries observe committed age, including a query after grant.
        lines += [
            f"    age_order: {age_type} = {(1 << width) - 1}",
            "    age_snapshot = age_order",
        ]
    arguments = "candidates, age_snapshot" if width else "candidates"
    lines += [
        "",
        "    @ac.method",
        f"    def select(candidates: {mask_type}) -> {mask_type}:",
        f"        return {choose}({arguments})",
        "",
        "    @ac.method(guard=lambda candidates: candidates != 0)",
        f"    def grant(candidates: {mask_type}) -> {index_type}:",
        f"        selected = {choose}({arguments})",
    ]
    if count == 1:
        lines += [f"        index: {index_type} = 0"]
    else:
        lines += ['        index, nonempty = ac.priority_encode(selected, order="low")']
    if width:
        lines += [f"        age_order = {update}(age_snapshot, selected)"]
    lines += ["        return index"]
    return ast.parse("\n".join(lines) + "\n").body


def constant_select(config, mask):
    """Fold a literal zero/one/two-candidate query using its exact age relation."""
    active = [index for index in range(config.inputs) if mask & (1 << index)]
    method = "select_mask_" + str(mask)
    result = str(mask)
    if len(active) == 2:
        left, right = active
        pairs = [
            (i, j) for i in range(config.inputs) for j in range(i + 1, config.inputs)
        ]
        bit = pairs.index((left, right))
        result = f"{1 << left} if age_snapshot[{bit}:{bit + 1}] else {1 << right}"
    source = (
        f"@ac.method\ndef {method}() -> ac.bits[{config.inputs}]:\n"
        f"    return {result}\n"
    )
    return ast.parse(source).body[0]
