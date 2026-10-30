"""Select the plain hardware branches of installed Runtime source inputs.

This never reads or changes native-generated DUT RTL. Unknown macro conditions
remain in the library source for the SystemVerilog preprocessor to decide.
SYNTHESIS and the internal PYCIRCUIT_PLAIN_RTL export macro are defined; the
ordinary library ABI and kernel remain available when the latter is absent.
"""

from __future__ import annotations

import re

_CONDITIONAL = re.compile(r"^\s*`(ifdef|ifndef|else|endif|elsif)\b(.*)$")


def synthesis_runtime_source(source: str) -> str:
    result: list[str] = []
    # parent active, known profile test, branch active, else seen
    stack: list[tuple[bool, bool, bool, bool]] = []
    active = True
    for line in source.splitlines(keepends=True):
        match = _CONDITIONAL.match(line)
        if match is None:
            if active:
                if re.match(
                    r"^\s*`(?:define|undef)\s+(?:SYNTHESIS|PYCIRCUIT_PLAIN_RTL)\b", line
                ):
                    raise ValueError("Runtime profile cannot redefine an export macro")
                result.append(line)
            continue
        directive, tail = match.groups()
        if directive in ("ifdef", "ifndef"):
            macro = tail.strip().split()[0] if tail.strip() else ""
            if not macro:
                raise ValueError("Runtime conditional lacks a macro name")
            known = macro in ("SYNTHESIS", "PYCIRCUIT_PLAIN_RTL")
            selected = directive == "ifdef" if known else True
            stack.append((active, known, selected, False))
            if active and not known:
                result.append(line)
            active = active and selected
        elif directive == "else":
            if not stack or stack[-1][3]:
                raise ValueError("Runtime conditional has unmatched or duplicate else")
            parent, known, selected, _ = stack[-1]
            stack[-1] = parent, known, not selected if known else True, True
            if parent and not known:
                result.append(line)
            active = parent and (not selected if known else True)
        elif directive == "elsif":
            if not stack or stack[-1][1]:
                raise ValueError(
                    "Runtime profile requires an explicit nested macro condition"
                )
            if active:
                result.append(line)
        else:
            if not stack:
                raise ValueError("Runtime conditional has unmatched endif")
            parent, known, _, _ = stack.pop()
            if parent and not known:
                result.append(line)
            active = parent
    if stack:
        raise ValueError("Runtime conditional is unterminated")
    return "".join(result)
