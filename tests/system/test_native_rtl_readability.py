"""Native source ownership and private transport remain readable in hardware RTL."""

import json
import re
from pathlib import Path

import pytest
from test_native_actions import _compile_pipe
from test_physical_rtl_readability import simulate
from test_scalar_generic_modules import _link
from test_source_system_execution import _cli, _compile, _ok, _run

pytestmark = pytest.mark.system


@pytest.mark.parametrize("depth", [1, 3])
def test_native_pipeline_synthesis_keeps_rule_structure_and_fifo_behavior(
    tmp_path, depth
):
    repository = Path(__file__).resolve().parents[2]
    pipe = _compile_pipe(tmp_path)
    source = tmp_path / "source"
    source.mkdir()
    (source / "pipeline.py").write_bytes(
        (repository / "examples/native_actions/pipeline.py").read_bytes()
    )
    (source / "top.py").write_text(
        "import pycircuit as ac\nfrom checks.pipeline import Pipeline\n"
        "@ac.module\ndef PipelineTop(source_enable: ac.u1, sink_enable: ac.u1) -> tuple[ac.u8, ac.u8]:\n"
        f"    last, count = Pipeline(source_enable, sink_enable, Depth={depth})\n"
        "    return last, count\n"
    )
    pipeline, top, final = (
        tmp_path / "pipeline-unit",
        tmp_path / "top-unit",
        tmp_path / "pipeline.ac",
    )
    _ok(_compile(source, "pipeline.py", pipeline, [pipe]))
    _ok(_compile(source, "top.py", top, [pipe, pipeline]))
    _ok(_link([pipe, pipeline, top], "checks.top.PipelineTop", final))
    original = final.read_bytes()
    output = tmp_path / "rtl"
    _ok(
        _cli(
            "emit",
            str(final),
            "--target",
            "verilog",
            "--rtl-mode",
            "synthesis",
            "-o",
            str(output),
        )
    )
    assert final.read_bytes() == original
    manifest = json.loads((output / "generated.json").read_text())
    files = [
        output / row["path"]
        for row in manifest["files"]
        if row["path"].endswith((".v", ".sv"))
    ]
    rtl = "\n".join(path.read_text() for path in files)
    assert not re.search(r"\binitial\b|__checks|pyc_phase|\bdffe\s*#", rtl)
    assert not re.search(r"\b(?:argument|capture)_\d+\b", rtl)
    for name in ("first", "second", "third"):
        assert f"{name}_tokens_push_data" in rtl
        assert f"{name}_tokens_pop" in rtl
    for name in ("produce", "double", "transform", "consume"):
        assert f"Source rule: {name}." in rtl
    _ok(
        _run(
            [
                "slang",
                "--top",
                manifest["root_rtl_name"],
                *map(str, sorted(files, key=lambda path: path.name != "design_top.sv")),
            ]
        )
    )

    # Old-state FIFO oracle: every transfer observes the token before the edge.
    stages = [[], [], []]
    next_input = last = count = 0
    body = "rst=1;step();rst=0;\n"
    for cycle in range(68):
        source_enabled = cycle not in (2, 8, 25)
        sink_enabled = not 4 <= cycle < 20
        body += (
            f"source_enable={int(source_enabled)};sink_enable={int(sink_enabled)};#1;"
        )
        body += f"if(result_0!==8'd{last} || result_1!==8'd{count})$fatal(1,\"cycle {cycle}\");step();\n"
        takes = [False, False, bool(stages[2]) and sink_enabled]
        takes[1] = bool(stages[1]) and (len(stages[2]) < depth or takes[2])
        takes[0] = bool(stages[0]) and (len(stages[1]) < depth or takes[1])
        produce = source_enabled and (len(stages[0]) < depth or takes[0])
        incoming = [
            (next_input + 1) % 256 if produce else None,
            (stages[0][0] * 2) % 256 if takes[0] else None,
            stages[1][0] ^ 0x55 if takes[1] else None,
        ]
        if takes[2]:
            last, count = stages[2][0], (count + 1) % 256
        for index, take in enumerate(takes):
            if take:
                stages[index].pop(0)
            if incoming[index] is not None:
                stages[index].append(incoming[index])
        next_input = (next_input + int(produce)) % 256
    simulate(output, tmp_path, body, verilator=True)
