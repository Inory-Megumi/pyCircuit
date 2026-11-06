"""A borrowed field does not reconstruct unrelated wide data in every iteration."""

from pathlib import Path

import pytest
from test_physical_rtl_export import simulate
from test_source_system_execution import _cli, _ok

pytestmark = pytest.mark.system

SOURCE = """import pycircuit as ac
@ac.struct
class Config:
    flags: ac.u32
    unrelated: ac.bits[4096]

def select_low(cfg: Config) -> ac.u8:
    answer: ac.u8 = 0
    for lane in range(8):
        if cfg.flags[lane]:
            one: ac.u8 = 1
            amount: ac.u3 = lane
            answer = answer | (one << amount)
    return answer

@ac.module
def Projection(cfg: Config) -> ac.u8:
    @ac.rule
    def project() -> ac.u8:
        return select_low(cfg)
    return project
"""


def test_bounded_projection_preserves_selected_bits(tmp_path: Path):
    source = tmp_path / "projection.py"
    source.write_text(SOURCE)
    unit, final = tmp_path / "unit", tmp_path / "final.ac"
    _ok(
        _cli(
            "compile",
            "-c",
            str(source),
            "--source-root",
            str(tmp_path),
            "-o",
            str(unit),
        )
    )
    _ok(_cli("link", str(unit), "--top", "projection.Projection", "-o", str(final)))
    _ok(_cli("emit", str(final), "--target", "cpp", "-o", str(tmp_path / "cpp")))
    rtl = tmp_path / "rtl"
    _ok(
        _cli(
            "emit",
            str(final),
            "--target",
            "verilog",
            "--rtl-mode",
            "physical",
            "-o",
            str(rtl),
        )
    )
    transcript = simulate(
        rtl,
        tmp_path,
        """
edge_up();
if(result_0 !== 8'ha5) $fatal(1,"low selected bits");
edge_down(); cfg={32'h5678003c,{4096{1'bz}}}; edge_up();
if(result_0 !== 8'h3c) $fatal(1,"unrelated high payload");
""",
        initialize="cfg={32'h123400a5,{4096{1'bx}}};",
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript
