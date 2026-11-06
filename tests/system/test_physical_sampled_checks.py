"""Physical checks preserve sampled admission and whole-root failure atomicity."""

import pytest
from test_physical_rtl_export import simulate
from test_source_system_execution import _cli, _ok

pytestmark = pytest.mark.system

SOURCE = """import pycircuit as ac
@ac.module
def CheckedUpdate(enabled: bool, accepted: bool, incoming: ac.u8) -> tuple[ac.u8, ac.u8]:
    saved: ac.u8 = 0
    count: ac.u8 = 0
    @ac.rule(guard=lambda: enabled)
    def update() -> None:
        assert accepted
        saved = incoming
    @ac.rule
    def independent() -> None:
        count = count + 1
    return saved, count

@ac.module
def AssertionChild(accepted: bool, incoming: ac.u8) -> ac.u8:
    saved: ac.u8 = 0
    @ac.rule
    def update() -> None:
        assert accepted
        saved = incoming
    return saved

@ac.module
def CheckedHierarchy(accepted: bool, incoming: ac.u8) -> tuple[ac.u8, ac.u8]:
    child = AssertionChild(accepted, incoming)
    count: ac.u8 = 0
    @ac.rule
    def independent() -> None:
        count = count + 1
    return child, count

@ac.module
def Capture(incoming: ac.u8) -> ac.u8:
    saved: ac.u8 = 0
    prepared = incoming + 1
    @ac.method
    def capture() -> None:
        saved = prepared
    return saved

@ac.module
def MethodCapture(incoming: ac.u8, enabled: bool) -> ac.u8:
    child = Capture(incoming)
    @ac.rule(guard=lambda: enabled)
    def accept() -> None:
        child.capture()
    return child

@ac.module
def Producer(enabled: bool, data: ac.u8) -> ac.u8:
    @ac.rule(guard=lambda: enabled)
    def offer() -> ac.u8:
        return data
    return offer

@ac.module
def Consumer(data: ac.u8, take: bool) -> ac.u8:
    saved: ac.u8 = 0
    @ac.rule(guard=lambda: take)
    def store() -> None:
        saved = data
    return saved

@ac.module
def Sibling() -> ac.u8:
    ticks: ac.u8 = 0
    @ac.rule
    def advance() -> None:
        ticks = ticks + 1
    return ticks

@ac.module
def Availability(enabled: bool, choose: bool, take: bool, data: ac.u8) -> tuple[ac.u8, ac.u8]:
    offered = Producer(enabled, data)
    selected = offered if choose else data
    return Consumer(selected, take), Sibling()
"""


@pytest.fixture(scope="module")
def sampled_designs(tmp_path_factory):
    root = tmp_path_factory.mktemp("sampled-physical")
    source = root / "design.py"
    source.write_text(SOURCE)
    unit = root / "unit"
    _ok(_cli("compile", "-c", str(source), "--source-root", str(root), "-o", str(unit)))
    designs = {}
    for name in ("CheckedUpdate", "CheckedHierarchy", "MethodCapture", "Availability"):
        final, output = root / (name + ".ac"), root / name
        _ok(_cli("link", str(unit), "--top", "design." + name, "-o", str(final)))
        _ok(
            _cli(
                "emit",
                str(final),
                "--target",
                "verilog",
                "--rtl-mode",
                "physical",
                "-o",
                str(output),
            )
        )
        designs[name] = output
    return designs


@pytest.mark.parametrize(
    "design,fault", [("CheckedUpdate", "0"), ("CheckedHierarchy", "x")]
)
def test_assertion_masks_reset_and_freezes_siblings(
    sampled_designs, tmp_path, design, fault
):
    inactive = ""
    enabled = ""
    if design == "CheckedUpdate":
        enabled = "enabled=1;"
        inactive = """
edge_down(); enabled=0; accepted=1'bx; edge_up();
if(result_0!==8'h12 || result_1!==2) $fatal(1,"inactive assertion");
enabled=1;
"""
    body = (
        """
accepted=1;edge_up();
if(result_0!==8'h12 || result_1!==1) $fatal(1,"accepted update");
"""
        + inactive
        + """
edge_down(); rst=1; accepted=1'bx; edge_up();
if(result_0!==0 || result_1!==0) $fatal(1,"reset masks assertion");
edge_down(); rst=0; accepted=1; incoming=8'h22; edge_up();
if(result_0!==8'h22 || result_1!==1) $fatal(1,"resume");
edge_down(); accepted=1'bFAULT; incoming=8'h33; edge_up();
if(result_0!==8'h22 || result_1!==1) $fatal(1,"failure committed an owner");
edge_down(); accepted=1; rst=1; edge_up();
if(result_0!==8'h22 || result_1!==1) $fatal(1,"failure was not sticky");
""".replace(
            "FAULT", fault
        )
    )
    log = simulate(
        sampled_designs[design],
        tmp_path,
        body,
        initialize=enabled + "accepted=1'bx;incoming=8'h12;",
    )
    assert log.count("PYCIRCUIT_PHYSICAL_FAULT") == 1


def test_method_capture_uses_the_parent_sampling_edge(sampled_designs, tmp_path):
    log = simulate(
        sampled_designs["MethodCapture"],
        tmp_path,
        """
if(result_0!==0) $fatal(1,"reset");
edge_up(); if(result_0!==8'h13) $fatal(1,"captured input expression");
incoming=8'h40; #2;
if(result_0!==8'h13) $fatal(1,"changed without an edge");
edge_down(); enabled=0; edge_up();
if(result_0!==8'h13) $fatal(1,"disabled parent rule");
edge_down(); enabled=1; edge_up();
if(result_0!==8'h41) $fatal(1,"new capture");
""",
        initialize="incoming=8'h12;enabled=1;",
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in log


def test_value_availability_stalls_only_its_consumer(sampled_designs, tmp_path):
    log = simulate(
        sampled_designs["Availability"],
        tmp_path,
        """
edge_up(); if(result_0!==8'h25 || result_1!==1) $fatal(1,"available");
edge_down(); enabled=0; data=8'h66; edge_up();
if(result_0!==8'h25 || result_1!==2) $fatal(1,"unavailable consumer");
edge_down(); choose=0; data=8'h37; edge_up();
if(result_0!==8'h37 || result_1!==3) $fatal(1,"total fallback");
edge_down(); enabled=1; choose=1; data=8'b10xz0101; edge_up();
if(result_0!==8'b10xz0101 || result_1!==4) $fatal(1,"available unknown data");
edge_down(); enabled=0; choose=1'bx; take=0; edge_up();
if(result_0!==8'b10xz0101 || result_1!==5) $fatal(1,"inactive requirement");
edge_down(); rst=1; choose=1'bz; take=1; edge_up();
if(result_0!==0 || result_1!==0) $fatal(1,"reset masks requirement");
""",
        initialize="enabled=1;choose=1;take=1;data=8'h25;",
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in log


@pytest.mark.parametrize("unknown", ["x", "z"])
def test_reached_unknown_availability_freezes_the_root(
    sampled_designs, tmp_path, unknown
):
    body = """
edge_up(); if(result_0!==8'h25 || result_1!==1) $fatal(1,"first update");
edge_down(); enabled=0; choose=1'bUNKNOWN; data=8'h66; edge_up();
if(result_0!==8'h25 || result_1!==1) $fatal(1,"unknown availability committed");
edge_down(); enabled=1; choose=1; edge_up();
if(result_0!==8'h25 || result_1!==1) $fatal(1,"fault was not sticky");
""".replace(
        "UNKNOWN", unknown
    )
    log = simulate(
        sampled_designs["Availability"],
        tmp_path,
        body,
        initialize="enabled=1;choose=1;take=1;data=8'h25;",
    )
    assert log.count("PYCIRCUIT_PHYSICAL_FAULT") == 1
