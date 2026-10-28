TEST_F(SourceTransactionCaptureTest, ComposeReadyMustBeUnconditionalAndWellTyped) {
    const std::array<std::pair<std::string, std::string>, 6> changes = {{
        {"        ops.take.ready = old != 0", "        if old != 0:\n            ops.take.ready = True"},
        {"        ops.take.ready = old != 0", "        saved = old\n        ops.take.ready = old != 0"},
        {"        ops.take.ready = old != 0", "        ops.take.ready = True\n        ops.take.ready = old != 0"},
        {"        ops.take.ready = old != 0", "        ops.take.ready = old"},
        {"        ops.take.ready = old != 0", "        ops.take.ready = ops.put.ready"},
        {"@ac.compose(target=count", "@ac.compose(mode=\"full\", target=count"}
    }};
    for (const auto &[before, after] : changes) {
        SCOPED_TRACE(after);
        std::string source = peerAdmissionSource.str();
        source.replace(source.find(before), before.size(), after);
        auto file = capture("ready_invalid.py", source);
        ASSERT_TRUE(file) << diagnostics;
        diagnostics.clear();
        EXPECT_TRUE(failed(lower(*file, "ready_invalid.py"))) << diagnostics;
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeReadyKeepsMethodGuardAndRejectsLegacyAdmit) {
    std::string source = peerAdmissionSource.str();
    auto declaration = source.find("    @ac.method\n    def put()");
    source.replace(declaration, std::string("    @ac.method").size(), "    @ac.method(guard=lambda: allowed)");
    auto file = capture("ready_guard.py", source);
    ASSERT_TRUE(file) << diagnostics;
    auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(registry));
    auto unit = compiler::compilePythonSourceUnit(*file, owner("ready_guard.py"), *registry, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "ready_guard.Owner", error());
    ASSERT_TRUE(succeeded(final)) << diagnostics;
    auto guard = source.find("guard=lambda: allowed");
    source.replace(guard, std::string("guard=lambda: allowed").size(),
        "guard=lambda: ac.admit(count < 7, releases=(take,))");
    auto rejected = capture("retired_admit.py", source);
    ASSERT_TRUE(rejected) << diagnostics;
    EXPECT_TRUE(failed(lower(*rejected, "retired_admit.py"))) << diagnostics;
}

TEST_F(SourceTransactionCaptureTest, ComposeOverlapDefaultsSupportScalarStructAndEnum) {
    const std::array<std::string, 3> declarations = {
        "    value: ac.u8 = 7\n",
        "    value: Pair = Pair(first=7, second=0)\n",
        "    value: Phase = Phase.IDLE\n"
    };
    const std::array<std::string, 3> updates = {
        "        value = 9\n", "        value.first = 9\n", "        value = Phase.DONE\n"
    };
    for (unsigned kind = 0; kind < declarations.size(); ++kind) {
        std::string source = "import pycircuit as ac\nfrom enum import Enum\n"
            "@ac.encoding(width=1)\nclass Phase(Enum):\n    IDLE = 0\n    DONE = 1\n"
            "@ac.struct\nclass Pair:\n    first: ac.u8\n    second: ac.u1\n"
            "@ac.module\ndef Owner(choose: ac.u1):\n" + declarations[kind] +
            "    @ac.method\n    def update() -> None:\n" + updates[kind] +
            "    @ac.compose(target=value, operations=(update,))\n"
            "    def unused_overlap(old, ops):\n        return old\n"
            "    @ac.rule\n    def run() -> None:\n        if choose:\n            update()\n";
        auto file = capture("default_types.py", source);
        ASSERT_TRUE(file) << diagnostics;
        auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
        ASSERT_TRUE(succeeded(registry));
        auto unit = compiler::compilePythonSourceUnit(*file, owner("default_types.py"), *registry, error());
        ASSERT_TRUE(succeeded(unit)) << diagnostics;
        auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "default_types.Owner", error());
        ASSERT_TRUE(succeeded(final)) << diagnostics;
        EXPECT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
    }
}
