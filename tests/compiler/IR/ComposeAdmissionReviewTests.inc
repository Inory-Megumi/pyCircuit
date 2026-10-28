TEST_F(SourceTransactionCaptureTest, ComposeReadyRejectsMethodArgumentsAndPrivateAliases) {
    for (StringRef condition : {"credit", "__ready_state_0", "__ready_peer_0", "allowed", "stamp == 0"}) {
        SCOPED_TRACE(condition.str());
        std::string source = peerAdmissionSource.str();
        auto declaration = source.find("def put()");
        source.replace(declaration, std::string("def put()").size(),
            "def put(credit: ac.u1, __ready_state_0: ac.u1, __ready_peer_0: ac.u1)");
        auto call = source.find("        put()");
        source.replace(call, std::string("        put()").size(), "        put(allowed, allowed, allowed)");
        auto ready = source.find("(old < 7) or ops.take.active");
        source.replace(ready, std::string("(old < 7) or ops.take.active").size(), condition.str());
        auto file = capture("closed_ready.py", source);
        ASSERT_TRUE(file) << diagnostics;
        diagnostics.clear();
        EXPECT_TRUE(failed(lower(*file, "closed_ready.py"))) << diagnostics;
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeReadyRetainsParameterGuardAndClosedConstant) {
    std::string source = peerAdmissionSource.str();
    source.insert(source.find("@ac.module"), "LIMIT = 7\n");
    auto declaration = source.find("    @ac.method\n    def put()");
    source.replace(declaration, std::string("    @ac.method\n    def put()").size(),
        "    @ac.method(guard=lambda credit: credit)\n    def put(credit: ac.u1)");
    auto call = source.find("        put()");
    source.replace(call, std::string("        put()").size(), "        put(allowed)");
    auto ready = source.find("old < 7");
    source.replace(ready, std::string("old < 7").size(), "old < LIMIT");
    auto file = capture("guard_and_ready.py", source);
    ASSERT_TRUE(file) << diagnostics;
    auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(registry));
    auto unit = compiler::compilePythonSourceUnit(*file, owner("guard_and_ready.py"), *registry, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "guard_and_ready.Owner", error());
    ASSERT_TRUE(succeeded(final)) << diagnostics;
    EXPECT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
}

TEST_F(SourceTransactionCaptureTest, ComposeBodyDoesNotExposePrivateInputs) {
    for (StringRef name : {"__compose_old_0", "__compose_active_0", "__compose_value_0_0"}) {
        SCOPED_TRACE(name.str());
        std::string source = peerAdmissionSource.str();
        auto result = source.find("        return old");
        source.replace(result, std::string("        return old").size(), "        return " + name.str());
        auto file = capture("private_compose.py", source);
        ASSERT_TRUE(file) << diagnostics;
        diagnostics.clear();
        EXPECT_TRUE(failed(lower(*file, "private_compose.py"))) << diagnostics;
    }
}
