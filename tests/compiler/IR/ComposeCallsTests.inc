TEST_F(SourceTransactionCaptureTest, ComposeExclusiveInvocationSites) {
    const std::array<std::string, 6> calls = {
        "    @ac.rule\n    def use() -> None:\n        if choose:\n            put(9)\n        else:\n            clear()\n        require()\n",
        "    @ac.rule\n    def use() -> None:\n        if choose:\n            put(9)\n        else:\n            put(5)\n        require()\n",
        "    @ac.rule\n    def use() -> None:\n        if choose:\n            if other:\n                put(9)\n            else:\n                clear()\n        else:\n            put(5)\n        require()\n",
        "    @ac.rule(guard=lambda: choose)\n    def first() -> None:\n        put(9)\n    @ac.rule(guard=lambda: not choose)\n    def second() -> None:\n        put(5)\n",
        "    @ac.rule\n    def first() -> None:\n        if choose:\n            put(9)\n    @ac.rule\n    def second() -> None:\n        if not choose:\n            put(5)\n",
        "    @ac.rule\n    def use() -> None:\n        if choose:\n            put(9)\n        if not choose:\n            clear()\n        require()\n"};
    for (auto [shape, statements] : llvm::enumerate(calls)) {
        SCOPED_TRACE(shape);
        diagnostics.clear();
        std::string source = composeSource.str();
        source.replace(source.find("def Owner():"), std::string("def Owner():").size(),
                       "def Owner(choose: ac.u1, other: ac.u1, allowed: ac.u1):");
        source += "\n    @ac.method(guard=lambda: allowed)\n    def require() -> None:\n        pass\n\n";
        source += statements;
        auto captured = capture("calls.py", source);
        ASSERT_TRUE(captured) << diagnostics;
        auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
        ASSERT_TRUE(succeeded(registry));
        auto unit = compiler::compilePythonSourceUnit(*captured, owner("calls.py"), *registry, error());
        ASSERT_TRUE(succeeded(unit)) << diagnostics;
        compiler::SourceLinkStages stages;
        auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "calls.Owner", error(),
                                              compiler::SourceLinkTarget::Hardware, &stages);
        ASSERT_TRUE(succeeded(final)) << diagnostics;
        ASSERT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
        if (shape != 0) continue;
        for (unsigned mutation = 0; mutation < 8; ++mutation) {
            SCOPED_TRACE(mutation);
            OwningOpRef<ModuleOp> copy(cast<ModuleOp>((*final)->clone()));
            ac::RuleOp compose;
            copy->walk([&](ac::RuleOp rule) { if (rule->hasAttr("ac.state_composition")) compose = rule; });
            ASSERT_TRUE(compose);
            // Two targets followed by two (E,D,E,D,branch) invocation captures.
            ASSERT_EQ(compose->getNumOperands(), 12u);
            if (mutation == 0) compose->setOperand(6, compose->getOperand(2));
            if (mutation == 1) compose->setOperand(3, compose->getOperand(0));
            if (mutation == 2) compose->setOperand(4, compose->getOperand(2));
            if (mutation == 3 || mutation == 4 || mutation == 5) {
                NamedAttrList contract(compose->getAttrOfType<DictionaryAttr>("ac.state_composition"));
                auto original = cast<ArrayAttr>(contract.get("calls"));
                SmallVector<Attribute> rows(original.begin(), original.end());
                if (mutation == 3) rows[1] = rows[0];
                if (mutation == 4) rows.pop_back();
                if (mutation == 5) {
                    NamedAttrList row(cast<DictionaryAttr>(rows[0]));
                    row.set("operation", IntegerAttr::get(IntegerType::get(&context, 64), 1));
                    rows[0] = row.getDictionary(&context);
                }
                contract.set("calls", ArrayAttr::get(&context, rows));
                compose->setAttr("ac.state_composition", contract.getDictionary(&context));
            }
            if (mutation == 6) {
                auto yielded = cast<ac::YieldOp>(compose.getBody().front().getTerminator());
                auto joined = yielded.getValues().back().getDefiningOp<ac::BitsBinaryOp>();
                ASSERT_TRUE(joined);
                yielded->setOperand(2, joined.getLhs());
            }
            if (mutation == 7) {
                auto result = cast<OpResult>(compose->getOperand(2));
                auto writer = cast<ac::RuleOp>(result.getOwner());
                auto yielded = cast<ac::YieldOp>(writer.getBody().front().getTerminator());
                auto gate = yielded.getValues()[result.getResultNumber()].getDefiningOp<ac::BitsBinaryOp>();
                ASSERT_TRUE(gate && gate.getOpcode() == "and");
                yielded->setOperand(result.getResultNumber(), gate.getRhs());
            }
            diagnostics.clear();
            EXPECT_TRUE(failed(ac::HardwareAnalysis(*copy).verify())) << diagnostics;
        }
        auto original = parseSourceString<ModuleOp>(stages.beforeTransactions, &context);
        ASSERT_TRUE(original);
        ac::SourceTransactionStateAnalysis analysis(original->getOperation());
        ASSERT_TRUE(analysis.isValid());
        ac::HardwareSourceCheckLimits limits;
        ac::detail::SourceCheckBudget preparation(limits);
        auto plan = acir::detail::prepareTransactionLowering(*original, analysis, preparation);
        ASSERT_TRUE(succeeded(plan)) << diagnostics;
        for (unsigned mutation = 0; mutation < 3; ++mutation) {
            ac::detail::SourceCheckBudget materialization(limits), checked(limits), tampered(limits);
            auto candidate = acir::detail::materializeTransactionLowering(*plan, materialization);
            ASSERT_TRUE(succeeded(candidate)) << diagnostics;
            ASSERT_TRUE(succeeded(acir::detail::verifyTransactionMaterialization(*plan, *candidate, checked))) << diagnostics;
            auto &record = candidate->compositions.front();
            if (mutation == 0) record.source.contributions[0].operation = 1;
            if (mutation == 1) record.source.contributions[0].path[0].second = false;
            if (mutation == 2) record.arguments[2] = record.rule.getBody().front().getArgument(2);
            diagnostics.clear();
            EXPECT_TRUE(failed(acir::detail::verifyTransactionMaterialization(*plan, *candidate, tampered))) << diagnostics;
        }
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeRejectsOverlappingAndSequentialCalls) {
    const std::array<std::string, 4> bodies = {
        "    @ac.rule\n    def use() -> None:\n        put(9)\n        clear()\n",
        "    @ac.rule\n    def use() -> None:\n        if choose:\n            put(9)\n        if other:\n            clear()\n",
        "    @ac.rule\n    def use() -> None:\n        if not valid:\n            put(9)\n        if valid:\n            clear()\n",
        "    @ac.rule\n    def first() -> None:\n        put(9)\n    @ac.rule\n    def second() -> None:\n        put(5)\n"};
    for (auto [shape, body] : llvm::enumerate(bodies)) {
        SCOPED_TRACE(shape);
        std::string source = composeSource.str();
        source.replace(source.find("def Owner():"), std::string("def Owner():").size(),
                       "def Owner(choose: ac.u1, other: ac.u1):");
        source += body;
        auto captured = capture("overlap.py", source);
        ASSERT_TRUE(captured);
        auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
        ASSERT_TRUE(succeeded(registry));
        auto unit = compiler::compilePythonSourceUnit(*captured, owner("overlap.py"), *registry, error());
        ASSERT_TRUE(succeeded(unit)) << diagnostics;
        diagnostics.clear();
        auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "overlap.Owner", error(),
                                              compiler::SourceLinkTarget::Hardware);
        EXPECT_TRUE(failed(final));
        EXPECT_NE(diagnostics.find("compose"), std::string::npos) << diagnostics;
    }
}

TEST_F(SourceTransactionCaptureTest, ComposePartialInvocationTreeRetainsEnableFacts) {
    // No operation occurs when choose is false. The fire boundary must retain
    // the resource write-intent/path mask, including E_write => choose.
    std::string source = composeSource.str();
    source.replace(source.find("def Owner():"), std::string("def Owner():").size(),
                   "def Owner(choose: ac.u1, other: ac.u1, allowed: ac.u1):");
    source += R"py(
    @ac.method(guard=lambda: allowed)
    def require() -> None:
        pass
    @ac.rule
    def use() -> None:
        if choose:
            if other:
                put(9)
            else:
                clear()
        require()
)py";
    auto captured = capture("partial_calls.py", source);
    ASSERT_TRUE(captured) << diagnostics;
    auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(registry));
    auto unit = compiler::compilePythonSourceUnit(*captured, owner("partial_calls.py"), *registry, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "partial_calls.Owner", error(),
                                          compiler::SourceLinkTarget::Hardware);
    ASSERT_TRUE(succeeded(final)) << diagnostics;
    EXPECT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
}
