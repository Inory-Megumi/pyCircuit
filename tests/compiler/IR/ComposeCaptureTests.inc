static constexpr llvm::StringLiteral composeSource = R"py(import pycircuit as ac
@ac.module
def Owner():
    value: ac.u8 = 10
    valid: ac.u1 = 1
    @ac.method
    def put(data: ac.u8) -> None:
        value = data
        valid = 1
    @ac.method
    def clear() -> None:
        value = value
        valid = 0
    @ac.compose(target=(value, valid), operations=(put, clear))
    def combine(old, ops):
        v = old.value
        ok = old.valid
        if ops.clear.active:
            ok = ops.clear.value.valid
        if ops.put.active:
            v = ops.put.value.value
            ok = ops.put.value.valid
        return v, ok
)py";

TEST_F(SourceTransactionCaptureTest, ComposeAggregateAndScalarTargetsShareCommitContract) {
    const std::string source = R"py(import pycircuit as ac
@ac.struct
class Entry:
    count: ac.u8
    valid: ac.u1
@ac.module
def Owner(choose: ac.u1, allowed: ac.u1):
    saved: Entry = Entry(count=3, valid=1)
    generation: ac.u4 = 0
    @ac.method
    def put(value: ac.u8) -> None:
        saved = Entry(count=value, valid=1)
        generation = generation + 1
    @ac.method
    def clear() -> None:
        saved = Entry(count=0, valid=0)
        generation = generation
    @ac.compose(target=(saved, generation), operations=(put, clear))
    def combine(old, ops):
        result = old.saved
        stamp = old.generation
        if ops.clear.active:
            result = ops.clear.value.saved
        if ops.put.active:
            result = ops.put.value.saved
            stamp = ops.put.value.generation
        return result, stamp
    @ac.method(guard=lambda: allowed)
    def require() -> None:
        pass
    @ac.rule
    def first() -> None:
        if choose:
            put(9)
        require()
    @ac.rule
    def second() -> None:
        clear()
)py";
    auto captured = capture("aggregate_compose.py", source);
    ASSERT_TRUE(captured) << diagnostics;
    auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(registry));
    auto unit = compiler::compilePythonSourceUnit(*captured, owner("aggregate_compose.py"), *registry, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}},
        "aggregate_compose.Owner", error(), compiler::SourceLinkTarget::Hardware);
    ASSERT_TRUE(succeeded(final)) << diagnostics;
    ASSERT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
    for (unsigned mutation = 0; mutation < 3; ++mutation) {
        OwningOpRef<ModuleOp> copy(cast<ModuleOp>((*final)->clone()));
        ac::RuleOp composition;
        copy->walk([&](ac::RuleOp rule) {
            if (rule->hasAttr("ac.state_composition")) composition = rule;
        });
        ASSERT_TRUE(composition);
        if (mutation == 0) composition->setOperand(0, composition->getOperand(3));
        if (mutation == 1) composition->setOperand(3, composition->getOperand(6));
        if (mutation == 2) composition->setOperand(2, composition->getOperand(5));
        diagnostics.clear();
        EXPECT_TRUE(failed(ac::HardwareAnalysis(*copy).verify())) << diagnostics;
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeExclusiveCallsPreserveAggregateCandidates) {
    for (bool table : {false, true}) {
        SCOPED_TRACE(table);
        std::string type = table ? "ac.table[2, Entry]" : "Entry";
        std::string source = R"py(import pycircuit as ac
@ac.struct
class Entry:
    count: ac.u8
    valid: ac.u1
@ac.module
def Owner(choose: ac.u1, left: TYPE, right: TYPE):
    saved: TYPE = 0
    @ac.method
    def put(value: TYPE) -> None:
        saved = value
    @ac.method
    def hold() -> None:
        saved = saved
    @ac.compose(target=saved, operations=(put, hold))
    def combine(old, ops):
        result = old
        if ops.put.active:
            result = ops.put.value
        return result
    @ac.rule
    def first() -> None:
        if choose:
            put(left)
        else:
            put(right)
    @ac.rule
    def second() -> None:
        hold()
)py";
        for (size_t position = source.find("TYPE"); position != std::string::npos;
                position = source.find("TYPE", position + type.size()))
            source.replace(position, 4, type);
        auto captured = capture("aggregate_calls.py", source);
        ASSERT_TRUE(captured) << diagnostics;
        auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
        ASSERT_TRUE(succeeded(registry));
        auto unit = compiler::compilePythonSourceUnit(*captured, owner("aggregate_calls.py"), *registry, error());
        ASSERT_TRUE(succeeded(unit)) << diagnostics;
        auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}},
            "aggregate_calls.Owner", error(), compiler::SourceLinkTarget::Hardware);
        ASSERT_TRUE(succeeded(final)) << diagnostics;
        ASSERT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
        for (unsigned mutation = 0; mutation < 4; ++mutation) {
            OwningOpRef<ModuleOp> copy(cast<ModuleOp>((*final)->clone()));
            ac::RuleOp composition;
            copy->walk([&](ac::RuleOp rule) {
                if (rule->hasAttr("ac.state_composition")) composition = rule;
            });
            ASSERT_TRUE(composition);
            ac::ValueMergeOp merge;
            composition.walk([&](ac::ValueMergeOp op) { if (!merge) merge = op; });
            ASSERT_TRUE(merge);
            if (mutation == 0)
                merge->setOperand(1, composition.getBody().front().front().getResult(0));
            if (mutation == 1) merge->setOperand(2, merge->getOperand(0));
            if (mutation == 2) {
                Builder builder(&context);
                merge->setAttr("paths", builder.getArrayAttr({
                    builder.getArrayAttr({builder.getStringAttr("count")})}));
            }
            if (mutation == 3) {
                auto *yield = composition.getBody().front().getTerminator();
                yield->setOperand(yield->getNumOperands() - 1, merge->getResult(1));
            }
            diagnostics.clear();
            EXPECT_TRUE(failed(ac::HardwareAnalysis(*copy).verify())) << diagnostics;
        }
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeConditionalMultiTargetFinalEnables) {
    const std::array<std::string, 3> calls = {
        "        if choose:\n            put(9)\n",
        "        if choose:\n            if other:\n                put(9)\n",
        "        if choose:\n            pass\n        else:\n            put(9)\n"};
    for (unsigned shape = 0; shape < calls.size(); ++shape) {
        SCOPED_TRACE(shape);
        std::string source = composeSource.str();
        source.replace(source.find("def Owner():"), std::string("def Owner():").size(),
                       "def Owner(choose: ac.u1, other: ac.u1, allowed: ac.u1):");
        source += R"py(
    @ac.method(guard=lambda: allowed)
    def require() -> None:
        pass
    @ac.rule
    def first() -> None:
)py";
        source += calls[shape];
        source += R"py(        require()
    @ac.rule
    def second() -> None:
        clear()
)py";
        auto captured = capture("conditional.py", source);
        ASSERT_TRUE(captured) << diagnostics;
        auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
        ASSERT_TRUE(succeeded(registry));
        auto unit = compiler::compilePythonSourceUnit(*captured, owner("conditional.py"), *registry, error());
        ASSERT_TRUE(succeeded(unit)) << diagnostics;
        auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "conditional.Owner", error(),
                                              compiler::SourceLinkTarget::Hardware);
        ASSERT_TRUE(succeeded(final)) << diagnostics;
        ASSERT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
        if (shape != 0) continue;

        // The accepted graph retains two separate original E ports. Only test
        // copies are mutated; none of these graphs is published or emitted.
        for (unsigned mutation = 0; mutation < 6; ++mutation) {
            SCOPED_TRACE(mutation);
            OwningOpRef<ModuleOp> copy(cast<ModuleOp>((*final)->clone()));
            ac::RuleOp compose;
            copy->walk([&](ac::RuleOp rule) { if (rule->hasAttr("ac.state_composition")) compose = rule; });
            ASSERT_TRUE(compose);
            auto active = dyn_cast<OpResult>(compose->getOperand(2));
            auto originalE = dyn_cast<OpResult>(compose->getOperand(8));
            ASSERT_TRUE(active && originalE);
            ASSERT_EQ(active.getOwner(), originalE.getOwner());
            ASSERT_NE(active, originalE);
            auto writer = cast<ac::RuleOp>(active.getOwner());
            auto yield = cast<ac::YieldOp>(writer.getBody().front().getTerminator());
            auto enable = yield.getValues()[originalE.getResultNumber()].getDefiningOp<ac::BitsBinaryOp>();
            ASSERT_TRUE(enable && enable.getOpcode() == "and");
            auto path = enable.getRhs().getDefiningOp<ac::BitsSelectOp>();
            ASSERT_TRUE(path);
            if (mutation == 0) {
                // Same shape but a different condition must not compare equal.
                path->setOperand(0, path.getFalseValue());
            } else if (mutation == 1) {
                Value yes = path.getTrueValue(), no = path.getFalseValue();
                path->setOperand(1, no);
                path->setOperand(2, yes);
            } else if (mutation == 2) {
                // Drop final admission: raw branch intent is not final fire.
                yield->setOperand(originalE.getResultNumber(), enable.getRhs());
            } else if (mutation == 3) {
                // Even equivalent E ports are not interchangeable as captures.
                compose->setOperand(8, active);
            } else if (mutation == 4) {
                compose->setOperand(2, compose->getOperand(5));
            } else {
                compose->setOperand(4, compose->getOperand(7));
            }
            diagnostics.clear();
            EXPECT_TRUE(failed(ac::HardwareAnalysis(*copy).verify())) << diagnostics;
        }
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeCapturesTypedGroupWithoutExecutingPython) {
    auto file = typed(composeSource);
    ASSERT_TRUE(file) << diagnostics;
    auto method = namedMethod(*file, "combine");
    ASSERT_TRUE(method);
    EXPECT_EQ(method.getFunctionType().getNumInputs(), 8u);
    EXPECT_EQ(method.getFunctionType().getNumResults(), 2u);
    EXPECT_TRUE(method.getCaptures().empty());
    EXPECT_EQ(method->getAttrOfType<StringAttr>("sym_visibility").getValue(), "private");
    EXPECT_TRUE(method->hasAttr("ac.compose"));
}

TEST_F(SourceTransactionCaptureTest, ComposeRejectsImpureOperations) {
    for (auto replacement : {std::string("        valid = 1\n        ac.log(\"info\", \"effect\", data)\n")}) {
        std::string text = composeSource.str();
        auto position = text.find("        valid = 1\n");
        text.replace(position, std::string("        valid = 1\n").size(), replacement);
        auto file = capture("invalid_compose.py", text);
        ASSERT_TRUE(file);
        diagnostics.clear();
        EXPECT_TRUE(failed(lower(*file, "invalid_compose.py"))) << diagnostics;
        EXPECT_NE(diagnostics.find("compose operation"), std::string::npos) << diagnostics;
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeFieldsKeepOneCandidatePerInvocation) {
    const std::string source = R"py(import pycircuit as ac
@ac.struct
class Entry:
    count0: ac.u8
    count1: ac.u8
    valid: ac.u1
@ac.module
def Owner(choose: ac.u1, allowed: ac.u1):
    saved: Entry = Entry(count0=2, count1=3, valid=1)
    @ac.method
    def add() -> None:
        saved.count0 = saved.count0 + 1
        saved.valid = 1
    @ac.method
    def sub() -> None:
        saved.count1 = saved.count1 - 1
    @ac.compose(target=saved, operations=(add, sub))
    def combine(old, ops):
        first = old.count0
        second = old.count1
        if ops.add.active:
            first = ops.add.value.count0
        if ops.sub.active:
            second = ops.sub.value.count1
        return Entry(count0=first, count1=second,
                     valid=(first != 0) or (second != 0))
    @ac.method(guard=lambda: allowed)
    def require() -> None:
        pass
    @ac.rule
    def first() -> None:
        if choose:
            add()
        require()
    @ac.rule
    def second() -> None:
        sub()
)py";
    auto captured = capture("field_compose.py", source);
    ASSERT_TRUE(captured) << diagnostics;
    auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(registry));
    auto unit = compiler::compilePythonSourceUnit(*captured, owner("field_compose.py"), *registry, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}},
        "field_compose.Owner", error(), compiler::SourceLinkTarget::Hardware);
    ASSERT_TRUE(succeeded(final)) << diagnostics;
    ASSERT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
}

TEST_F(SourceTransactionCaptureTest, ComposeWriteViewsTrackAuthoredFieldsAndFinalCommit) {
    for (bool table : {false, true}) {
        SCOPED_TRACE(table);
        std::string source = R"py(import pycircuit as ac
@ac.struct
class Entry:
    count0: ac.u8
    count1: ac.u8
    valid: ac.u1
@ac.module
def Owner(choose: ac.u1, allowed: ac.u1, index: ac.u1):
    saved: TYPE = 0
    @ac.method
    def add() -> None:
        if choose:
            WRITE.count0 = WRITE.count0
        else:
            WRITE.count1 = WRITE.count1 + 1
    @ac.method
    def sub() -> None:
        WRITE.count0 = WRITE.count0 - 1
    @ac.compose(target=saved, operations=(add, sub))
    def combine(old, ops):
        result = old
        if ops.add.writes.count0INDEX and not ops.sub.writes.count0INDEX:
            RESULT.count0 = ops.add.valueINDEX.count0
        elif ops.sub.writes.count0INDEX and not ops.add.writes.count0INDEX:
            RESULT.count0 = ops.sub.valueINDEX.count0
        if ops.add.writes.count1INDEX:
            RESULT.count1 = ops.add.valueINDEX.count1
        RESULT.valid = (RESULT.count0 != 0) or (RESULT.count1 != 0)
        return result
    @ac.method(guard=lambda: allowed)
    def require() -> None:
        pass
    @ac.rule
    def first() -> None:
        add()
        require()
    @ac.rule
    def second() -> None:
        sub()
)py";
        const std::array<std::pair<std::string, std::string>, 4> replacements{{
            {"TYPE", table ? "ac.table[2, Entry]" : "Entry"},
            {"WRITE", table ? "saved[index]" : "saved"},
            {"INDEX", table ? "[0]" : ""},
            {"RESULT", table ? "result[0]" : "result"}}};
        for (const auto &[before, after] : replacements)
            for (size_t at = source.find(before); at != std::string::npos; at = source.find(before, at + after.size()))
                source.replace(at, before.size(), after);
        auto captured = capture("write_views.py", source);
        ASSERT_TRUE(captured) << diagnostics;
        auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
        ASSERT_TRUE(succeeded(registry));
        auto unit = compiler::compilePythonSourceUnit(*captured, owner("write_views.py"), *registry, error());
        ASSERT_TRUE(succeeded(unit)) << diagnostics;
        auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}},
            "write_views.Owner", error(), compiler::SourceLinkTarget::Hardware);
        ASSERT_TRUE(succeeded(final)) << diagnostics;
        ASSERT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
        for (unsigned mutation = 0; mutation < 2; ++mutation) {
            SCOPED_TRACE(mutation);
            OwningOpRef<ModuleOp> copy(cast<ModuleOp>((*final)->clone()));
            ac::RuleOp compose;
            copy->walk([&](ac::RuleOp rule) { if (rule->hasAttr("ac.state_composition")) compose = rule; });
            ASSERT_TRUE(compose);
            if (mutation == 0) {
                // Swap two authored field mask captures of the same type.
                unsigned end = compose->getNumOperands();
                compose->setOperand(end - 1, compose->getOperand(end - 2));
            } else {
                // Remove final invocation admission from a mask gate.
                ac::BitsBinaryOp maskGate;
                for (auto op : compose.getBody().front().getOps<ac::BitsBinaryOp>())
                    if (!maskGate && op.getOpcode() == "and") maskGate = op;
                ASSERT_TRUE(maskGate);
                maskGate->setOperand(0, maskGate.getRhs());
            }
            diagnostics.clear();
            EXPECT_TRUE(failed(ac::HardwareAnalysis(*copy).verify())) << diagnostics;
        }
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeOperationBandwidthDoesNotDependOnAddress) {
    for (bool exclusive : {false, true}) {
        SCOPED_TRACE(exclusive);
        std::string source = R"py(import pycircuit as ac
@ac.module
def Owner(choose: ac.u1):
    saved: ac.table[2, ac.u8] = 0
    @ac.method
    def put(index: ac.u1) -> None:
        saved[index] = 1
    @ac.compose(target=saved, operations=(put,))
    def combine(old, ops):
        result = old
        if ops.put.active:
            result = ops.put.value
        return result
    @ac.rule
    def first() -> None:
FIRST
    @ac.rule
    def second() -> None:
SECOND
)py";
        source.replace(source.find("FIRST"), 5,
            exclusive ? "        if choose:\n            put(0)" : "        put(0)");
        source.replace(source.find("SECOND"), 6,
            exclusive ? "        if not choose:\n            put(1)" : "        put(1)");
        auto captured = capture("operation_bandwidth.py", source);
        ASSERT_TRUE(captured) << diagnostics;
        auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
        ASSERT_TRUE(succeeded(registry));
        auto unit = compiler::compilePythonSourceUnit(*captured, owner("operation_bandwidth.py"), *registry, error());
        ASSERT_TRUE(succeeded(unit)) << diagnostics;
        diagnostics.clear();
        auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}},
            "operation_bandwidth.Owner", error(), compiler::SourceLinkTarget::Hardware);
        EXPECT_EQ(succeeded(final), exclusive) << diagnostics;
        if (!exclusive) EXPECT_NE(diagnostics.find("mutually exclusive invocations"), std::string::npos) << diagnostics;
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeClosesConditionalTargetsWithoutChangingCandidates) {
    std::string source = composeSource.str();
    auto position = source.find("        valid = 1\n");
    source.replace(position, std::string("        valid = 1\n").size(),
        "        if data != 0:\n            valid = 1\n");
    source += R"py(
    @ac.rule
    def first() -> None:
        put(0)
    @ac.rule
    def second() -> None:
        clear()
)py";
    auto captured = capture("different_enable.py", source);
    ASSERT_TRUE(captured) << diagnostics;
    auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(registry));
    auto unit = compiler::compilePythonSourceUnit(*captured, owner("different_enable.py"), *registry, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    diagnostics.clear();
    auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}},
        "different_enable.Owner", error(), compiler::SourceLinkTarget::Hardware);
    EXPECT_TRUE(succeeded(final)) << diagnostics;
}

TEST_F(SourceTransactionCaptureTest, ComposeImplicitHoldMustReadTheSameCandidate) {
    std::string source = composeSource.str();
    auto position = source.find("        valid = 1\n");
    source.replace(position, std::string("        valid = 1\n").size(), "        pass\n");
    auto file = typed(source);
    ASSERT_TRUE(file) << diagnostics;
    auto put = namedMethod(*file, "put");
    ASSERT_TRUE(put);
    ac::SourceStateWriteOp hold;
    put.getBody().walk([&](ac::SourceStateWriteOp write) {
        if (write->hasAttr("ac.compose_hold")) hold = write;
    });
    ASSERT_TRUE(hold);
    auto read = hold.getValue().getDefiningOp<ac::SourceStateReadOp>();
    ASSERT_TRUE(read);
    // A tagged real update is not an implicit hold. Mutate only this test IR.
    hold->setOperand(1, hold.getPath());
    diagnostics.clear();
    EXPECT_TRUE(failed(mlir::verify(*file))) << diagnostics;
}

TEST_F(SourceTransactionCaptureTest, ComposeRejectsImpureComposerAndDuplicateOperations) {
    for (auto mutation : {0, 1, 2}) {
        SCOPED_TRACE(mutation);
        std::string text = composeSource.str();
        if (mutation == 0) {
            auto position = text.find("        return v, ok");
            text.insert(position, "        valid = 0\n");
        } else if (mutation == 1) {
            auto position = text.find("operations=(put, clear)");
            text.replace(position, std::string("operations=(put, clear)").size(), "operations=(put, put)");
        } else {
            auto position = text.find("        v = old.value");
            text.insert(position, "        ac.log(\"info\", \"compose effect\", old.value)\n");
        }
        auto file = capture("invalid_compose.py", text);
        ASSERT_TRUE(file);
        diagnostics.clear();
        EXPECT_TRUE(failed(lower(*file, "invalid_compose.py"))) << diagnostics;
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeRejectsTamperedTargetAndOperationContracts) {
    for (auto field : {"targets", "operations"}) {
        auto file = typed(composeSource);
        ASSERT_TRUE(file);
        auto method = namedMethod(*file, "combine");
        NamedAttrList attrs(method->getAttrOfType<DictionaryAttr>("ac.compose"));
        Builder builder(&context);
        attrs.set(field, builder.getArrayAttr({builder.getStringAttr("missing")}));
        method->setAttr("ac.compose", attrs.getDictionary(&context));
        diagnostics.clear();
        EXPECT_TRUE(failed(mlir::verify(*file))) << diagnostics;
    }
}

TEST_F(SourceTransactionCaptureTest, ComposeIndependentProofRejectsWrongCandidateEnableAndOwner) {
    std::string source = composeSource.str() + R"py(
    @ac.rule
    def first() -> None:
        put(9)
    @ac.rule
    def second() -> None:
        clear()
)py";
    auto captured = capture("compose.py", source);
    ASSERT_TRUE(captured);
    auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(registry));
    auto unit = compiler::compilePythonSourceUnit(*captured, owner("compose.py"), *registry, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    compiler::SourceLinkStages stages;
    auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "compose.Owner", error(),
                                          compiler::SourceLinkTarget::Hardware, &stages);
    ASSERT_TRUE(succeeded(final)) << diagnostics;
    ASSERT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
    // Mutate only private in-memory test copies. Published output is untouched.
    for (unsigned mutation = 0; mutation < 6; ++mutation) {
        SCOPED_TRACE(mutation);
        OwningOpRef<ModuleOp> copy(cast<ModuleOp>((*final)->clone()));
        ac::RuleOp compose;
        copy->walk([&](ac::RuleOp rule) { if (rule->hasAttr("ac.state_composition")) compose = rule; });
        ASSERT_TRUE(compose);
        if (mutation == 0) compose->setOperand(0, compose->getOperand(3));
        if (mutation == 1) compose->setOperand(2, compose->getOperand(1));
        if (mutation == 2) compose->setOperand(8, compose->getOperand(5));
        if (mutation == 3) compose->setOperand(3, compose->getOperand(0));
        if (mutation == 4) {
            auto yield = compose.getBody().front().getTerminator();
            yield->setOperand(2, compose.getBody().front().getArgument(2));
        }
        if (mutation == 5) {
            NamedAttrList attrs(compose->getAttrOfType<DictionaryAttr>("ac.state_composition"));
            auto rows = cast<ArrayAttr>(attrs.get("operations"));
            attrs.set("operations", ArrayAttr::get(&context, rows.getValue().take_front(1)));
            compose->setAttr("ac.state_composition", attrs.getDictionary(&context));
        }
        diagnostics.clear();
        EXPECT_TRUE(failed(ac::HardwareAnalysis(*copy).verify())) << diagnostics;
    }
    auto original = parseSourceString<ModuleOp>(stages.beforeTransactions, &context);
    ASSERT_TRUE(original) << diagnostics;
    ac::SourceTransactionStateAnalysis analysis(original->getOperation());
    ASSERT_TRUE(analysis.isValid()) << diagnostics;
    ac::HardwareSourceCheckLimits limits;
    ac::detail::SourceCheckBudget preparation(limits);
    auto plan = acir::detail::prepareTransactionLowering(*original, analysis, preparation);
    ASSERT_TRUE(succeeded(plan)) << diagnostics;
    for (unsigned mutation = 0; mutation < 2; ++mutation) {
        SCOPED_TRACE(mutation);
        ac::detail::SourceCheckBudget materialization(limits), initialProof(limits), tamperedProof(limits);
        auto candidate = acir::detail::materializeTransactionLowering(*plan, materialization);
        ASSERT_TRUE(succeeded(candidate)) << diagnostics;
        ASSERT_TRUE(succeeded(acir::detail::verifyTransactionMaterialization(*plan, *candidate, initialProof))) << diagnostics;
        ASSERT_EQ(candidate->compositions.size(), 1u);
        auto &record = candidate->compositions.front();
        if (mutation == 0) std::swap(record.source.states[0], record.source.states[1]);
        else record.rule.getBody().front().getTerminator()->setOperand(0, record.rule.getBody().front().getArgument(0));
        diagnostics.clear();
        EXPECT_TRUE(failed(acir::detail::verifyTransactionMaterialization(*plan, *candidate, tamperedProof))) << diagnostics;
    }
}
