static constexpr llvm::StringLiteral peerAdmissionSource = R"py(import pycircuit as ac
@ac.module
def Owner(choose: ac.u1, allowed: ac.u1):
    count: ac.u3 = 7
    stamp: ac.u8 = 0
    @ac.method
    def take() -> None:
        count = count - 1
    @ac.method
    def put() -> None:
        count = count + 1
    @ac.compose(target=count, operations=(put, take))
    def combine(old, ops):
        ops.take.ready = old != 0
        ops.put.ready = (old < 7) or ops.take.active
        return old
    @ac.method(guard=lambda: allowed)
    def gate() -> None:
        pass
    @ac.rule
    def produce() -> None:
        put()
    @ac.rule
    def consume() -> None:
        if choose:
            take()
        stamp = stamp + 1
        gate()
)py";

TEST_F(SourceTransactionCaptureTest, PeerAdmissionUsesFinalInvocationCommit) {
    auto captured = capture("peer.py", peerAdmissionSource);
    ASSERT_TRUE(captured) << diagnostics;
    auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(registry));
    auto unit = compiler::compilePythonSourceUnit(*captured, owner("peer.py"), *registry, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    compiler::SourceLinkStages stages;
    auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "peer.Owner", error(),
        compiler::SourceLinkTarget::Hardware, &stages);
    ASSERT_TRUE(succeeded(final)) << diagnostics;
    ASSERT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
    for (unsigned mutation = 0; mutation < 6; ++mutation) {
        SCOPED_TRACE(mutation);
        OwningOpRef<ModuleOp> copy(cast<ModuleOp>((*final)->clone()));
        ac::RuleOp consumer;
        copy->walk([&](ac::RuleOp rule) { if (rule->hasAttr("ac.peer_admissions")) consumer = rule; });
        ASSERT_TRUE(consumer);
        auto rows = consumer->getAttrOfType<ArrayAttr>("ac.peer_admissions");
        auto row = cast<DictionaryAttr>(rows[0]);
        auto capture = row.getAs<IntegerAttr>("capture").getInt();
        auto joined = consumer->getOperand(capture).getDefiningOp<ac::BitsBinaryOp>();
        ASSERT_TRUE(joined);
        if (mutation == 0) joined->setOperand(1, joined.getLhs());
        if (mutation == 1) {
            auto path = joined.getRhs().getDefiningOp<ac::BitsBinaryOp>();
            ASSERT_TRUE(path);
            joined->setOperand(1, path.getRhs());
        }
        if (mutation == 2) consumer->removeAttr("ac.peer_admissions");
        if (mutation == 3 || mutation == 4) {
            NamedAttrList changed(row);
            Builder builder(&context);
            changed.set(mutation == 3 ? "calls" : "releases", builder.getArrayAttr({}));
            consumer->setAttr("ac.peer_admissions", builder.getArrayAttr({changed.getDictionary(&context)}));
        }
        if (mutation == 5) {
            OpBuilder builder(consumer);
            OperationState leak(consumer.getLoc(), ac::BitsUnaryOp::getOperationName());
            leak.addOperands(joined.getResult());
            leak.addTypes(joined.getResult().getType());
            leak.addAttribute("opcode", builder.getStringAttr("not"));
            builder.create(leak);
        }
        diagnostics.clear();
        EXPECT_TRUE(failed(ac::HardwareAnalysis(*copy).verify())) << diagnostics;
    }
    auto original = parseSourceString<ModuleOp>(stages.beforeTransactions, &context);
    ASSERT_TRUE(original);
    ac::SourceTransactionStateAnalysis analysis(original->getOperation());
    ASSERT_TRUE(analysis.isValid()) << diagnostics;
    ac::HardwareSourceCheckLimits limits;
    ac::detail::SourceCheckBudget preparation(limits);
    auto plan = acir::detail::prepareTransactionLowering(*original, analysis, preparation);
    ASSERT_TRUE(succeeded(plan)) << diagnostics;
    for (unsigned mutation = 0; mutation < 5; ++mutation) {
        SCOPED_TRACE(mutation);
        ac::detail::SourceCheckBudget materialization(limits), checked(limits), tampered(limits);
        auto candidate = acir::detail::materializeTransactionLowering(*plan, materialization);
        ASSERT_TRUE(succeeded(candidate)) << diagnostics;
        ASSERT_TRUE(succeeded(acir::detail::verifyTransactionMaterialization(*plan, *candidate, checked))) << diagnostics;
        unsigned consumer = 0;
        while (consumer < plan->transactions.size() && plan->transactions[consumer].peerAdmissions.empty()) ++consumer;
        ASSERT_LT(consumer, plan->transactions.size());
        auto request = plan->transactions[consumer].peerAdmissions.front();
        auto rule = candidate->transactions[consumer].rule;
        if (mutation == 0) rule->setOperand(request.capture, rule->getOperand(plan->transactions[consumer].clockCapture));
        if (mutation == 1) {
            auto expression = candidate->transactions[consumer].frames[request.frame].lookup(request.operation.getReady());
            auto gate = expression.getDefiningOp<ac::BitsBinaryOp>();
            ASSERT_TRUE(gate);
            gate->setOperand(1, gate.getLhs());
        }
        if (mutation == 2) {
            auto joined = rule->getOperand(request.capture).getDefiningOp<ac::BitsBinaryOp>();
            ASSERT_TRUE(joined);
            joined->setOperand(1, joined.getLhs());
        }
        if (mutation == 3) {
            auto joined = rule->getOperand(request.capture).getDefiningOp<ac::BitsBinaryOp>();
            auto selected = joined.getRhs().getDefiningOp<ac::BitsBinaryOp>();
            ASSERT_TRUE(selected);
            joined->setOperand(1, selected.getRhs());
        }
        if (mutation == 4) {
            unsigned other = 0;
            while (other < plan->transactions.size() && !plan->transactions[other].peerAdmissions.empty()) ++other;
            ASSERT_LT(other, plan->transactions.size());
            candidate->transactions[other].rule->setAttr("ac.peer_admissions", rule->getAttr("ac.peer_admissions"));
        }
        diagnostics.clear();
        EXPECT_TRUE(failed(acir::detail::verifyTransactionMaterialization(*plan, *candidate, tampered))) << diagnostics;
    }
}

TEST_F(SourceTransactionCaptureTest, PeerAdmissionRejectsInvalidReleaseContracts) {
    for (StringRef peers : {"ops.put.active", "ops.missing.active", "ops.take.value", "ops.gate.active", "old"}) {
        SCOPED_TRACE(peers.str());
        std::string text = peerAdmissionSource.str();
        auto position = text.find("(old < 7) or ops.take.active");
        text.replace(position, std::string("(old < 7) or ops.take.active").size(), peers.str());
        auto file = capture("invalid_peer.py", text);
        ASSERT_TRUE(file) << diagnostics;
        diagnostics.clear();
        EXPECT_TRUE(failed(lower(*file, "invalid_peer.py"))) << diagnostics;
    }
}

TEST_F(SourceTransactionCaptureTest, PeerAdmissionRejectsTrueCommitCycle) {
    std::string text = peerAdmissionSource.str();
    auto position = text.find("ops.take.ready = old != 0");
    text.replace(position, std::string("ops.take.ready = old != 0").size(),
        "ops.take.ready = (old != 0) or ops.put.active");
    auto file = capture("peer_cycle.py", text);
    ASSERT_TRUE(file) << diagnostics;
    auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(registry));
    auto unit = compiler::compilePythonSourceUnit(*file, owner("peer_cycle.py"), *registry, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    diagnostics.clear();
    auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "peer_cycle.Owner", error());
    EXPECT_TRUE(failed(final)) << diagnostics;
    EXPECT_NE(diagnostics.find("combinational cycle"), std::string::npos) << diagnostics;
}

TEST_F(SourceTransactionCaptureTest, PeerAdmissionAbsentPeerContributesZero) {
    std::string text = peerAdmissionSource.str();
    auto position = text.find("    @ac.rule\n    def consume()");
    text.erase(position);
    auto file = capture("peer_absent.py", text);
    ASSERT_TRUE(file) << diagnostics;
    auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(registry));
    auto unit = compiler::compilePythonSourceUnit(*file, owner("peer_absent.py"), *registry, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "peer_absent.Owner", error());
    EXPECT_TRUE(succeeded(final)) << diagnostics;
}

TEST_F(SourceTransactionCaptureTest, PeerAdmissionAcceptsReverseOrderAndExclusiveCalls) {
    for (bool reverse : {false, true}) {
        std::string text = peerAdmissionSource.str();
        auto insertion = text.find("        stamp = stamp + 1");
        text.insert(insertion, "        else:\n            take()\n");
        if (reverse) {
            auto start = text.find("    @ac.rule\n    def produce()");
            auto end = text.find("    @ac.rule\n    def consume()");
            auto producer = text.substr(start, end - start);
            text.erase(start, end - start);
            text += producer;
        }
        auto file = capture("peer_order.py", text);
        ASSERT_TRUE(file) << diagnostics;
        auto registry = compiler::SourceHeaderRegistry::create(&context, {}, error());
        ASSERT_TRUE(succeeded(registry));
        auto unit = compiler::compilePythonSourceUnit(*file, owner("peer_order.py"), *registry, error());
        ASSERT_TRUE(succeeded(unit)) << diagnostics;
        auto final = compiler::linkSourceUnits({{*unit->body, *unit->interface}}, "peer_order.Owner", error());
        ASSERT_TRUE(succeeded(final)) << diagnostics;
        EXPECT_TRUE(succeeded(ac::HardwareAnalysis(**final).verify())) << diagnostics;
    }
}
