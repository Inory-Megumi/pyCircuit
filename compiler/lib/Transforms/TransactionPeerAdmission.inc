// Queue-style capacity credit for ordinary composed operations. This carries
// only final invocation success; it does not forward candidate state or data.
FailureOr<SmallVector<detail::TransactionPreparation::PeerAdmission, 0>>
collectPeerAdmissions(const TransactionPreparation &transaction, SourceCheckBudget &budget) {
    SmallVector<detail::TransactionPreparation::PeerAdmission, 0> result;
    for (auto [frame, binding] : llvm::enumerate(transaction.plan->frames)) {
        if (!charge(budget, transaction.plan->transaction)) return failure();
        auto method = binding.method;
        if (!method) continue;
        for (auto operation : method.getGuard().front().getOps<ac::SourceAdmitOp>()) {
            if (!prepayAppend(budget, operation, result)) return failure();
            result.push_back({operation, frame, transaction.liveIns.size() +
                transaction.externalPops.size() + result.size()});
        }
    }
    return result;
}

FailureOr<SmallVector<detail::ComposeContribution, 0>> peerAdmissionCalls(
        const PreparedTransactionLowering &prepared, unsigned transactionID,
        detail::TransactionPreparation::PeerAdmission request,
        ArrayRef<detail::ComposeGroup> groups, SourceCheckBudget &budget) {
    const auto &plan = *prepared.transactions[transactionID].plan;
    auto method = plan.frames[request.frame].method;
    auto path = anchorPath(plan, plan.frames[request.frame].anchor);
    SmallVector<detail::ComposeContribution, 0> result;
    bool found = false;
    for (const auto &group : groups) {
        if (!charge(budget, request.operation, 1 + group.path.size())) return failure();
        auto names = group.composer->getAttrOfType<DictionaryAttr>("ac.compose").getAs<ArrayAttr>("operations");
        if (group.module != plan.routingModule || group.path != path ||
                !llvm::is_contained(names, method.getSymNameAttr())) continue;
        found = true;
        for (const auto &call : group.contributions) {
            if (!charge(budget, request.operation)) return failure();
            // Same-Rule sequential calls remain rejected by compose's existing
            // invocation proof. Exclusive alternatives cannot credit each other.
            if (call.transaction == transactionID ||
                    !llvm::is_contained(request.operation.getReleases(), names[call.operation])) continue;
            if (!prepayAppend(budget, request.operation, result)) return failure();
            if (!charge(budget, request.operation, call.outputs.size() + 2 * call.path.size())) return failure();
            result.push_back(call);
        }
    }
    if (!found) return request.operation.emitOpError() << "admit has no actual compose owner group";
    return result;
}

FailureOr<ArrayAttr> peerAdmissionMetadata(const PreparedTransactionLowering &prepared,
        unsigned index, ArrayRef<detail::ComposeGroup> groups, SourceCheckBudget &budget) {
    const auto &transaction = prepared.transactions[index];
    const auto &plan = *transaction.plan;
    Builder builder(plan.transaction->getContext());
    SmallVector<Attribute> rows;
    for (auto request : transaction.peerAdmissions) {
        auto method = plan.frames[request.frame].method;
        auto path = anchorPath(plan, plan.frames[request.frame].anchor);
        auto group = llvm::find_if(groups, [&](const auto &item) {
            return item.module == plan.routingModule && item.path == path &&
                llvm::is_contained(item.composer->template getAttrOfType<DictionaryAttr>("ac.compose")
                    .template getAs<ArrayAttr>("operations"), method.getSymNameAttr());
        });
        if (group == groups.end()) return failure();
        auto calls = peerAdmissionCalls(prepared, index, request, groups, budget);
        if (failed(calls)) return failure();
        SmallVector<Attribute> producers;
        auto names = group->composer->getAttrOfType<DictionaryAttr>("ac.compose").getAs<ArrayAttr>("operations");
        for (const auto &call : *calls) {
            if (!charge(budget, request.operation, 16)) return failure();
            producers.push_back(builder.getDictionaryAttr({
                builder.getNamedAttr("registration", routedOccurrence(*prepared.transactions[call.transaction].plan)),
                builder.getNamedAttr("candidate", builder.getI64IntegerAttr(call.outputs.front())),
                builder.getNamedAttr("guard", builder.getI64IntegerAttr(call.guard)),
                builder.getNamedAttr("operation", names[call.operation])}));
        }
        auto state = group->states.front();
        auto owner = builder.getDictionaryAttr({builder.getNamedAttr("instance_path", routePath(builder.getContext(), path))});
        auto identity = builder.getDictionaryAttr({builder.getNamedAttr("owner", owner),
            builder.getNamedAttr("declaration", state.getOccurrence()),
            builder.getNamedAttr("element", builder.getArrayAttr({}))});
        if (!prepayAppend(budget, request.operation, rows)) return failure();
        rows.push_back(builder.getDictionaryAttr({
            builder.getNamedAttr("capture", builder.getI64IntegerAttr(request.capture)),
            builder.getNamedAttr("guard", builder.getI64IntegerAttr(transaction.sourceControls[
                plan.guards[plan.frames[request.frame].guard].control])),
            builder.getNamedAttr("state", identity),
            builder.getNamedAttr("releases", request.operation.getReleases()),
            builder.getNamedAttr("calls", builder.getArrayAttr(producers))}));
    }
    return builder.getArrayAttr(rows);
}

LogicalResult materializePeerAdmissions(const PreparedTransactionLowering &prepared,
        detail::MaterializedTransactionLowering &candidate, SourceCheckBudget &budget) {
    if (llvm::all_of(prepared.transactions, [](const auto &item) { return item.peerAdmissions.empty(); }))
        return success();
    auto groups = collectComposeGroups(prepared, budget);
    if (failed(groups)) return failure();
    for (auto [index, transaction] : llvm::enumerate(prepared.transactions)) {
        auto rule = candidate.transactions[index].rule;
        OpBuilder builder(rule);
        if (!transaction.peerAdmissions.empty()) {
            auto metadata = peerAdmissionMetadata(prepared, index, *groups, budget);
            if (failed(metadata)) return failure();
            rule->setAttr("ac.peer_admissions", *metadata);
        }
        for (auto request : transaction.peerAdmissions) {
            if (!charge(budget, request.operation, 32)) return failure();
            auto calls = peerAdmissionCalls(prepared, index, request, *groups, budget);
            if (failed(calls)) return failure();
            Value credit = bitsLiteral(request.operation.getReady().getType(),
                request.operation.getOccurrence(), request.operation.getLoc(), false, builder);
            for (const auto &call : *calls) {
                const auto &producer = prepared.transactions[call.transaction];
                auto writer = candidate.transactions[call.transaction].rule;
                Value active = writer->getResult(producer.outputs[call.outputs.front()].enableResult);
                auto binary = [&](Value lhs, Value rhs, StringRef opcode) -> Value {
                    OperationState state(request.operation.getLoc(), ac::BitsBinaryOp::getOperationName());
                    state.addOperands({lhs, rhs});
                    state.addTypes(credit.getType());
                    state.addAttribute("opcode", builder.getStringAttr(opcode));
                    return builder.create(state)->getResult(0);
                };
                for (auto [control, polarity] : call.path) {
                    if (!charge(budget, request.operation, 64)) return failure();
                    Value selected = writer->getResult(producer.checkBase + 2 * control);
                    if (!polarity) {
                        OperationState invert(request.operation.getLoc(), ac::BitsUnaryOp::getOperationName());
                        invert.addOperands(selected);
                        invert.addTypes(selected.getType());
                        invert.addAttribute("opcode", builder.getStringAttr("not"));
                        selected = builder.create(invert)->getResult(0);
                    }
                    active = binary(active, selected, "and");
                }
                if (!charge(budget, request.operation, 32)) return failure();
                credit = binary(credit, active, "or");
            }
            rule->setOperand(request.capture, credit);
        }
    }
    return success();
}
