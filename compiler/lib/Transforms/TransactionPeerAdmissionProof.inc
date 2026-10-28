    LogicalResult peerAdmissionProof() {
        if (llvm::all_of(prepared.transactions, [](const auto &item) { return item.peerAdmissions.empty(); }))
            return success();
        auto groups = collectComposeGroups(prepared, budget);
        if (failed(groups)) return failure();
        for (auto [index, transaction] : llvm::enumerate(prepared.transactions)) {
            auto rule = candidate.transactions[index].rule;
            auto metadata = peerAdmissionMetadata(prepared, index, *groups, budget);
            if (failed(metadata) || (transaction.peerAdmissions.empty()
                    ? rule->hasAttr("ac.peer_admissions") : rule->getAttr("ac.peer_admissions") != *metadata))
                return reject("original peer admission metadata differs");
            auto *block = rule->getBlock();
            for (auto request : transaction.peerAdmissions) {
                auto calls = peerAdmissionCalls(prepared, index, request, *groups, budget);
                if (failed(calls)) return failure();
                Value credit = rule->getOperand(request.capture);
                Builder attributes(request.operation.getContext());
                auto gate = [&](Value value, Value left, Value right, StringRef opcode) {
                    return generatedProof(value.getDefiningOp(), ac::BitsBinaryOp::getOperationName(),
                        {left, right}, {request.operation.getReady().getType()},
                        attributes.getDictionaryAttr({attributes.getNamedAttr("opcode", attributes.getStringAttr(opcode))}),
                        request.operation.getLoc(), block);
                };
                for (const auto &call : llvm::reverse(*calls)) {
                    auto joined = credit.getDefiningOp<ac::BitsBinaryOp>();
                    if (!joined) return reject("peer admission union differs");
                    Value active = joined.getRhs();
                    const auto &producer = prepared.transactions[call.transaction];
                    auto writer = candidate.transactions[call.transaction].rule;
                    for (auto [control, polarity] : llvm::reverse(call.path)) {
                        if (!charge(budget, request.operation)) return failure();
                        auto selected = active.getDefiningOp<ac::BitsBinaryOp>();
                        if (!selected) return reject("peer admission invocation path is absent");
                        Value predicate = writer->getResult(producer.checkBase + 2 * control);
                        Value actual = selected.getRhs();
                        if (!polarity) {
                            if (failed(generatedProof(actual.getDefiningOp(), ac::BitsUnaryOp::getOperationName(),
                                    {predicate}, {predicate.getType()},
                                    attributes.getDictionaryAttr({attributes.getNamedAttr("opcode", attributes.getStringAttr("not"))}),
                                    request.operation.getLoc(), block))) return failure();
                        } else if (actual != predicate) return reject("peer admission invocation selector differs");
                        if (failed(gate(active, selected.getLhs(), actual, "and"))) return failure();
                        active = selected.getLhs();
                    }
                    if (active != writer->getResult(producer.outputs[call.outputs.front()].enableResult))
                        return reject("peer admission must use the matching owner's final invocation commit");
                    if (failed(gate(credit, joined.getLhs(), joined.getRhs(), "or"))) return failure();
                    credit = joined.getLhs();
                }
                if (failed(literalProof(credit, request.operation.getReady().getType(),
                        request.operation.getOccurrence(), request.operation.getLoc(), false, block)))
                    return failure();
            }
        }
        return success();
    }
