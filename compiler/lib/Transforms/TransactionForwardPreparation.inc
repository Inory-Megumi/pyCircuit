DictionaryAttr forwardStateIdentity(const ac::TransactionStatePlan &plan,
    ac::StateOwnerId owner) {
    const auto &state = plan.owners[owner];
    Builder b(plan.transaction->getContext());
    return b.getDictionaryAttr({b.getNamedAttr("owner", b.getDictionaryAttr({
        b.getNamedAttr("instance_path", state.instancePath)})),
        b.getNamedAttr("declaration", state.declaration->getAttr("occurrence")),
        b.getNamedAttr("element", b.getArrayAttr({}))});
}

LogicalResult prepareForwardExports(PreparedTransactionLowering &prepared,
    SourceCheckBudget &budget) {
    for (const auto &observer : prepared.transactions)
        for (const auto &input : observer.actionInputs) {
            const auto &read = observer.plan->actionReads[input.read];
            if (!read.forwardOwner) continue;
            auto op = read.operation;
            const auto &receiver = observer.plan->owners[*read.forwardOwner];
            if (input.producers.empty()) return op.emitOpError()
                << "forward source has no actual potentially writing invocation";
            for (auto [producerID, exportID] : input.producers) {
                auto &producer = prepared.transactions[producerID];
                auto &output = producer.actionExports[exportID];
                const auto &plan = *producer.plan;
                std::optional<ac::StateOwnerId> owner;
                for (auto [id, state] : llvm::enumerate(plan.owners)) {
                    if (!charge(budget, op, 8 + state.instancePath.size())) return failure();
                    if (state.declaration == receiver.declaration && state.instancePath == receiver.instancePath)
                        owner = id;
                }
                if (!owner) return op.emitOpError() << "forward source does not write the requested physical owner";
                if (!charge(budget, op, 1 + output.forwards.size())) return failure();
                if (llvm::any_of(output.forwards, [&](const auto &entry) {
                        return entry.owner == *owner && entry.fields == read.forwardFields; })) continue;
                detail::TransactionForwardExport view;
                view.owner = *owner; view.fields = read.forwardFields;
                auto sourceFrame = output.call ? plan.calls[*output.call].callee : plan.rootFrame;
                for (auto [id, write] : llvm::enumerate(plan.writes)) {
                    if (!charge(budget, op, 8 + write.selectors.size())) return failure();
                    if (write.owner != *owner) continue;
                    auto frame = write.frame;
                    unsigned depth = 0;
                    while (frame != sourceFrame && plan.frames[frame].parent) {
                        if (++depth > 128 || !charge(budget, op)) return failure();
                        frame = *plan.frames[frame].parent;
                    }
                    if (frame != sourceFrame) continue;
                    bool covers = write.selectors.size() <= view.fields.size();
                    for (auto [index, raw] : llvm::enumerate(write.selectors)) {
                        auto selector = cast<DictionaryAttr>(raw);
                        auto field = selector.getAs<StringAttr>("field");
                        if (!field) return op.emitOpError() << "forward does not support indexed writer footprints";
                        if (index >= view.fields.size() || field != view.fields[index]) covers = false;
                    }
                    if (!covers) continue;
                    if (write.forwardedProposal || !write.pathFact || !write.pathFact.getValue())
                        return op.emitOpError() << "forward requires real writes with a proved true authored path";
                    if (!prepayAppend(budget, op, view.writes)) return failure();
                    view.writes.push_back(id);
                }
                if (view.writes.empty()) return op.emitOpError()
                    << "forward source has no potential assignment to the requested leaf";
                for (auto id : view.writes) {
                    if (!charge(budget, op, 1 + producer.writeDomains.size() + producer.forwardWrites.size()))
                        return failure();
                    bool domain = llvm::any_of(producer.writeDomains,
                        [&](const auto &entry) { return entry.write == id; });
                    if (!domain && !llvm::is_contained(producer.forwardWrites, id)) {
                        if (!plan.writes[id].selectors.empty()) return op.emitOpError()
                            << "forward partial assignment has no native write domain";
                        // Ordinary expansion ran before observation demand. Pay
                        // the newly activated witness array before allocating it.
                        if (producer.writeDomains.empty() && producer.forwardWrites.empty() &&
                            !charge(budget, op, SourceCheckBudget::bytes(SourceCheckBudget::multiply(
                                plan.writes.size(), sizeof(detail::MaterializedSelectedWrite))))) return failure();
                        if (!prepayAppend(budget, op, producer.forwardWrites)) return failure();
                        producer.forwardWrites.push_back(id);
                    }
                }
                auto boundary = output.call ? ArrayRef(plan.calls[*output.call].exitVersions)
                                            : ArrayRef(plan.finalVersions);
                if (!charge(budget, op, 1 + boundary.size())) return failure();
                auto found = llvm::find_if(boundary, [&](auto entry) { return entry.owner == *owner; });
                if (found == boundary.end()) return op.emitOpError() << "forward source boundary has no owner version";
                view.version = found->version;
                if (output.call) {
                    if (!charge(budget, op, 1 + plan.finalVersions.size())) return failure();
                    auto final = llvm::find_if(plan.finalVersions,
                        [&](auto entry) { return entry.owner == *owner; });
                    if (final == plan.finalVersions.end() || final->version != view.version)
                        return op.emitOpError() << "action forward requires its whole-owner exit version to be root-final; later writes or joins need a checked history certificate";
                }
                if (!prepayAppend(budget, op, output.forwards)) return failure();
                output.forwards.push_back(std::move(view));
            }
        }
    // Demand collection precedes layout, keeping each source's suffix contiguous.
    for (auto &producer : prepared.transactions) {
        for (const auto &output : producer.actionExports)
            producer.totalResults -= 1 + output.arguments.size();
        for (auto &output : producer.actionExports) {
            output.activeResult = producer.totalResults++;
            for (auto &argument : output.arguments) argument = producer.totalResults++;
            for (auto &view : output.forwards) view.result = producer.totalResults++;
        }
    }
    return success();
}

FailureOr<ArrayAttr> forwardExportMetadata(const TransactionPreparation &prepared,
    const detail::TransactionActionExport &output, SourceCheckBudget &budget) {
    const auto &plan = *prepared.plan;
    Builder b(plan.transaction->getContext());
    SmallVector<Attribute> rows;
    for (const auto &view : output.forwards) {
        if (!charge(budget, plan.transaction, 64 + view.writes.size() * 16)) return failure();
        SmallVector<Attribute> writes;
        for (auto write : view.writes) {
            auto invocation = actionInvocation(plan, plan.writes[write].frame, budget);
            if (failed(invocation) || !charge(budget, plan.transaction, 1 + prepared.writeDomains.size()))
                return failure();
            auto domain = llvm::find_if(prepared.writeDomains,
                [&](const auto &entry) { return entry.write == write; });
            NamedAttrList row;
            row.append("invocation", *invocation);
            if (domain != prepared.writeDomains.end())
                row.append("domain", b.getI64IntegerAttr(domain - prepared.writeDomains.begin()));
            else
                row.append("whole_owner", b.getBoolAttr(true));
            writes.push_back(row.getDictionary(b.getContext()));
        }
        rows.push_back(b.getDictionaryAttr({b.getNamedAttr("state", forwardStateIdentity(plan, view.owner)),
            b.getNamedAttr("fields", view.fields), b.getNamedAttr("result", b.getI64IntegerAttr(view.result)),
            b.getNamedAttr("writes", b.getArrayAttr(writes))}));
    }
    return b.getArrayAttr(rows);
}

FailureOr<uint64_t> forwardResult(const TransactionPreparation &producer,
    const detail::TransactionActionExport &output, DictionaryAttr state,
    ArrayAttr fields, Operation *site, SourceCheckBudget &budget) {
    for (const auto &view : output.forwards) {
        if (!charge(budget, site, 16 + fields.size())) return failure();
        if (view.fields == fields && forwardStateIdentity(*producer.plan, view.owner) == state)
            return view.result;
    }
    return site->emitOpError() << "forward source suffix does not match its receiver";
}
