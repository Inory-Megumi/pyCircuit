DictionaryAttr actionIdentity(const ac::TransactionStatePlan &plan,
    ac::InvocationFrameId frame, ac::SourceMethodOp method) {
    Builder b(method.getContext());
    ac::SourceMethodView view{plan.instances[plan.frames[frame].anchor].definition, method, {}};
    return b.getDictionaryAttr({
        b.getNamedAttr("callee", view.getSymbol()),
        b.getNamedAttr("declaration", method.getOccurrence()),
        b.getNamedAttr("owner", plan.instances[plan.frames[frame].anchor].occurrencePath)});
}

DictionaryAttr rootIdentity(const ac::TransactionStatePlan &plan,
    ac::InvocationFrameId frame, ac::SourceTransactionOp root) {
    Builder b(root.getContext());
    auto module = root->getParentOfType<ac::ModuleOp>();
    return b.getDictionaryAttr({b.getNamedAttr("callee", SymbolRefAttr::get(b.getContext(), module.getSymName(), {})),
        b.getNamedAttr("declaration", root.getDeclaration()),
        b.getNamedAttr("registration", root.getOccurrence()),
        b.getNamedAttr("owner", plan.instances[plan.frames[frame].anchor].occurrencePath)});
}

DictionaryAttr observationIdentity(const ac::TransactionStatePlan &plan,
    const ac::TransactionActionRead &read) {
    return read.root ? rootIdentity(plan, read.frame, read.root)
                     : actionIdentity(plan, read.frame, read.method);
}

FailureOr<ArrayAttr> actionInvocation(const ac::TransactionStatePlan &plan,
    ac::InvocationFrameId frame, SourceCheckBudget &budget) {
    SmallVector<ac::InvocationFrameId> chain;
    while (plan.frames[frame].parent) {
        if (!charge(budget, plan.transaction, 24)) return failure();
        chain.push_back(frame);
        frame = *plan.frames[frame].parent;
    }
    SmallVector<Attribute> rows;
    registrationInvocation(plan, rows);
    Builder b(plan.transaction->getContext());
    for (auto id : llvm::reverse(chain)) {
        const auto &entry = plan.frames[id];
        rows.push_back(b.getDictionaryAttr({b.getNamedAttr("call", entry.callOccurrence),
            b.getNamedAttr("receiver", entry.receiver)}));
    }
    return b.getArrayAttr(rows);
}

FailureOr<DictionaryAttr> projectedActionPath(const TransactionPreparation &prepared,
    ac::TransactionSourcePath source, SourceCheckBudget &budget) {
    auto path = sampledPath(*prepared.plan, source, budget);
    if (failed(path) || path->empty()) return path;
    NamedAttrList fields(*path);
    auto selection = path->getAs<IntegerAttr>("selection").getInt();
    fields.set("selection", Builder(prepared.plan->transaction->getContext()).getI64IntegerAttr(
        prepared.sourceControls[selection]));
    return fields.getDictionary(prepared.plan->transaction->getContext());
}

// The first slice admits explicit statement-if validity facts. Native and/or
// and conditional expressions do not establish lazy argument evaluation.
FailureOr<bool> actionArgumentAvailable(const ac::TransactionStatePlan &plan,
    const ac::TransactionActionRead &read, SourceCheckBudget &budget) {
    auto expected = actionIdentity(plan, read.frame, read.method);
    auto path = read.point.path;
    for (unsigned depth = 0; path.branch; ++depth) {
        if (depth > 128 || !charge(budget, read.operation)) return failure();
        const auto &branch = plan.branches[*path.branch];
        auto value = branch.condition;
        for (unsigned aliases = 0; aliases <= 128; ++aliases) {
            if (!charge(budget, read.operation, 1 + plan.calls.size())) return failure();
            std::optional<ac::BoundValueId> yielded;
            for (const auto &call : plan.calls)
                for (const auto &binding : call.results) {
                    if (!charge(budget, read.operation)) return failure();
                    if (binding.result == value) yielded = binding.yielded;
                }
            if (!yielded) break;
            value = *yielded;
            if (aliases == 128) return failure();
        }
        if (path.whenTrue)
            for (const auto &candidate : plan.actionReads) {
                if (!charge(budget, read.operation)) return failure();
                if (candidate.result == value &&
                    candidate.operation->getAttrOfType<StringAttr>("member").getValue() == "active" &&
                    actionIdentity(plan, candidate.frame, candidate.method) == expected) return true;
            }
        path = branch.entry.path;
    }
    return false;
}

#include "TransactionForwardPreparation.inc"

LogicalResult prepareActionObservations(PreparedTransactionLowering &prepared,
    SourceCheckBudget &budget) {
    for (auto &observer : prepared.transactions) {
        const auto &plan = *observer.plan;
        for (auto [readID, read] : llvm::enumerate(plan.actionReads)) {
            auto op = read.operation;
            if (!charge(budget, op, 32)) return failure();
            auto key = observationIdentity(plan, read);
            detail::TransactionActionInput input;
            input.read = readID;
            input.capture = observer.liveIns.size() + observer.externalPops.size() +
                            observer.actionInputs.size();
            if (op.getMember() == "argument") {
                auto available = actionArgumentAvailable(plan, read, budget);
                if (failed(available)) return failure();
                if (!*available) return op.emitOpError()
                    << "action args require an enclosing if action.active source path";
            }
            for (auto [producerID, producer] : llvm::enumerate(prepared.transactions)) {
                const auto &source = *producer.plan;
                if (source.routingModule != plan.routingModule) continue;
                if (read.root) {
                    if (!charge(budget, op, 8 + producer.actionExports.size())) return failure();
                    if (rootIdentity(source, source.rootFrame, source.transaction) != key) continue;
                    if (&producer == &observer) return op.emitOpError() << "own-root fired observation is unsupported";
                    auto found = llvm::find_if(producer.actionExports,
                        [](const auto &entry) { return !entry.call; });
                    uint64_t exportID = found - producer.actionExports.begin();
                    if (found == producer.actionExports.end()) {
                        detail::TransactionActionExport output;
                        output.activeResult = producer.totalResults++;
                        if (!prepayAppend(budget, op, producer.actionExports)) return failure();
                        producer.actionExports.push_back(std::move(output));
                    }
                    if (!prepayAppend(budget, op, input.producers)) return failure();
                    input.producers.push_back({producerID, exportID});
                    continue;
                }
                for (auto [callID, call] : llvm::enumerate(source.calls)) {
                    if (!charge(budget, op, 8 + producer.actionExports.size())) return failure();
                    auto method = source.frames[call.callee].method;
                    auto kind = method->getAttrOfType<StringAttr>("ac.method_kind");
                    if (!kind || kind.getValue() != "action" ||
                        actionIdentity(source, call.callee, method) != key) continue;
                    if (&producer == &observer) return op.emitOpError()
                        << "aggregate action observation from its own calling root is unsupported";
                    auto found = llvm::find_if(producer.actionExports,
                        [&](const auto &entry) { return entry.call == callID; });
                    uint64_t exportID = found - producer.actionExports.begin();
                    if (found == producer.actionExports.end()) {
                        detail::TransactionActionExport output;
                        output.call = callID;
                        output.activeResult = producer.totalResults++;
                        for (auto argument : call.arguments) {
                            (void)argument;
                            if (!prepayAppend(budget, op, output.arguments)) return failure();
                            output.arguments.push_back(producer.totalResults++);
                        }
                        if (!prepayAppend(budget, op, producer.actionExports)) return failure();
                        producer.actionExports.push_back(std::move(output));
                    }
                    if (!prepayAppend(budget, op, input.producers)) return failure();
                    input.producers.push_back({producerID, exportID});
                }
            }
            if (!prepayAppend(budget, op, observer.actionInputs)) return failure();
            observer.actionInputs.push_back(std::move(input));
        }
    }
    if (failed(prepareForwardExports(prepared, budget))) return failure();
    for (auto &transaction : prepared.transactions) {
        const auto &plan = *transaction.plan;
        Builder b(plan.transaction->getContext());
        NamedAttrList metadata(transaction.expectedAdmission);
        SmallVector<Attribute> exports, inputs;
        for (const auto &entry : transaction.actionExports) {
            if (!charge(budget, plan.transaction, 64 + entry.arguments.size() * 16)) return failure();
            const auto *call = entry.call ? &plan.calls[*entry.call] : nullptr;
            const auto frameID = call ? call->callee : plan.rootFrame;
            const auto &frame = plan.frames[frameID];
            auto path = projectedActionPath(transaction, frame.entry.path, budget);
            auto invocation = actionInvocation(plan, frameID, budget);
            if (failed(path) || failed(invocation)) return failure();
            SmallVector<Attribute> arguments;
            auto names = call ? ac::SourceMethodView{plan.instances[frame.anchor].definition,
                frame.method, {}}.getArgumentNames() : ArrayAttr();
            for (auto [index, result] : llvm::enumerate(entry.arguments))
                arguments.push_back(b.getDictionaryAttr({
                    b.getNamedAttr("name", names[index]),
                    b.getNamedAttr("result", b.getI64IntegerAttr(result))}));
            NamedAttrList fields(b.getDictionaryAttr({
                b.getNamedAttr("action", call ? actionIdentity(plan, frameID, frame.method)
                    : rootIdentity(plan, frameID, plan.transaction)),
                b.getNamedAttr("call", call ? frame.callOccurrence : plan.transaction->getAttrOfType<DictionaryAttr>("occurrence")),
                b.getNamedAttr("invocation", *invocation),
                b.getNamedAttr("path", *path),
                b.getNamedAttr("active", b.getI64IntegerAttr(entry.activeResult)),
                b.getNamedAttr("arguments", b.getArrayAttr(arguments))}));
            if (!entry.forwards.empty()) {
                auto forwards = forwardExportMetadata(transaction, entry, budget);
                if (failed(forwards)) return failure();
                fields.append("forwards", *forwards);
            }
            exports.push_back(fields.getDictionary(b.getContext()));
        }
        for (const auto &entry : transaction.actionInputs) {
            auto read = plan.actionReads[entry.read];
            auto op = read.operation;
            if (!charge(budget, op, 48)) return failure();
            NamedAttrList fields(b.getDictionaryAttr({
                b.getNamedAttr("capture", b.getI64IntegerAttr(entry.capture)),
                b.getNamedAttr("action", observationIdentity(plan, read)),
                b.getNamedAttr("member", b.getStringAttr(op.getMember() == "fired" ? "active" : op.getMember())),
                b.getNamedAttr("argument", op.getArgumentAttr()),
                b.getNamedAttr("occurrence", op.getOccurrence())}));
            if (read.forwardOwner) {
                fields.append("state", forwardStateIdentity(plan, *read.forwardOwner));
                fields.append("fields", read.forwardFields);
            }
            inputs.push_back(fields.getDictionary(b.getContext()));
        }
        if (!exports.empty()) metadata.append("actions", b.getArrayAttr(exports));
        if (!inputs.empty()) metadata.append("action_inputs", b.getArrayAttr(inputs));
        transaction.expectedAdmission = metadata.getDictionary(b.getContext());
    }
    return success();
}
