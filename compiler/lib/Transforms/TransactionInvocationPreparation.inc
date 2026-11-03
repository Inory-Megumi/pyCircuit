    struct ActionInvocation {
        SmallVector<ac::InstanceOp> ownerPath, transactionPath;
        const ac::TransactionStatePlan *plan = nullptr;
        ac::CallBindingId call = 0;
        ac::SourceMethodOp method;
    };

    llvm::DenseMap<Operation *, unsigned> invocationStatus;
    std::map<Operation *, SmallVector<ActionInvocation>> invocationSummaries;

    // Empty actions retain call identity without inventing a state write.
    // Summaries are relative to real allocations; declaration symbols alone
    // never identify an operation port in two instances of the same Module.
    LogicalResult invocationSummary(ac::ModuleOp module, unsigned depth) {
        if (depth > 256 || !charge(budget, module)) return failure();
        unsigned status = invocationStatus.lookup(module);
        if (status == 2) return success();
        if (status == 1)
            return module.emitOpError() << "action invocation closure is recursive";
        invocationStatus[module] = 1;
        auto &summary = invocationSummaries[module];
        std::unique_ptr<SourceWriteGrantProof> proof;
        auto add = [&](ActionInvocation invocation) -> LogicalResult {
            if (!charge(budget, module, 8 + invocation.ownerPath.size() +
                        invocation.transactionPath.size())) return failure();
            for (const auto &prior : summary) {
                if (!charge(budget, module, 2 + prior.ownerPath.size())) return failure();
                if (prior.method != invocation.method || prior.ownerPath != invocation.ownerPath)
                    continue;
                if (!proof) {
                    if (!charge(budget, module, SourceCheckBudget::bytes(sizeof(SourceWriteGrantProof))))
                        return failure();
                    proof = std::make_unique<SourceWriteGrantProof>(module, hardware, budget);
                }
                bool sameRoot = prior.plan == invocation.plan &&
                                prior.transactionPath == invocation.transactionPath;
                auto disjoint = proof->disjointCalls(*prior.plan, prior.transactionPath, prior.call,
                    *invocation.plan, invocation.transactionPath, invocation.call, !sameRoot);
                if (failed(disjoint))
                    return invocation.plan->calls[invocation.call].operation->emitOpError()
                        << "action invocation exclusivity could not be proved: " << proof->failureReason();
                if (!*disjoint) {
                    auto diagnostic = invocation.plan->calls[invocation.call].operation->emitOpError();
                    diagnostic << (sameRoot ? "action can be invoked twice on one source path"
                                            : "action requires mutually exclusive successful outer callers");
                    diagnostic.attachNote(prior.plan->calls[prior.call].operation->getLoc())
                        << "other invocation of this concrete action is here";
                    return failure();
                }
            }
            if (!prepayAppend(budget, module, summary)) return failure();
            summary.push_back(std::move(invocation));
            return success();
        };
        for (unsigned index : routing(module).transactionIndices) {
            const auto &plan = *transactions[index].plan;
            for (auto [id, call] : llvm::enumerate(plan.calls)) {
                if (!charge(budget, module)) return failure();
                auto method = plan.frames[call.callee].method;
                auto kind = method->getAttrOfType<StringAttr>("ac.method_kind");
                if (!kind || kind.getValue() != "action") continue;
                auto path = anchorPath(plan, plan.frames[call.callee].anchor);
                if (!charge(budget, module, path.size())) return failure();
                if (failed(add({std::move(path), {}, &plan, id, method}))) return failure();
            }
        }
        for (Operation &operation : module.getBody().front()) {
            if (!charge(budget, &operation)) return failure();
            auto allocation = dyn_cast<ac::InstanceOp>(operation);
            auto collection = dyn_cast<ac::CollectionOp>(operation);
            Operation *target = allocation ? hardware.resolveCallee(allocation)
                                          : collection ? hardware.resolveCallee(collection) : nullptr;
            auto child = dyn_cast_or_null<ac::ModuleOp>(target);
            if (!child) continue;
            if (failed(invocationSummary(child, depth + 1))) return failure();
            if (collection) {
                if (!invocationSummaries[child].empty())
                    return collection.emitOpError() << "action invocation summaries cannot cross Collection";
                continue;
            }
            for (const auto &childInvocation : invocationSummaries[child]) {
                if (!charge(budget, module, 8 + SourceCheckBudget::bytes(sizeof(ActionInvocation)) +
                            2 * (childInvocation.ownerPath.size() + childInvocation.transactionPath.size())))
                    return failure();
                ActionInvocation invocation = childInvocation;
                invocation.ownerPath.insert(invocation.ownerPath.begin(), allocation);
                invocation.transactionPath.insert(invocation.transactionPath.begin(), allocation);
                if (failed(add(std::move(invocation)))) return failure();
            }
        }
        invocationStatus[module] = 2;
        return success();
    }
