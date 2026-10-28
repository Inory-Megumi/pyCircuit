// Compose retains invocation identity until mutual exclusion has been proved.
// The source plan, including statement-time candidate versions, is immutable.
FailureOr<SmallVector<detail::ComposeGroup, 0>> collectComposeGroups(
        const PreparedTransactionLowering &prepared, SourceCheckBudget &budget) {
    SmallVector<detail::ComposeGroup, 0> groups;
    for (auto [index, transaction] : llvm::enumerate(prepared.transactions)) {
        const auto &plan = *transaction.plan;
        for (const auto &output : transaction.outputs) {
            if (!charge(budget, plan.transaction, 1 + groups.size())) return failure();
            const auto &owner = plan.owners[output.binding.owner];
            auto composer = ac::detail::stateComposer(owner.declaration);
            if (!composer) continue;
            auto path = anchorPath(plan, owner.anchor);
            auto group = llvm::find_if(groups, [&](const auto &entry) {
                return entry.module == plan.routingModule && entry.path == path && entry.composer == composer;
            });
            if (group == groups.end()) {
                if (!prepayAppend(budget, composer, groups)) return failure();
                groups.push_back({plan.routingModule, path, composer, {}, {}, false, {}});
                group = std::prev(groups.end());
                auto targets = composer->getAttrOfType<DictionaryAttr>("ac.compose").getAs<ArrayAttr>("targets");
                for (auto name : targets) {
                    for (auto state : composer->getParentOfType<ac::ModuleOp>().getBody().front().getOps<ac::SourceStateOp>()) {
                        if (!charge(budget, composer)) return failure();
                        if (state.getInstanceNameAttr() == name) {
                            if (!prepayAppend(budget, composer, group->states)) return failure();
                            group->states.push_back(state);
                        }
                    }
                }
            }
            if (!charge(budget, composer, 1 + group->contributions.size())) return failure();
            // All targets of this writer are checked together below.
            if (llvm::any_of(group->contributions, [&](const auto &entry) { return entry.transaction == index; })) continue;
            auto names = composer->getAttrOfType<DictionaryAttr>("ac.compose").getAs<ArrayAttr>("operations");
            SmallVector<uint64_t> outputs;
            for (auto state : group->states) {
                if (!charge(budget, composer, transaction.outputs.size())) return failure();
                auto target = llvm::find_if(transaction.outputs, [&](const auto &candidate) {
                    const auto &other = plan.owners[candidate.binding.owner];
                    return other.anchor == owner.anchor && other.declaration == state;
                });
                if (target == transaction.outputs.end()) return composer.emitOpError() << "compose operation must contribute all target states";
                if (!prepayAppend(budget, composer, outputs)) return failure();
                outputs.push_back(target - transaction.outputs.begin());
            }
            auto firstOwner = transaction.outputs[outputs.front()].binding.owner;
            SmallVector<uint64_t> frames;
            for (auto [writeID, write] : llvm::enumerate(plan.writes)) {
                if (!charge(budget, composer)) return failure();
                if (write.owner != firstOwner) continue;
                auto method = plan.frames[write.frame].method;
                if (!method || write.forwardedProposal || method->getParentOp() != composer->getParentOp())
                    return composer.emitOpError() << "composed state must be written through a declared Method";
                auto operation = llvm::find(names, method.getSymNameAttr());
                if (operation == names.end()) return composer.emitOpError() << "state writer is not a declared compose operation";
                if (llvm::is_contained(frames, write.frame)) continue;
                if (!prepayAppend(budget, composer, frames)) return failure();
                frames.push_back(write.frame);
                detail::ComposeContribution call;
                call.transaction = index;
                call.operation = operation - names.begin();
                call.frame = write.frame;
                call.write = writeID;
                bool invocationBoundary = false;
                // The proof represents invocation bandwidth, not a conditional
                // field write inside the Method. Candidate closure supplies an
                // unconditional root write at the invocation boundary.
                for (auto [candidateID, candidate] : llvm::enumerate(plan.writes)) {
                    if (!charge(budget, composer)) return failure();
                    if (candidate.owner == firstOwner && candidate.frame == write.frame &&
                            candidate.selectors.empty() && candidate.pathFact && candidate.pathFact.getValue() &&
                            candidate.operation->getBlock() == &method.getBody().front()) {
                        call.write = candidateID;
                        invocationBoundary = true;
                        break;
                    }
                }
                if (!invocationBoundary)
                    return composer.emitOpError() << "compose invocation needs an unconditional candidate closure";
                call.guard = transaction.sourceControls[plan.guards[plan.frames[write.frame].guard].control];
                if (!product(budget, composer, outputs.size(), 2)) return failure();
                call.outputs = outputs;
                auto ancestry = plan.frames[write.frame].entry.path;
                for (unsigned depth = 0; ancestry.branch; ++depth) {
                    if (depth >= 128 || !charge(budget, composer)) return failure();
                    const auto &branch = plan.branches[*ancestry.branch];
                    if (!branch.selection) return composer.emitOpError() << "compose invocation path has no sampled selection";
                    auto control = transaction.sourceControls[plan.selections[*branch.selection].control];
                    if (!prepayAppend(budget, composer, call.path)) return failure();
                    call.path.push_back({control, ancestry.whenTrue});
                    ancestry = branch.entry.path;
                }
                if (!prepayAppend(budget, composer, group->contributions)) return failure();
                group->contributions.push_back(std::move(call));
            }
            if (frames.empty()) return composer.emitOpError() << "compose writer has no operation invocation";
            for (auto outputID : outputs) {
                auto targetOwner = transaction.outputs[outputID].binding.owner;
                SmallVector<uint64_t> targetFrames;
                for (const auto &write : plan.writes) {
                    if (!charge(budget, composer, 1 + frames.size())) return failure();
                    if (write.owner != targetOwner) continue;
                    if (write.forwardedProposal || !llvm::is_contained(frames, write.frame))
                        return composer.emitOpError() << "compose invocation has an undeclared target writer";
                    if (llvm::is_contained(targetFrames, write.frame)) continue;
                    if (!prepayAppend(budget, composer, targetFrames)) return failure();
                    targetFrames.push_back(write.frame);
                }
                if (targetFrames.size() != frames.size()) return composer.emitOpError() << "compose invocation omits a target";
            }
        }
    }
    ac::HardwareAnalysis hardware(prepared.original);
    for (auto &group : groups) {
        for (const auto &call : group.contributions) {
            auto method = prepared.transactions[call.transaction].plan->frames[call.frame].method;
            if (!method.getGuard().front().getOps<ac::SourceAdmitOp>().empty()) group.expanded = true;
        }
#include "TransactionComposeWritesPreparation.inc"
        SourceWriteGrantProof proof(group.module, hardware, budget);
        for (size_t i = 0; i < group.contributions.size(); ++i) {
            const auto &left = group.contributions[i];
            for (size_t j = 0; j < i; ++j) {
                if (!charge(budget, group.composer)) return failure();
                const auto &right = group.contributions[j];
                bool sameRule = left.transaction == right.transaction;
                if (!sameRule && left.operation != right.operation) continue;
                group.expanded = true;
                const auto &a = *prepared.transactions[left.transaction].plan;
                const auto &b = *prepared.transactions[right.transaction].plan;
                auto disjoint = sameRule ? proof.disjointExecutionPaths(a, left.write, right.write)
                                         : proof.disjointInvocations(a, left.write, b, right.write);
                if (failed(disjoint)) return group.composer.emitOpError() << "compose invocation proof failed: " << proof.failureReason();
                if (!*disjoint) {
                    auto diagnostic = group.composer.emitOpError()
                            << (sameRule ? "compose calls in one outer Rule require mutually exclusive execution paths"
                    : "compose duplicate operation requires mutually exclusive invocations");
                    diagnostic.attachNote(a.frames[left.frame].call->getLoc()) << "first invocation";
                    diagnostic.attachNote(b.frames[right.frame].call->getLoc()) << "other invocation";
                    return failure();
                }
            }
        }
    }
    return groups;
}
