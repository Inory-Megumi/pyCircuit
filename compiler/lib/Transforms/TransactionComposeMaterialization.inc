DictionaryAttr composeMetadata(const detail::ComposeGroup &group,
                               const PreparedTransactionLowering &prepared, Builder &builder) {
    SmallVector<Attribute> states, operations;
    for (auto state : group.states)
        states.push_back(builder.getDictionaryAttr({
            builder.getNamedAttr("owner", builder.getDictionaryAttr({builder.getNamedAttr(
                "instance_path", routePath(builder.getContext(), group.path))})),
            builder.getNamedAttr("declaration", state.getOccurrence()),
            builder.getNamedAttr("element", builder.getArrayAttr({}))}));
    auto names = group.composer->getAttrOfType<DictionaryAttr>("ac.compose").getAs<ArrayAttr>("operations");
    if (group.expanded) {
        SmallVector<Attribute> calls;
        for (const auto &call : group.contributions) {
            const auto &plan = *prepared.transactions[call.transaction].plan;
            SmallVector<Attribute> candidates;
            for (auto output : call.outputs) candidates.push_back(builder.getI64IntegerAttr(output));
            calls.push_back(builder.getDictionaryAttr({
                builder.getNamedAttr("registration", routedOccurrence(plan)),
                builder.getNamedAttr("candidates", builder.getArrayAttr(candidates)),
                builder.getNamedAttr("guard", builder.getI64IntegerAttr(call.guard)),
                builder.getNamedAttr("operation", builder.getI64IntegerAttr(call.operation))}));
        }
        SmallVector<NamedAttribute> result{builder.getNamedAttr("states", builder.getArrayAttr(states)),
            builder.getNamedAttr("operations", names), builder.getNamedAttr("calls", builder.getArrayAttr(calls))};
        if (!group.writes.empty()) {
            SmallVector<Attribute> views;
            for (const auto &view : group.writes) {
                SmallVector<Attribute> domains;
                for (auto [call, domain] : view.domains)
                    domains.push_back(builder.getArrayAttr({builder.getI64IntegerAttr(call), builder.getI64IntegerAttr(domain)}));
                SmallVector<NamedAttribute> fields(view.descriptor.getValue());
                fields.push_back(builder.getNamedAttr("domains", builder.getArrayAttr(domains)));
                views.push_back(builder.getDictionaryAttr(fields));
            }
            result.push_back(builder.getNamedAttr("writes", builder.getArrayAttr(views)));
        }
        return builder.getDictionaryAttr(result);
    }
    for (unsigned i = 0; i < names.size(); ++i) {
        auto contribution = llvm::find_if(group.contributions, [&](const auto &entry) { return entry.operation == i; });
        if (contribution == group.contributions.end()) { operations.push_back(builder.getDictionaryAttr({})); continue; }
        const auto &plan = *prepared.transactions[contribution->transaction].plan;
        SmallVector<Attribute> candidates;
        for (auto ordinal : contribution->outputs) candidates.push_back(builder.getI64IntegerAttr(ordinal));
        operations.push_back(builder.getDictionaryAttr({
            builder.getNamedAttr("registration", routedOccurrence(plan)),
            builder.getNamedAttr("candidates", builder.getArrayAttr(candidates))}));
    }
    return builder.getDictionaryAttr({builder.getNamedAttr("states", builder.getArrayAttr(states)),
                                      builder.getNamedAttr("operations", builder.getArrayAttr(operations))});
}

LogicalResult materializeComposeBody(detail::MaterializedCompose &record,
                                     const PreparedTransactionLowering &prepared,
                                     unsigned ordinal, OpBuilder &outer, SourceCheckBudget &budget) {
    IRMapping values;
    auto method = record.source.composer;
    auto &body = method.getBody().front();
    OperationState wrapper(method.getLoc(), ac::RuleOp::getOperationName());
    wrapper.addOperands(record.inputs);
    wrapper.addTypes(method.getFunctionType().getResults());
    wrapper.addTypes(record.inputs[record.source.states.size()].getType());
    wrapper.addAttribute("name", outer.getStringAttr("__ac_compose_" + std::to_string(ordinal)));
    wrapper.addAttribute("occurrence", method.getOccurrence());
    wrapper.addAttribute("ac.state_composition", composeMetadata(record.source, prepared, outer));
    wrapper.addRegion();
    record.rule = cast<ac::RuleOp>(outer.create(wrapper));
    auto *block = new Block;
    record.rule.getBody().push_back(block);
    for (auto actual : record.inputs) block->addArgument(actual.getType(), method.getLoc());
    auto builder = OpBuilder::atBlockEnd(block);
    auto create = [&](OperationState &state) -> Operation * {
        if (!charge(budget, method, 32 + 4 * state.operands.size())) return nullptr;
        state.location = ac::sourceIdentityLocation(state.location);
        auto *op = builder.create(state);
        record.generated.push_back(op);
        return op;
    };
#include "TransactionComposeCallsArguments.inc"
    std::function<LogicalResult(Block &)> emit = [&](Block &block) -> LogicalResult {
        for (Operation &operation : block.without_terminator()) {
            if (!charge(budget, method, 8)) return failure();
            if (auto branch = dyn_cast<ac::SourceBranchOp>(operation)) {
                if (failed(emit(branch.getThenRegion().front())) || failed(emit(branch.getElseRegion().front()))) return failure();
                auto yes = cast<ac::YieldOp>(branch.getThenRegion().front().getTerminator());
                auto no = cast<ac::YieldOp>(branch.getElseRegion().front().getTerminator());
                for (auto [result, first, second] : llvm::zip(branch.getResults(), yes.getValues(), no.getValues())) {
                    if (!isa<ac::BitsType>(result.getType())) {
                        ac::HardwareBindings bindings;
                        bindings.owner = method->getParentOfType<ac::ModuleOp>();
                        auto selected = materializeSelection(branch, bindings,
                            values.lookup(branch.getCondition()), values.lookup(first),
                            values.lookup(second), result.getType(), builder, budget);
                        if (failed(selected) || !prepayAppend(budget, method, record.branchSelections))
                            return failure();
                        values.map(result, selected->value);
                        record.branchSelections.push_back(std::move(*selected));
                        continue;
                    }
                    OperationState select(branch.getLoc(), ac::BitsSelectOp::getOperationName());
                    select.addOperands({values.lookup(branch.getCondition()), values.lookup(first), values.lookup(second)});
                    select.addTypes(result.getType());
                    auto *op = create(select); if (!op) return failure();
                    values.map(result, op->getResult(0));
                }
            } else {
                auto prepaid = operation.walk([&](Operation *nested) {
                    return charge(budget, method, 32 + 4 * nested->getNumOperands() + 2 * nested->getNumResults())
                        ? WalkResult::advance() : WalkResult::interrupt();
                });
                if (prepaid.wasInterrupted() || !prepayAppend(budget, method, record.generated)) return failure();
                Operation *copy = builder.clone(operation, values);
                record.generated.push_back(copy);
            }
        }
        return success();
    };
    if (failed(emit(body))) return failure();
    for (auto result : cast<ac::YieldOp>(body.getTerminator()).getValues()) record.results.push_back(values.lookup(result));
    unsigned count = record.source.states.size();
    auto operations = method->getAttrOfType<DictionaryAttr>("ac.compose").getAs<ArrayAttr>("operations");
    record.enable = record.arguments[count];
    for (unsigned i = 1; i < operations.size(); ++i) {
        OperationState combine(method.getLoc(), ac::BitsBinaryOp::getOperationName());
        combine.addOperands({record.enable, record.arguments[count + i * (count + 1)]});
        combine.addTypes(record.enable.getType());
        combine.addAttribute("opcode", builder.getStringAttr("or"));
        auto *op = create(combine); if (!op) return failure();
        record.enable = op->getResult(0);
    }
    OperationState yield(method.getLoc(), ac::YieldOp::getOperationName());
    yield.addOperands(record.results);
    yield.addOperands(record.enable);
    builder.create(yield);
    record.results.clear();
    for (unsigned i = 0; i < count; ++i) record.results.push_back(record.rule->getResult(i));
    record.enable = record.rule->getResult(count);
    return success();
}
