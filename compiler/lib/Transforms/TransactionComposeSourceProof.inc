    LogicalResult compositionProof() {
        auto groups = collectComposeGroups(prepared, budget);
        if (failed(groups)) return failure();
        if (groups->size() != candidate.compositions.size()) return reject("compose inventory differs");
        for (auto [ordinal, group] : llvm::enumerate(*groups)) {
            const auto &record = candidate.compositions[ordinal];
            auto method = group.composer;
            if (record.source.module != group.module || record.source.path != group.path ||
                    record.source.composer != group.composer || record.source.states != group.states ||
                    record.source.expanded != group.expanded ||
                    record.source.writes.size() != group.writes.size() ||
                    record.source.contributions.size() != group.contributions.size())
                return reject("compose source inventory differs");
            for (auto [actual, expected] : llvm::zip(record.source.contributions, group.contributions))
                if (actual.transaction != expected.transaction || actual.operation != expected.operation ||
                        actual.outputs != expected.outputs || actual.frame != expected.frame || actual.write != expected.write ||
                        actual.guard != expected.guard || actual.path != expected.path) return reject("compose source contribution differs");
            for (auto [actual, expected] : llvm::zip(record.source.writes, group.writes))
                if (actual.descriptor != expected.descriptor || actual.type != expected.type || actual.domains != expected.domains)
                    return reject("compose source write view differs");
            auto module = cast<ac::ModuleOp>(candidate.packageMap.lookup(group.module.operator->()));
            auto rule = record.rule;
            Builder builder(method.getContext());
            SmallVector<Value> inputs;
            for (auto state : group.states) {
                auto old = routed(group.module, group.path, state.getQ());
                if (failed(old)) return failure();
                inputs.push_back(*old);
            }
            unsigned count = group.states.size(), cursor = 0;
            auto names = method->getAttrOfType<DictionaryAttr>("ac.compose").getAs<ArrayAttr>("operations");
            if (group.expanded) {
                for (const auto &call : group.contributions) {
                    const auto &transaction = prepared.transactions[call.transaction];
                    auto writer = candidate.transactions[call.transaction].rule;
                    for (auto output : call.outputs) {
                        inputs.push_back(writer->getResult(transaction.outputs[output].enableResult));
                        inputs.push_back(writer->getResult(transaction.outputs[output].dataResult));
                    }
                    for (auto [control, polarity] : call.path) {
                        (void)polarity;
                        inputs.push_back(writer->getResult(transaction.checkBase + 2 * control));
                    }
                }
            } else {
            for (unsigned op = 0; op < names.size(); ++op) {
                auto contribution = llvm::find_if(group.contributions, [&](const auto &entry) { return entry.operation == op; });
                if (contribution == group.contributions.end()) {
                    if (cursor >= record.generated.size()) return reject("compose absent operation has no zero activity");
                    auto zero = record.generated[cursor++]->getResult(0);
                    if (failed(literalProof(zero, group.states.front()->getOperand(0).getType(), method.getOccurrence(),
                                                                    method.getLoc(), false, &module.getBody().front()))) return failure();
                    inputs.push_back(zero);
                    for (unsigned i = 0; i < count; ++i) inputs.push_back(inputs[i]);
                } else {
                    const auto &transaction = prepared.transactions[contribution->transaction];
                    const auto &actual = candidate.transactions[contribution->transaction];
                    inputs.push_back(actual.rule->getResult(transaction.outputs[contribution->outputs.front()].enableResult));
                    for (auto output : contribution->outputs) inputs.push_back(actual.rule->getResult(transaction.outputs[output].dataResult));
                }
            }
            for (unsigned op = 0; op < names.size(); ++op) {
                auto found = llvm::find_if(group.contributions, [&](const auto &entry) { return entry.operation == op; });
                if (found == group.contributions.end()) continue;
                const auto &contribution = *found;
                const auto &transaction = prepared.transactions[contribution.transaction];
                auto writer = candidate.transactions[contribution.transaction].rule;
                for (auto output : llvm::drop_begin(contribution.outputs))
                    inputs.push_back(writer->getResult(transaction.outputs[output].enableResult));
            }
            }
            for (const auto &view : group.writes) for (auto [callID, domainID] : view.domains) {
                if (!prepayAppend(budget, method, inputs)) return failure();
                const auto &call = group.contributions[callID];
                auto writer = candidate.transactions[call.transaction].rule;
                inputs.push_back(writer->getResult(prepared.transactions[call.transaction].writeDomains[domainID].result));
            }
            if (!rule || rule.getBody().empty() || rule.getBody().front().getNumArguments() != inputs.size())
                return reject("compose rule shape differs");
            SmallVector<Type> results(method.getFunctionType().getResults());
            results.push_back(inputs[count].getType());
            auto attributes = builder.getDictionaryAttr({
                    builder.getNamedAttr("name", builder.getStringAttr("__ac_compose_" + std::to_string(ordinal))),
                    builder.getNamedAttr("occurrence", method.getOccurrence()),
                    builder.getNamedAttr("ac.state_composition", composeMetadata(group, prepared, builder))});
            if (failed(generatedProof(rule, ac::RuleOp::getOperationName(), inputs, results, attributes,
                                                                method.getLoc(), &module.getBody().front(), 1))) return failure();
            IRMapping mapping;
            auto &body = rule.getBody().front();
            auto take = [&](StringRef name, ArrayRef<Value> operands, ArrayRef<Type> types,
                                            DictionaryAttr attrs, Location loc) -> FailureOr<Operation *> {
                if (cursor == record.generated.size()) return reject("compose operation inventory is truncated");
                auto operation = record.generated[cursor++];
                if (failed(generatedProof(operation, name, operands, types, attrs, loc, &body))) return failure();
                return operation;
            };
#include "TransactionComposeCallsSourceProof.inc"
            std::function<LogicalResult(Operation &, Operation *, Block *, unsigned)> payload;
            payload = [&](Operation &source, Operation *actual, Block *parent, unsigned depth) -> LogicalResult {
                if (depth >= 128 || !charge(budget, method, 4 + source.getNumOperands())) return failure();
                SmallVector<Value> operands;
                for (auto operand : source.getOperands()) operands.push_back(mapping.lookup(operand));
                if (failed(generatedProof(actual, source.getName().getStringRef(), operands,
                        SmallVector<Type>(source.getResultTypes()), source.getAttrDictionary(),
                        source.getLoc(), parent, source.getNumRegions()))) return failure();
                for (auto [before, after] : llvm::zip(source.getRegions(), actual->getRegions())) {
                    if (!before.hasOneBlock() || !after.hasOneBlock() ||
                            before.front().getArgumentTypes() != after.front().getArgumentTypes() ||
                            before.front().getOperations().size() != after.front().getOperations().size())
                        return reject("compose pure collection region differs");
                    if (!charge(budget, method, before.front().getNumArguments())) return failure();
                    for (auto [formal, value] : llvm::zip(before.front().getArguments(), after.front().getArguments()))
                        mapping.map(formal, value);
                    for (auto [original, candidate] : llvm::zip(before.front(), after.front()))
                        if (failed(payload(original, &candidate, &after.front(), depth + 1))) return failure();
                }
                for (auto [before, after] : llvm::zip(source.getResults(), actual->getResults())) mapping.map(before, after);
                return success();
            };
            unsigned branchSelection = 0;
            std::function<LogicalResult(Block &)> replay = [&](Block &source) -> LogicalResult {
                for (Operation &op : source.without_terminator()) {
                    if (auto branch = dyn_cast<ac::SourceBranchOp>(op)) {
                        if (failed(replay(branch.getThenRegion().front())) || failed(replay(branch.getElseRegion().front()))) return failure();
                        auto yes = cast<ac::YieldOp>(branch.getThenRegion().front().getTerminator());
                        auto no = cast<ac::YieldOp>(branch.getElseRegion().front().getTerminator());
                        for (auto [result, first, second] : llvm::zip(branch.getResults(), yes.getValues(), no.getValues())) {
                            if (!isa<ac::BitsType>(result.getType())) {
                                if (branchSelection >= record.branchSelections.size())
                                    return reject("compose aggregate selection inventory is truncated");
                                const auto &selected = record.branchSelections[branchSelection++];
                                ac::HardwareBindings bindings;
                                bindings.owner = method->getParentOfType<ac::ModuleOp>();
                                Operation *last = nullptr;
                                if (failed(localBranchProof(branch, result.getType(), bindings,
                                        mapping.lookup(branch.getCondition()), mapping.lookup(first),
                                        mapping.lookup(second), selected, &body, last))) return failure();
                                mapping.map(result, selected.value);
                                continue;
                            }
                            auto selected = take(ac::BitsSelectOp::getOperationName(),
                                    {mapping.lookup(branch.getCondition()), mapping.lookup(first), mapping.lookup(second)},
                                    {result.getType()}, builder.getDictionaryAttr({}), branch.getLoc());
                            if (failed(selected)) return failure();
                            mapping.map(result, (*selected)->getResult(0));
                        }
                    } else {
                        if (cursor == record.generated.size()) return reject("compose payload inventory is truncated");
                        if (failed(payload(op, record.generated[cursor++], &body, 0))) return failure();
                    }
                }
                return success();
            };
            if (failed(replay(method.getBody().front()))) return failure();
            if (branchSelection != record.branchSelections.size())
                return reject("compose aggregate selection inventory has extra entries");
            SmallVector<Value> expected;
            for (auto value : cast<ac::YieldOp>(method.getBody().front().getTerminator()).getValues()) expected.push_back(mapping.lookup(value));
            Value enabled = arguments[count];
            for (unsigned i = 1; i < names.size(); ++i) {
                auto gate = take(ac::BitsBinaryOp::getOperationName(), {enabled, arguments[count + i * (count + 1)]},
                                                    {enabled.getType()}, builder.getDictionaryAttr({builder.getNamedAttr("opcode", builder.getStringAttr("or"))}), method.getLoc());
                if (failed(gate)) return failure(); enabled = (*gate)->getResult(0);
            }
            expected.push_back(enabled);
            if (cursor != record.generated.size() || record.enable != rule->getResult(count) || record.results.size() != count)
                return reject("compose result inventory differs");
            for (unsigned i = 0; i < count; ++i)
                if (record.results[i] != rule->getResult(i)) return reject("compose result identity differs");
            if (failed(generatedProof(body.getTerminator(), ac::YieldOp::getOperationName(), expected, {},
                            builder.getDictionaryAttr({}), method.getLoc(), &body))) return failure();
        }
        return success();
    }
