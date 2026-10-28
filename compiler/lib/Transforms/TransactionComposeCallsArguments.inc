    unsigned targetCount = record.source.states.size();
    auto operationNames = method->getAttrOfType<DictionaryAttr>("ac.compose").getAs<ArrayAttr>("operations");
    if (record.source.expanded) {
        if (!charge(budget, method, 32)) return failure();
        auto zero = bitsLiteral(record.inputs[targetCount].getType(), method.getOccurrence(),
                                method.getLoc(), false, builder);
        record.generated.push_back(zero.getDefiningOp());
        SmallVector<Value> active;
        SmallVector<unsigned> starts;
        unsigned input = targetCount;
        for (const auto &call : record.source.contributions) {
            if (!charge(budget, method, 4 + call.path.size())) return failure();
            starts.push_back(input);
            Value enabled = block->getArgument(input);
            input += 2 * targetCount;
            for (auto [control, polarity] : call.path) {
                (void)control;
                Value condition = block->getArgument(input++);
                if (!polarity) {
                    OperationState invert(method.getLoc(), ac::BitsUnaryOp::getOperationName());
                    invert.addOperands(condition); invert.addTypes(condition.getType());
                    invert.addAttribute("opcode", builder.getStringAttr("not"));
                    auto *op = create(invert); if (!op) return failure(); condition = op->getResult(0);
                }
                OperationState gate(method.getLoc(), ac::BitsBinaryOp::getOperationName());
                gate.addOperands({enabled, condition}); gate.addTypes(enabled.getType());
                gate.addAttribute("opcode", builder.getStringAttr("and"));
                auto *op = create(gate); if (!op) return failure(); enabled = op->getResult(0);
            }
            active.push_back(enabled);
        }
        unsigned maskInput = input;
        for (const auto &view : record.source.writes) input += view.domains.size();
        if (input != block->getNumArguments()) return method.emitOpError() << "compose call input inventory differs";
        for (unsigned i = 0; i < targetCount; ++i) record.arguments.push_back(block->getArgument(i));
        for (unsigned kind = 0; kind < operationNames.size(); ++kind) {
            Value enabled = zero;
            SmallVector<Value> candidates;
            for (unsigned i = 0; i < targetCount; ++i) candidates.push_back(block->getArgument(i));
            for (auto [ordinal, call] : llvm::enumerate(record.source.contributions)) {
                if (!charge(budget, method)) return failure();
                if (call.operation != kind) continue;
                OperationState join(method.getLoc(), ac::BitsBinaryOp::getOperationName());
                join.addOperands({enabled, active[ordinal]}); join.addTypes(enabled.getType());
                join.addAttribute("opcode", builder.getStringAttr("or"));
                auto *op = create(join); if (!op) return failure(); enabled = op->getResult(0);
                for (unsigned i = 0; i < targetCount; ++i) {
                    if (!isa<ac::BitsType>(candidates[i].getType())) {
                        ac::HardwareBindings bindings;
                        bindings.owner = method->getParentOfType<ac::ModuleOp>();
                        auto selected = materializeSelection(method, bindings, active[ordinal],
                            block->getArgument(starts[ordinal] + 2 * i + 1), candidates[i],
                            candidates[i].getType(), builder, budget);
                        if (failed(selected) || !prepayAppend(budget, method, record.callSelections))
                            return failure();
                        candidates[i] = selected->value;
                        record.callSelections.push_back(std::move(*selected));
                        continue;
                    }
                    OperationState select(method.getLoc(), ac::BitsSelectOp::getOperationName());
                    select.addOperands({active[ordinal], block->getArgument(starts[ordinal] + 2 * i + 1), candidates[i]});
                    select.addTypes(candidates[i].getType());
                    auto *op = create(select); if (!op) return failure(); candidates[i] = op->getResult(0);
                }
            }
            record.arguments.push_back(enabled);
            llvm::append_range(record.arguments, candidates);
        }
#include "TransactionComposeWritesMaterialization.inc"
    } else {
        llvm::append_range(record.arguments, block->getArguments().take_front(body.getNumArguments()));
    }
    for (auto [formal, actual] : llvm::zip(body.getArguments(), record.arguments)) values.map(formal, actual);
