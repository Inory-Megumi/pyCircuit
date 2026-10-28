            // Replay the adapter from the original invocation inventory. Nothing
            // in record.arguments or the candidate metadata supplies this plan.
            SmallVector<Value> arguments;
            unsigned callSelection = 0;
            if (group.expanded) {
                if (cursor >= record.generated.size()) return reject("compose calls omit inactive literal");
                Value zero = record.generated[cursor++]->getResult(0);
                if (failed(literalProof(zero, inputs[count].getType(), method.getOccurrence(),
                                        method.getLoc(), false, &body))) return failure();
                SmallVector<Value> activities;
                SmallVector<unsigned> starts;
                unsigned input = count;
                for (const auto &call : group.contributions) {
                    if (!charge(budget, method, 4 + call.path.size())) return failure();
                    starts.push_back(input);
                    Value active = body.getArgument(input);
                    input += 2 * count;
                    for (auto [control, polarity] : call.path) {
                        (void)control;
                        Value condition = body.getArgument(input++);
                        if (!polarity) {
                            auto inverse = take(ac::BitsUnaryOp::getOperationName(), {condition}, {condition.getType()},
                                builder.getDictionaryAttr({builder.getNamedAttr("opcode", builder.getStringAttr("not"))}), method.getLoc());
                            if (failed(inverse)) return failure(); condition = (*inverse)->getResult(0);
                        }
                        auto gate = take(ac::BitsBinaryOp::getOperationName(), {active, condition}, {active.getType()},
                            builder.getDictionaryAttr({builder.getNamedAttr("opcode", builder.getStringAttr("and"))}), method.getLoc());
                        if (failed(gate)) return failure(); active = (*gate)->getResult(0);
                    }
                    activities.push_back(active);
                }
                unsigned maskInput = input;
                for (const auto &view : group.writes) input += view.domains.size();
                if (input != inputs.size()) return reject("compose invocation capture count differs");
                for (unsigned i = 0; i < count; ++i) arguments.push_back(body.getArgument(i));
                for (unsigned kind = 0; kind < names.size(); ++kind) {
                    Value active = zero;
                    SmallVector<Value> values;
                    for (unsigned i = 0; i < count; ++i) values.push_back(body.getArgument(i));
                    for (auto [ordinal, call] : llvm::enumerate(group.contributions)) {
                        if (!charge(budget, method)) return failure();
                        if (call.operation != kind) continue;
                        auto joined = take(ac::BitsBinaryOp::getOperationName(), {active, activities[ordinal]}, {active.getType()},
                            builder.getDictionaryAttr({builder.getNamedAttr("opcode", builder.getStringAttr("or"))}), method.getLoc());
                        if (failed(joined)) return failure(); active = (*joined)->getResult(0);
                        for (unsigned i = 0; i < count; ++i) {
                            if (!isa<ac::BitsType>(values[i].getType())) {
                                if (callSelection >= record.callSelections.size())
                                    return reject("compose aggregate call selection inventory is truncated");
                                const auto &selected = record.callSelections[callSelection++];
                                ac::HardwareBindings bindings;
                                bindings.owner = method->getParentOfType<ac::ModuleOp>();
                                Operation *last = nullptr;
                                if (failed(localBranchProof(method, values[i].getType(), bindings,
                                        activities[ordinal], body.getArgument(starts[ordinal] + 2 * i + 1),
                                        values[i], selected, &body, last))) return failure();
                                values[i] = selected.value;
                                continue;
                            }
                            auto selected = take(ac::BitsSelectOp::getOperationName(),
                                {activities[ordinal], body.getArgument(starts[ordinal] + 2 * i + 1), values[i]},
                                {values[i].getType()}, builder.getDictionaryAttr({}), method.getLoc());
                            if (failed(selected)) return failure(); values[i] = (*selected)->getResult(0);
                        }
                    }
                    arguments.push_back(active);
                    llvm::append_range(arguments, values);
                }
#include "TransactionComposeWritesSourceProof.inc"
            } else {
                llvm::append_range(arguments, body.getArguments().take_front(method.getBody().front().getNumArguments()));
            }
            if (arguments != record.arguments) return reject("compose normalized argument identities differ");
            if (callSelection != record.callSelections.size())
                return reject("compose aggregate call selection inventory has extra entries");
            for (auto [formal, actual] : llvm::zip(method.getBody().front().getArguments(), arguments)) mapping.map(formal, actual);
