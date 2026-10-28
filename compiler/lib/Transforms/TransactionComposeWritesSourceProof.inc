                // The descriptor and domain list were rebuilt from the original
                // source writes, including call identity and field projection.
                ac::HardwareAnalysis maskHardware(prepared.original);
                for (const auto &view : group.writes) {
                    auto table = dyn_cast<ac::TableType>(view.type);
                    uint64_t size = 1;
                    if (table) {
                        ac::HardwareBindings bindings;
                        bindings.owner = method->getParentOfType<ac::ModuleOp>();
                        auto count = maskHardware.getTableSize(table, bindings, method);
                        if (failed(count)) return failure();
                        size = *count;
                    }
                    SmallVector<Value> elements;
                    for (uint64_t row = 0; row < size; ++row) {
                        if (!prepayAppend(budget, method, elements)) return failure();
                        Value mask = zero;
                        for (auto [offset, use] : llvm::enumerate(view.domains)) {
                            if (!charge(budget, method, 4)) return failure();
                            auto [call, domain] = use;
                            (void)domain;
                            Value raw = body.getArgument(maskInput + offset);
                            if (isa<ac::TableType>(raw.getType())) {
                                auto number = ac::MathIntAttr::get(method.getContext(), llvm::APSInt(llvm::APInt(64, row), true));
                                auto expression = builder.getDictionaryAttr({
                                    builder.getNamedAttr("kind", builder.getStringAttr("literal")),
                                    builder.getNamedAttr("value", builder.getDictionaryAttr({
                                        builder.getNamedAttr("kind", builder.getStringAttr("integer")),
                                        builder.getNamedAttr("value", number)})),
                                    builder.getNamedAttr("origin", method.getOccurrence()),
                                    builder.getNamedAttr("location", selectionSourceLocation(method))});
                                auto index = take(ac::BitsConstantOp::getOperationName(), {}, {branchCarrierType(64, method)},
                                    builder.getDictionaryAttr({builder.getNamedAttr("value", ac::StaticExprAttr::get(method.getContext(), expression))}), method.getLoc());
                                if (failed(index)) return failure();
                                auto projected = take(ac::TableGetOp::getOperationName(), {raw, (*index)->getResult(0)},
                                    {zero.getType(), zero.getType()}, builder.getDictionaryAttr({}), method.getLoc());
                                if (failed(projected) || !(*projected)->getResult(1).use_empty()) return failure();
                                raw = (*projected)->getResult(0);
                            }
                            auto gated = take(ac::BitsBinaryOp::getOperationName(), {activities[call], raw}, {zero.getType()},
                                builder.getDictionaryAttr({builder.getNamedAttr("opcode", builder.getStringAttr("and"))}), method.getLoc());
                            if (failed(gated)) return failure();
                            auto joined = take(ac::BitsBinaryOp::getOperationName(), {mask, (*gated)->getResult(0)}, {zero.getType()},
                                builder.getDictionaryAttr({builder.getNamedAttr("opcode", builder.getStringAttr("or"))}), method.getLoc());
                            if (failed(joined)) return failure();
                            mask = (*joined)->getResult(0);
                        }
                        elements.push_back(mask);
                    }
                    Value value = elements.front();
                    if (table) {
                        auto built = take(ac::TableCreateOp::getOperationName(), elements, {view.type}, builder.getDictionaryAttr({}), method.getLoc());
                        if (failed(built)) return failure();
                        value = (*built)->getResult(0);
                    }
                    arguments.push_back(value);
                    maskInput += view.domains.size();
                }
