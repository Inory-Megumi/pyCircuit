        ac::HardwareAnalysis maskHardware(prepared.original);
        for (const auto &view : record.source.writes) {
            Type bit = zero.getType();
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
                    Value raw = block->getArgument(maskInput + offset);
                    if (isa<ac::TableType>(raw.getType())) {
                        auto integer = ac::MathIntAttr::get(method.getContext(), llvm::APSInt(llvm::APInt(64, row), true));
                        auto expression = builder.getDictionaryAttr({
                            builder.getNamedAttr("kind", builder.getStringAttr("literal")),
                            builder.getNamedAttr("value", builder.getDictionaryAttr({
                                builder.getNamedAttr("kind", builder.getStringAttr("integer")),
                                builder.getNamedAttr("value", integer)})),
                            builder.getNamedAttr("origin", method.getOccurrence()),
                            builder.getNamedAttr("location", selectionSourceLocation(method))});
                        OperationState constant(method.getLoc(), ac::BitsConstantOp::getOperationName());
                        constant.addTypes(branchCarrierType(64, method));
                        constant.addAttribute("value", ac::StaticExprAttr::get(method.getContext(), expression));
                        auto *index = create(constant); if (!index) return failure();
                        OperationState get(method.getLoc(), ac::TableGetOp::getOperationName());
                        get.addOperands({raw, index->getResult(0)}); get.addTypes({bit, bit});
                        auto *selected = create(get); if (!selected) return failure(); raw = selected->getResult(0);
                    }
                    OperationState gate(method.getLoc(), ac::BitsBinaryOp::getOperationName());
                    gate.addOperands({active[call], raw}); gate.addTypes(bit);
                    gate.addAttribute("opcode", builder.getStringAttr("and"));
                    auto *committed = create(gate); if (!committed) return failure();
                    OperationState join(method.getLoc(), ac::BitsBinaryOp::getOperationName());
                    join.addOperands({mask, committed->getResult(0)}); join.addTypes(bit);
                    join.addAttribute("opcode", builder.getStringAttr("or"));
                    auto *joined = create(join); if (!joined) return failure(); mask = joined->getResult(0);
                }
                elements.push_back(mask);
            }
            Value value = elements.front();
            if (table) {
                OperationState createTable(method.getLoc(), ac::TableCreateOp::getOperationName());
                createTable.addOperands(elements); createTable.addTypes(view.type);
                auto *created = create(createTable); if (!created) return failure(); value = created->getResult(0);
            }
            record.arguments.push_back(value);
            maskInput += view.domains.size();
        }
