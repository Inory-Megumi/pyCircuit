        // Authenticate each projected raw write mask and its final invocation
        // enable from actual SSA, independently of source replay metadata.
        auto takeMask = [&](StringRef name, ValueRange operands) -> FailureOr<Operation *> {
            if (cursor == body.end() || failed(budget.debit(4 + operands.size(), rule))) return failure();
            Operation *operation = &*cursor++;
            if (operation->getName().getStringRef() != name || !llvm::equal(operation->getOperands(), operands) ||
                    failed(analysis.verifyResolvedOperation(operation, entry.bindings)))
                return rule.emitOpError() << "composition write-mask adapter differs";
            return operation;
        };
        for (const auto &mask : masks) {
            auto table = dyn_cast<TableType>(mask.type);
            uint64_t size = 1;
            if (table) {
                auto count = analysis.getTableSize(table, entry.bindings, rule);
                if (failed(count)) return failure(); size = *count;
            }
            SmallVector<Value> elements;
            for (uint64_t row = 0; row < size; ++row) {
                if (failed(charge(budget, rule, 1, sizeof(Value)))) return failure();
                Value merged = zero;
                for (auto [callID, capture] : mask.uses) {
                    Value raw = body.getArgument(capture);
                    if (isa<TableType>(raw.getType())) {
                        auto literal = takeMask(BitsConstantOp::getOperationName(), {});
                        if (failed(literal)) return failure();
                        auto value = analysis.evaluateStatic(cast<BitsConstantOp>(*literal).getValue(), entry.bindings, rule);
                        auto number = succeeded(value) ? dyn_cast<MathIntAttr>(*value) : MathIntAttr();
                        if (!number || number.getCanonicalValue() != std::to_string(row))
                            return rule.emitOpError() << "composition write-mask Table index differs";
                        auto get = takeMask(TableGetOp::getOperationName(), {raw, (*literal)->getResult(0)});
                        if (failed(get) || !(*get)->getResult(1).use_empty()) return failure();
                        raw = (*get)->getResult(0);
                    }
                    auto committed = take(BitsBinaryOp::getOperationName(), {calls[callID].active, raw}, "and");
                    if (failed(committed)) return failure();
                    auto joined = take(BitsBinaryOp::getOperationName(), {merged, *committed}, "or");
                    if (failed(joined)) return failure(); merged = *joined;
                }
                elements.push_back(merged);
            }
            if (table) {
                auto built = takeMask(TableCreateOp::getOperationName(), elements);
                if (failed(built) || !areEquivalentHardwareTypes((*built)->getResult(0).getType(), mask.type)) return failure();
            }
        }
