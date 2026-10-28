    // Replay a finite typed selection from actual SSA. Aggregate activity is
    // still one final operation enable; every leaf must select the same call.
    FailureOr<Value> compositionSelection(
            RuleOp rule, Block::iterator &cursor, const HardwareBindings &bindings,
            Value condition, Value whenTrue, Value whenFalse, unsigned depth = 0) {
        if (depth > 128 || failed(budget.debit(4, rule)))
            return rule.emitOpError() << "composition typed selection exceeds its bound";
        Type type = whenTrue.getType();
        if (!areEquivalentHardwareTypes(type, whenFalse.getType()))
            return rule.emitOpError() << "composition selection candidate types differ";
        auto &body = rule.getBody().front();
        auto take = [&](StringRef name, ValueRange operands) -> FailureOr<Operation *> {
            if (cursor == body.end() || failed(budget.debit(4 + operands.size(), rule))) return failure();
            Operation *operation = &*cursor++;
            if (operation->getName().getStringRef() != name ||
                    !llvm::equal(operation->getOperands(), operands) ||
                    failed(analysis.verifyResolvedOperation(operation, bindings)))
                return rule.emitOpError() << "composition typed invocation adapter differs";
            return operation;
        };
        // Current aggregate lowering uses one whole-value merge where the
        // original logical type admits it. The source proof authenticates that
        // choice; independently require the exact selection here, including an
        // unused auxiliary enable. A partial-field merge is not this adapter.
        if (cursor != body.end() && isa<ValueMergeOp>(*cursor)) {
            auto selected = take(ValueMergeOp::getOperationName(),
                {whenFalse, condition, whenTrue});
            if (failed(selected)) return failure();
            Builder builder(rule.getContext());
            if ((*selected)->getAttr("paths") !=
                    builder.getArrayAttr({builder.getArrayAttr({})}) ||
                    (*selected)->getAttr("operandSegmentSizes") !=
                    builder.getDenseI32ArrayAttr({1, 1, 1}) ||
                    (*selected)->getNumResults() != 2 ||
                    (*selected)->getResult(0).getType() != type ||
                    (*selected)->getResult(1).getType() != condition.getType() ||
                    !(*selected)->getResult(1).use_empty())
                return rule.emitOpError() << "composition whole-value invocation adapter differs";
            return (*selected)->getResult(0);
        }
        if (isa<BitsType>(type)) {
            auto selected = take(BitsSelectOp::getOperationName(), {condition, whenTrue, whenFalse});
            if (failed(selected)) return failure();
            return (*selected)->getResult(0);
        }
        if (isa<EnumType>(type)) {
            auto yes = take(EnumToBitsOp::getOperationName(), {whenTrue});
            auto no = take(EnumToBitsOp::getOperationName(), {whenFalse});
            if (failed(yes) || failed(no)) return failure();
            auto selected = take(BitsSelectOp::getOperationName(),
                {condition, (*yes)->getResult(0), (*no)->getResult(0)});
            if (failed(selected)) return failure();
            auto restored = take(EnumFromBitsOp::getOperationName(), {(*selected)->getResult(0)});
            if (failed(restored) || (*restored)->getResult(0).getType() != type ||
                    !(*restored)->getResult(1).use_empty()) return failure();
            return (*restored)->getResult(0);
        }
        SmallVector<Value> elements;
        if (auto structure = dyn_cast<StructType>(type)) {
            auto declaration = analysis.lookupStruct(structure);
            if (!declaration) return failure();
            for (Attribute raw : declaration.getFields()) {
                auto field = cast<DictionaryAttr>(raw).getAs<StringAttr>("name");
                auto yes = take(StructGetOp::getOperationName(), {whenTrue});
                auto no = take(StructGetOp::getOperationName(), {whenFalse});
                if (failed(yes) || failed(no) || (*yes)->getAttr("field") != field ||
                        (*no)->getAttr("field") != field) return failure();
                auto selected = compositionSelection(rule, cursor, bindings, condition,
                    (*yes)->getResult(0), (*no)->getResult(0), depth + 1);
                if (failed(selected) || failed(charge(budget, rule, 1, sizeof(Value)))) return failure();
                elements.push_back(*selected);
            }
        } else if (auto table = dyn_cast<TableType>(type)) {
            auto count = analysis.getTableSize(table, bindings, rule);
            if (failed(count)) return failure();
            for (uint64_t index = 0; index < *count; ++index) {
                auto literal = take(BitsConstantOp::getOperationName(), {});
                if (failed(literal)) return failure();
                auto number = analysis.evaluateStatic(cast<BitsConstantOp>(*literal).getValue(), bindings, rule);
                auto integer = succeeded(number) ? dyn_cast<MathIntAttr>(*number) : MathIntAttr();
                if (!integer || integer.getCanonicalValue() != std::to_string(index))
                    return rule.emitOpError() << "composition Table selection index differs";
                Value address = (*literal)->getResult(0);
                auto yes = take(TableGetOp::getOperationName(), {whenTrue, address});
                auto no = take(TableGetOp::getOperationName(), {whenFalse, address});
                if (failed(yes) || failed(no) || !(*yes)->getResult(1).use_empty() ||
                        !(*no)->getResult(1).use_empty()) return failure();
                auto selected = compositionSelection(rule, cursor, bindings, condition,
                    (*yes)->getResult(0), (*no)->getResult(0), depth + 1);
                if (failed(selected) || failed(charge(budget, rule, 1, sizeof(Value)))) return failure();
                elements.push_back(*selected);
            }
        } else return rule.emitOpError() << "composition selection has unsupported storage type";
        auto rebuilt = take(isa<StructType>(type) ? StructCreateOp::getOperationName()
                                                : TableCreateOp::getOperationName(), elements);
        if (failed(rebuilt) || (*rebuilt)->getResult(0).getType() != type) return failure();
        return (*rebuilt)->getResult(0);
    }
