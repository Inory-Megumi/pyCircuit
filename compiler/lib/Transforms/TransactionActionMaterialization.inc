FailureOr<Value> actionZero(Type type, Operation *site, DictionaryAttr occurrence,
    OpBuilder &builder, SourceCheckBudget &budget, unsigned depth = 0) {
    if (depth > 128 || !charge(budget, site, 24)) return failure();
    if (isa<ac::BitsType>(type))
        return bitsLiteral(type, occurrence, site->getLoc(), false, builder);
    auto structure = dyn_cast<ac::StructType>(type);
    ac::HardwareAnalysis hardware(site->getParentOfType<mlir::ModuleOp>());
    auto declaration = structure ? hardware.lookupStruct(structure) : ac::StructOp();
    if (!declaration) return site->emitOpError()
        << "action argument views currently require fixed Bits or Struct payloads";
    SmallVector<Value> fields;
    for (Attribute raw : declaration.getFields()) {
        auto field = cast<DictionaryAttr>(raw);
        auto value = actionZero(field.getAs<TypeAttr>("type").getValue(), site,
            occurrence, builder, budget, depth + 1);
        if (failed(value) || !prepayAppend(budget, site, fields)) return failure();
        fields.push_back(*value);
    }
    OperationState state(ac::sourceIdentityLocation(site->getLoc()), ac::StructCreateOp::getOperationName());
    state.addOperands(fields); state.addTypes(type);
    return builder.create(state)->getResult(0);
}

LogicalResult materializeActionViews(const PreparedTransactionLowering &prepared,
    MaterializedTransactionLowering &candidate, SourceCheckBudget &budget) {
    for (auto [transactionID, transaction] : llvm::enumerate(prepared.transactions)) {
        const auto &plan = *transaction.plan;
        auto observer = candidate.transactions[transactionID].rule;
        auto module = observer->getParentOfType<ac::ModuleOp>();
        for (auto [inputID, input] : llvm::enumerate(transaction.actionInputs)) {
            const auto &read = plan.actionReads[input.read];
            auto op = read.operation;
            if (!charge(budget, op, 96)) return failure();
            SmallVector<Value> inputs;
            SmallVector<Attribute> sources;
            Builder attrs(op.getContext());
            if (read.forwardOwner) {
                auto old = plan.owners[*read.forwardOwner].oldQ;
                auto capture = llvm::find(transaction.liveIns, old) - transaction.liveIns.begin();
                if (capture >= transaction.liveIns.size()) return failure();
                inputs.push_back(observer->getOperand(capture));
            }
            for (auto [producerID, exportID] : input.producers) {
                const auto &producer = prepared.transactions[producerID];
                const auto &output = producer.actionExports[exportID];
                auto source = candidate.transactions[producerID].rule;
                ac::HardwareAnalysis hardware(*candidate.module);
                if (source->getParentOp() != module.operator->() ||
                    failed(ac::detail::verifyActionDomains(source, observer, hardware, budget)))
                    return op.emitOpError() << "action observations require the same physical clock/reset domain";
                inputs.push_back(source->getResult(output.activeResult));
                SmallVector<NamedAttribute> row{
                    attrs.getNamedAttr("registration", source->getAttr("occurrence")),
                    attrs.getNamedAttr("active", attrs.getI64IntegerAttr(output.activeResult))};
                if (op.getMember() == "argument") {
                    const auto &call = producer.plan->calls[*output.call];
                    auto method = producer.plan->frames[call.callee].method;
                    unsigned ordinal = 0;
                    for (auto name : method.getArgumentNames()) {
                        if (cast<StringAttr>(name).getValue() == op.getArgument()) break;
                        ++ordinal;
                    }
                    if (ordinal >= output.arguments.size()) return failure();
                    inputs.push_back(source->getResult(output.arguments[ordinal]));
                    row.push_back(attrs.getNamedAttr("argument", attrs.getI64IntegerAttr(output.arguments[ordinal])));
                }
                if (read.forwardOwner) {
                    auto result = forwardResult(producer, output,
                        forwardStateIdentity(plan, *read.forwardOwner), read.forwardFields, op, budget);
                    if (failed(result)) return failure();
                    inputs.push_back(source->getResult(*result));
                    row.push_back(attrs.getNamedAttr("forward", attrs.getI64IntegerAttr(*result)));
                }
                sources.push_back(attrs.getDictionaryAttr(row));
            }
            auto inputRow = cast<DictionaryAttr>(
                transaction.expectedAdmission.getAs<ArrayAttr>("action_inputs")[inputID]);
            NamedAttrList view(inputRow);
            view.append("registration", routedOccurrence(plan));
            view.append("sources", attrs.getArrayAttr(sources));
            auto builder = OpBuilder::atBlockTerminator(&module.getBody().front());
            OperationState state(ac::sourceIdentityLocation(op->getLoc()), ac::RuleOp::getOperationName());
            state.addOperands(inputs);
            state.addTypes(observer->getOperand(input.capture).getType());
            state.addAttribute("name", attrs.getStringAttr("__ac_action_view_" +
                std::to_string(transactionID) + "_" + std::to_string(inputID)));
            state.addAttribute("occurrence", op.getOccurrence());
            state.addAttribute("ac.action_view", view.getDictionary(op.getContext()));
            state.addRegion();
            auto rule = cast<ac::RuleOp>(builder.create(state));
            auto block = new Block();
            rule.getBody().push_back(block);
            for (Value value : inputs) block->addArgument(value.getType(), op->getLoc());
            auto inside = OpBuilder::atBlockEnd(block);
            unsigned cursor = 0;
            FailureOr<Value> initial = failure();
            if (read.forwardOwner) {
                ac::HardwareAnalysis hardware(*candidate.module);
                ac::HardwareBindings bindings; bindings.owner = module;
                initial = projectForwardLeaf(block->getArgument(cursor++), read.forwardFields,
                    hardware, bindings, rule, inside, budget);
            } else initial = actionZero(rule->getResult(0).getType(), rule, op.getOccurrence(), inside, budget);
            if (failed(initial)) return failure();
            Value value = *initial;
            for (const auto &source : sources) {
                (void)source;
                Value active = block->getArgument(cursor++);
                if (op.getMember() == "active" || op.getMember() == "fired") {
                    OperationState join(rule->getLoc(), ac::BitsBinaryOp::getOperationName());
                    join.addOperands({value, active}); join.addTypes(value.getType());
                    join.addAttribute("opcode", inside.getStringAttr("or"));
                    value = inside.create(join)->getResult(0);
                } else {
                    Value payload = block->getArgument(cursor++);
                    ac::HardwareBindings bindings;
                    bindings.owner = module;
                    auto selected = materializeSelection(rule, bindings, active, payload,
                        value, value.getType(), inside, budget);
                    if (failed(selected)) return failure();
                    value = selected->value;
                }
            }
            OperationState yield(rule->getLoc(), ac::YieldOp::getOperationName());
            yield.addOperands(value); inside.create(yield);
            observer->setOperand(input.capture, rule->getResult(0));
            auto placeholder = candidate.transactions[transactionID].actionPlaceholders[inputID];
            if (!placeholder->use_empty()) return op.emitOpError() << "action placeholder has an unrelated use";
            placeholder->erase();
            if (!prepayAppend(budget, op, candidate.actionViews)) return failure();
            candidate.actionViews.push_back({transactionID, inputID, rule});
        }
        candidate.transactions[transactionID].actionPlaceholders.clear();
    }
    return success();
}
