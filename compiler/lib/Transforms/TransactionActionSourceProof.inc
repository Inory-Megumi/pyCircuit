    LogicalResult actionViewsProof() {
        bool present = llvm::any_of(prepared.transactions,
            [](const auto &transaction) { return !transaction.plan->actionReads.empty(); });
        if (!present) return candidate.actionViews.empty() ? success()
            : reject("original package has invented action adapters");
        PreparedTransactionLowering expected;
        expected.original = prepared.original;
        for (const auto &original : prepared.transactions) {
            if (!charge(budget, original.plan->transaction, 64 +
                        original.liveIns.size() + original.externalPops.size() +
                        original.sourceControls.size() + original.writeDomains.size())) return failure();
            if (!charge(budget, original.plan->transaction, SourceCheckBudget::bytes(
                    SourceCheckBudget::multiply(original.writeDomains.size(),
                                                sizeof(detail::TransactionWriteDomain))))) return failure();
            TransactionPreparation transaction;
            transaction.plan = original.plan;
            transaction.liveIns.resize(original.liveIns.size());
            transaction.externalPops.resize(original.externalPops.size());
            transaction.sourceControls = original.sourceControls;
            transaction.writeDomains = original.writeDomains;
            transaction.totalResults = original.totalResults;
            for (const auto &output : original.actionExports) {
                if (output.arguments.size() + output.forwards.size() + 1 > transaction.totalResults)
                    return reject("original action suffix subtraction overflows");
                transaction.totalResults -= output.arguments.size() + output.forwards.size() + 1;
            }
            NamedAttrList metadata(original.expectedAdmission);
            metadata.erase("actions"); metadata.erase("action_inputs");
            transaction.expectedAdmission = metadata.getDictionary(prepared.original->getContext());
            if (!prepayAppend(budget, prepared.original, expected.transactions)) return failure();
            expected.transactions.push_back(std::move(transaction));
        }
        if (failed(prepareActionObservations(expected, budget))) return failure();
        uint64_t cursor = 0;
        ac::HardwareAnalysis stagedHardware(*candidate.module);
        for (auto [transactionID, transaction] : llvm::enumerate(expected.transactions)) {
            const auto &original = prepared.transactions[transactionID];
            const auto &plan = *transaction.plan;
            auto observer = candidate.transactions[transactionID].rule;
            if (transaction.totalResults != original.totalResults ||
                transaction.expectedAdmission != original.expectedAdmission ||
                transaction.actionExports.size() != original.actionExports.size() ||
                transaction.actionInputs.size() != original.actionInputs.size() ||
                transaction.forwardWrites != original.forwardWrites ||
                !candidate.transactions[transactionID].actionPlaceholders.empty())
                return reject("original action export/read inventory differs");
            for (auto [a, b] : llvm::zip(transaction.actionExports, original.actionExports)) {
                if (a.call != b.call || a.activeResult != b.activeResult || a.arguments != b.arguments ||
                    a.forwards.size() != b.forwards.size())
                    return reject("original action export identity differs");
                for (auto [left, right] : llvm::zip(a.forwards, b.forwards))
                    if (left.owner != right.owner || left.version != right.version || left.fields != right.fields ||
                        left.result != right.result || left.writes != right.writes)
                        return reject("original forward source boundary/write inventory differs");
            }
            for (auto [inputID, input] : llvm::enumerate(transaction.actionInputs)) {
                const auto &actual = original.actionInputs[inputID];
                if (input.read != actual.read || input.capture != actual.capture || input.producers != actual.producers)
                    return reject("original action producer closure differs");
                if (cursor >= candidate.actionViews.size()) return reject("original action adapter is missing");
                const auto &record = candidate.actionViews[cursor++];
                auto read = plan.actionReads[input.read];
                auto source = read.operation;
                auto rule = record.rule;
                auto module = candidate.packageMap.lookup(plan.routingModule.operator->());
                if (record.transaction != transactionID || record.input != inputID ||
                    !rule || !operations.contains(rule) || rule->getParentOp() != module ||
                    rule->getNumResults() != 1 || input.capture >= observer->getNumOperands() ||
                    observer->getOperand(input.capture) != rule->getResult(0) ||
                    rule.getOccurrence() != source.getOccurrence())
                    return reject("original action adapter routing differs");
                Builder b(rule.getContext());
                SmallVector<Value> inputs;
                SmallVector<Attribute> sources;
                if (read.forwardOwner) {
                    auto old = plan.owners[*read.forwardOwner].oldQ;
                    auto capture = llvm::find(original.liveIns, old) - original.liveIns.begin();
                    if (capture >= original.liveIns.size()) return reject("original forward baseline is absent");
                    inputs.push_back(observer->getOperand(capture));
                }
                for (auto [producerID, exportID] : input.producers) {
                    const auto &producer = expected.transactions[producerID];
                    const auto &output = producer.actionExports[exportID];
                    auto producerRule = candidate.transactions[producerID].rule;
                    inputs.push_back(producerRule->getResult(output.activeResult));
                    SmallVector<NamedAttribute> row{
                        b.getNamedAttr("registration", producerRule.getOccurrence()),
                        b.getNamedAttr("active", b.getI64IntegerAttr(output.activeResult))};
                    if (source.getMember() == "argument") {
                        const auto &call = producer.plan->calls[*output.call];
                        auto method = producer.plan->frames[call.callee].method;
                        auto names = method.getArgumentNames();
                        auto position = llvm::find(names, source.getArgumentAttr());
                        if (position == names.end()) return reject("original action argument is absent");
                        auto index = output.arguments[position - names.begin()];
                        inputs.push_back(producerRule->getResult(index));
                        row.push_back(b.getNamedAttr("argument", b.getI64IntegerAttr(index)));
                    }
                    if (read.forwardOwner) {
                        auto result = forwardResult(producer, output,
                            forwardStateIdentity(plan, *read.forwardOwner), read.forwardFields, source, budget);
                        if (failed(result)) return failure();
                        inputs.push_back(producerRule->getResult(*result));
                        row.push_back(b.getNamedAttr("forward", b.getI64IntegerAttr(*result)));
                    }
                    sources.push_back(b.getDictionaryAttr(row));
                }
                if (inputs != SmallVector<Value>(rule->getOperands()))
                    return reject("original action adapter captures different snapshots/events");
                auto inputRow = cast<DictionaryAttr>(
                    transaction.expectedAdmission.getAs<ArrayAttr>("action_inputs")[inputID]);
                NamedAttrList metadata(inputRow);
                metadata.append("registration", routedOccurrence(plan));
                metadata.append("sources", b.getArrayAttr(sources));
                if (rule->getAttr("ac.action_view") != metadata.getDictionary(rule.getContext()))
                    return reject("original action adapter metadata differs");
                if (rule->getRawDictionaryAttrs().size() != 1 ||
                    rule.getName() != "__ac_action_view_" + std::to_string(transactionID) +
                        "_" + std::to_string(inputID))
                    return reject("original action adapter attributes differ");
                auto proof = ac::detail::verifyActionView(rule, stagedHardware, budget);
                if (failed(proof)) return failure();
                for (Operation *operation : proof->operations)
                    if (failed(cover(operation))) return failure();
            }
        }
        return cursor == candidate.actionViews.size() ? success()
            : reject("original package has extra action adapters");
    }
