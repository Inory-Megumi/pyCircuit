    // Authenticate every cross-Rule credit before granting narrowly scoped
    // private-enable uses. Composition independently proves the call inventory.
    LogicalResult peerAdmissions() {
        for (const auto &entry : occurrences) {
            if (!entry.wiring) continue;
            Builder builder(entry.module->getContext());
            for (const auto &consumer : entry.wiring->writers) {
                auto rule = consumer.rule;
                auto raw = rule->getAttr("ac.peer_admissions");
                if (!raw) continue;
                auto rows = dyn_cast<ArrayAttr>(raw);
                if (!rows || rows.empty()) return rule.emitOpError() << "invalid peer admission inventory";
                auto admission = writerAdmission(entry, rule);
                if (failed(admission)) return failure();
                SmallVector<uint64_t> captures;
                auto ordinal = [&](DictionaryAttr row, StringRef key, uint64_t bound) -> FailureOr<uint64_t> {
                    auto value = row.getAs<IntegerAttr>(key);
                    if (!value || !value.getType().isSignlessInteger(64) || value.getInt() < 0 ||
                            uint64_t(value.getInt()) >= bound)
                        return rule.emitOpError() << "invalid peer admission " << key;
                    return uint64_t(value.getInt());
                };
                for (auto rawRow : rows) {
                    auto row = dyn_cast<DictionaryAttr>(rawRow);
                    if (failed(exact(row, {"capture", "guard", "state", "releases", "calls"}, rule, "peer admission"))) return failure();
                    auto capture = ordinal(row, "capture", rule->getNumOperands());
                    auto guard = ordinal(row, "guard", (*admission)->controls.size());
                    if (failed(capture) || failed(guard)) return failure();
                    if (llvm::is_contained(captures, *capture) ||
                            (*admission)->controls[*guard].kind != SampledControlKind::CallableGuard)
                        return rule.emitOpError() << "peer admission must name a distinct capture and callable guard";
                    if (failed(charge(budget, rule, captures.size() + 1, sizeof(uint64_t)))) return failure();
                    captures.push_back(*capture);
                    auto id = row.getAs<DictionaryAttr>("state");
                    if (!id || failed(wholeStateID(id, rule))) return failure();
                    auto state = target(entry, id);
                    if (failed(state)) return failure();
                    DictionaryAttr group;
                    for (auto compose : entry.module->getRegion(0).front().getOps<RuleOp>()) {
                        if (failed(budget.debit(1, compose))) return failure();
                        auto contract = compose->getAttrOfType<DictionaryAttr>("ac.state_composition");
                        auto targets = contract ? contract.getAs<ArrayAttr>("states") : ArrayAttr();
                        if (!targets || targets.empty() || targets[0] != id) continue;
                        if (group) return rule.emitOpError() << "peer admission has ambiguous composition owner";
                        group = contract;
                    }
                    auto names = group ? group.getAs<ArrayAttr>("operations") : ArrayAttr();
                    auto calls = group ? group.getAs<ArrayAttr>("calls") : ArrayAttr();
                    auto releases = row.getAs<ArrayAttr>("releases");
                    auto declared = row.getAs<ArrayAttr>("calls");
                    if (!names || !calls || !releases || releases.empty() || !declared)
                        return rule.emitOpError() << "peer admission requires an expanded composition call inventory";
                    Attribute own;
                    for (auto call : calls) {
                        auto item = dyn_cast<DictionaryAttr>(call);
                        if (failed(exact(item, {"registration", "candidates", "operation", "guard"}, rule, "peer composition call"))) return failure();
                        if (!item.getAs<DictionaryAttr>("registration") || !item.getAs<IntegerAttr>("guard") ||
                                !item.getAs<ArrayAttr>("candidates") || failed(budget.debit(1, rule))) return failure();
                        auto kind = ordinal(item, "operation", names.size());
                        if (failed(kind)) return failure();
                        if (item.getAs<DictionaryAttr>("registration") == consumer.registration &&
                                item.getAs<IntegerAttr>("guard") == row.getAs<IntegerAttr>("guard")) {
                            if (own) return rule.emitOpError() << "peer admission has duplicate consumer invocation";
                            own = names[*kind];
                        }
                    }
                    if (!own) return rule.emitOpError() << "peer admission consumer is outside its composition";
                    SmallVector<Attribute> seen;
                    for (auto name : releases) {
                        if (failed(charge(budget, rule, names.size() + seen.size() + 1, sizeof(Attribute)))) return failure();
                        if (!isa<StringAttr>(name) || name == own || !llvm::is_contained(names, name) || llvm::is_contained(seen, name))
                            return rule.emitOpError() << "peer admission names an invalid release operation";
                        seen.push_back(name);
                    }
                    SmallVector<Attribute> expected;
                    for (auto call : calls) {
                        auto item = cast<DictionaryAttr>(call);
                        auto kind = ordinal(item, "operation", names.size());
                        if (failed(kind)) return failure();
                        if (item.getAs<DictionaryAttr>("registration") == consumer.registration ||
                                !llvm::is_contained(releases, names[*kind])) continue;
                        auto slots = item.getAs<ArrayAttr>("candidates");
                        if (!slots || slots.empty() || failed(charge(budget, rule, 16, 512))) return failure();
                        expected.push_back(builder.getDictionaryAttr({
                            builder.getNamedAttr("registration", item.getAs<DictionaryAttr>("registration")),
                            builder.getNamedAttr("candidate", slots[0]),
                            builder.getNamedAttr("guard", item.getAs<IntegerAttr>("guard")),
                            builder.getNamedAttr("operation", names[*kind])}));
                    }
                    if (declared != builder.getArrayAttr(expected))
                        return rule.emitOpError() << "peer admission release calls differ from composition";

                    // Credit gates are private to this one capture. Allowing the
                    // producer's E at a gate must not expose it to arbitrary users.
                    auto singleUse = [&](Value value, Operation *user, unsigned operand) {
                        if (!value.hasOneUse()) return false;
                        auto &use = *value.use_begin();
                        return use.getOwner() == user && use.getOperandNumber() == operand;
                    };
                    Value credit = rule->getOperand(*capture);
                    Operation *creditUser = rule;
                    unsigned creditOperand = *capture;
                    for (auto rawCall : llvm::reverse(declared)) {
                        auto call = cast<DictionaryAttr>(rawCall);
                        auto joined = credit.getDefiningOp<BitsBinaryOp>();
                        if (!joined || joined.getOpcode() != "or" || !singleUse(credit, creditUser, creditOperand))
                            return rule.emitOpError() << "peer admission credit union differs";
                        const TransactionWriterView *writer = nullptr;
                        for (const auto &candidate : entry.wiring->writers) {
                            if (failed(budget.debit(1, rule))) return failure();
                            if (candidate.registration == call.getAs<DictionaryAttr>("registration")) writer = &candidate;
                        }
                        if (!writer) return failure();
                        auto slot = ordinal(call, "candidate", writer->candidates.size());
                        auto sampled = writerAdmission(entry, writer->rule);
                        if (failed(slot) || failed(sampled)) return failure();
                        auto invocation = ordinal(call, "guard", (*sampled)->controls.size());
                        if (failed(invocation) || (*sampled)->controls[*invocation].kind != SampledControlKind::CallableGuard) return failure();
                        if (failed(budget.debit(states[*state].candidates.size(), rule))) return failure();
                        auto candidate = llvm::find_if(states[*state].candidates, [&](const auto &item) {
                            return item.rule == writer->rule && item.ordinal == *slot &&
                                item.occurrence == size_t(&entry - occurrences.data());
                        });
                        if (candidate == states[*state].candidates.end())
                            return rule.emitOpError() << "peer admission producer belongs to another state or owner";
                        SmallVector<std::pair<uint64_t, bool>> path;
                        auto ancestry = (*sampled)->controls[*invocation].executionPath;
                        for (unsigned depth = 0; ancestry.selectionControl; ++depth) {
                            if (depth >= 128 || failed(charge(budget, rule, 1, sizeof(std::pair<uint64_t, bool>)))) return failure();
                            auto index = *ancestry.selectionControl;
                            if (index >= (*sampled)->controls.size() || (*sampled)->controls[index].kind != SampledControlKind::BranchSelect) return failure();
                            path.push_back({index, ancestry.whenTrue});
                            ancestry = (*sampled)->controls[index].executionPath;
                        }
                        Value active = joined.getRhs();
                        Operation *activeUser = joined;
                        unsigned activeOperand = 1;
                        for (auto [index, polarity] : llvm::reverse(path)) {
                            auto gate = active.getDefiningOp<BitsBinaryOp>();
                            if (!gate || gate.getOpcode() != "and" || !singleUse(active, activeUser, activeOperand))
                                return rule.emitOpError() << "peer admission invocation path differs";
                            Value selector = gate.getRhs();
                            Operation *selectorUser = gate;
                            unsigned selectorOperand = 1;
                            if (!polarity) {
                                auto invert = selector.getDefiningOp<BitsUnaryOp>();
                                if (!invert || invert.getOpcode() != "not" || !singleUse(selector, gate, 1))
                                    return rule.emitOpError() << "peer admission invocation polarity differs";
                                selector = invert.getInput(); selectorUser = invert; selectorOperand = 0;
                            }
                            const auto &control = (*sampled)->controls[index];
                            auto actual = normal(selector, entry.scope);
                            auto wanted = normal(writer->rule->getResult(control.rawResult), entry.scope);
                            if (failed(actual) || failed(wanted) || !sameEndpoint(*actual, *wanted))
                                return rule.emitOpError() << "peer admission branch selector differs";
                            auto terminals = effectTerminals(entry);
                            if (failed(terminals)) return failure();
                            auto terminal = checkTerminal(**terminals, control.id, rule);
                            if (failed(terminal) || failed(charge(budget, rule,
                                    orderedLookupCost(compositionControlUses.size()), sizeof(CompositionControlUse) + 4 * sizeof(void *)))) return failure();
                            compositionControlUses.emplace(size_t(&entry - occurrences.data()), selectorUser,
                                selectorOperand, terminal->getOperation());
                            active = gate.getLhs(); activeUser = gate; activeOperand = 0;
                        }
                        auto actual = normal(active, entry.scope);
                        if (failed(actual) || !sameEndpoint(*actual, candidate->enable))
                            return rule.emitOpError() << "peer admission must use the producer's final commit enable";
                        if (failed(allowUse(entry.scope, activeUser, activeOperand, *state, PrivateRoute::Enable))) return failure();
                        credit = joined.getLhs(); creditUser = joined; creditOperand = 0;
                    }
                    auto tail = normal(credit, entry.scope);
                    if (failed(tail)) return failure();
                    auto zero = literal(*tail, analysis, budget);
                    if (failed(zero) || !zero->has_value() || **zero)
                        return rule.emitOpError() << "peer admission credit must start at zero";
                }
            }
        }
        return success();
    }
