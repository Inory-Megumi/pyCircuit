    // Keep exact endpoint equality as the first proof. Distinct result ports
    // may agree only when they belong to the SAME sampled writer and instance,
    // and their yielded expressions have identical checked AND/NOT/select trees.
    // This does not authorize any capture: compositions() separately requires
    // every original E port (including the first active port) by exact identity.
    FailureOr<bool> sameCompositionEnable(const HardwareIdentityEndpoint &actual,
                                          const HardwareIdentityEndpoint &expected,
                                          Operation *site) {
        auto direct = sameRequiredWritePath(actual, expected, site);
        if (failed(direct) || *direct) return direct;
        auto left = dyn_cast<OpResult>(actual.value);
        auto right = dyn_cast<OpResult>(expected.value);
        if (!left || !right || left.getOwner() != right.getOwner() ||
                !sameScope(actual.scope, expected.scope)) return false;
        auto writer = dyn_cast<RuleOp>(left.getOwner());
        if (!writer || !writer->hasAttr("ac.sampled_admission")) return false;
        auto yielded = cast<YieldOp>(writer.getBody().front().getTerminator());
        auto a = normalBorrowed(yielded.getValues()[left.getResultNumber()], actual.scope);
        auto b = normalBorrowed(yielded.getValues()[right.getResultNumber()], expected.scope);
        if (failed(a) || failed(b)) return failure();

        // These pointers belong to the immutable IdentityMemo, whose entries
        // include the full instance path, bindings and resolved type. They are
        // stable for this proof; the local memo never escapes this writer pair.
        using Pair = std::pair<const HardwareIdentityEndpoint *, const HardwareIdentityEndpoint *>;
        auto less = [](const Pair &x, const Pair &y) {
            std::less<const HardwareIdentityEndpoint *> order;
            return order(x.first, y.first) || (x.first == y.first && order(x.second, y.second));
        };
        std::map<Pair, bool, decltype(less)> memo(less);
        std::function<FailureOr<bool>(Pair, unsigned)> compare;
        compare = [&](Pair pair, unsigned depth) -> FailureOr<bool> {
            if (depth > 128)
                return site->emitOpError() << "composition enable exceeds the structural depth bound";
            if (failed(charge(budget, site, 1, sizeof(Pair) + sizeof(unsigned))) ||
                    failed(payScope(pair.first->scope, budget, site)) ||
                    failed(payScope(pair.second->scope, budget, site))) return failure();
            const auto &lhs = *pair.first;
            const auto &rhs = *pair.second;
            if (sameEndpoint(lhs, rhs)) return true;
            if (!sameScope(lhs.scope, rhs.scope) ||
                    !areEquivalentHardwareTypes(lhs.resolvedType, rhs.resolvedType)) return false;
            if (failed(budget.debit(orderedLookupCost(memo.size()), site))) return failure();
            auto found = memo.find(pair);
            if (found != memo.end()) return found->second;

            auto prove = [&]() -> FailureOr<bool> {
                auto l = literal(lhs, analysis, budget), r = literal(rhs, analysis, budget);
                if (failed(l) || failed(r)) return failure();
                if (l->has_value() || r->has_value())
                    return l->has_value() && r->has_value() && **l == **r;
                auto la = lhs.value.getDefiningOp<BitsBinaryOp>();
                auto ra = rhs.value.getDefiningOp<BitsBinaryOp>();
                auto ln = lhs.value.getDefiningOp<BitsUnaryOp>();
                auto rn = rhs.value.getDefiningOp<BitsUnaryOp>();
                auto ls = lhs.value.getDefiningOp<BitsSelectOp>();
                auto rs = rhs.value.getDefiningOp<BitsSelectOp>();
                bool supported = (la && ra && la.getOpcode() == "and" && ra.getOpcode() == "and") ||
                                 (ln && rn && ln.getOpcode() == "not" && rn.getOpcode() == "not") ||
                                 (ls && rs);
                if (!supported) return false;
                // Compare select condition, true arm and false arm in order.
                // Do not simplify select(C, 1, 0) to C: keep four-state semantics
                // and the actual path/final-admission expression intact.
                auto leftOp = lhs.value.getDefiningOp(), rightOp = rhs.value.getDefiningOp();
                if (leftOp->getNumOperands() != rightOp->getNumOperands()) return false;
                for (auto [lv, rv] : llvm::zip(leftOp->getOperands(), rightOp->getOperands())) {
                    auto le = normalBorrowed(lv, lhs.scope), re = normalBorrowed(rv, rhs.scope);
                    if (failed(le) || failed(re)) return failure();
                    auto same = compare({*le, *re}, depth + 1);
                    if (failed(same) || !*same) return same;
                }
                return true;
            };
            auto result = prove();
            if (failed(result)) return failure();
            if (failed(budget.debit(orderedLookupCost(memo.size()), site)) ||
                    failed(charge(budget, site, 1,
                                  sizeof(decltype(memo)::value_type) + 4 * sizeof(void *)))) return failure();
            memo.emplace(pair, *result);
            return *result;
        };
        return compare({*a, *b}, 0);
    }

#include "HardwareComposeSelectionProof.inc"
#include "HardwareComposeCallsProof.inc"

    LogicalResult compositions() {
        for (const auto &entry : occurrences) {
            if (!entry.wiring) continue;
            for (auto rule : entry.module->getRegion(0).front().getOps<RuleOp>()) {
                if (failed(budget.debit(1, rule))) return failure();
                auto raw = rule->getAttr("ac.state_composition");
                if (!raw) continue;
                auto contract = dyn_cast<DictionaryAttr>(raw);
                if (contract && contract.get("calls")) {
                    if (failed(composeCalls(entry, rule, contract))) return failure();
                    continue;
                }
                if (failed(exact(contract, {"states", "operations"}, rule, "state composition"))) return failure();
                auto targets = contract.getAs<ArrayAttr>("states");
                auto operations = contract.getAs<ArrayAttr>("operations");
                if (!targets || targets.empty() || !operations || operations.empty() || rule->hasAttr("ac.sampled_admission"))
                    return rule.emitOpError() << "state composition requires nonempty state and operation inventories";
                uint64_t slots = SourceCheckBudget::add(targets.size(), SourceCheckBudget::multiply(
                        operations.size(), SourceCheckBudget::add(1, SourceCheckBudget::multiply(2, targets.size()))));
                // Each typed slot reserves one bounded adapter record. The
                // helper already multiplies this per-slot storage by slots.
                if (failed(charge(budget, rule, slots, 64))) return failure();
                uint64_t count = targets.size(), base = count + operations.size() * (count + 1);
                uint64_t extra = base;
                SmallVector<size_t> indices;
                for (auto targetID : targets) {
                    auto id = dyn_cast<DictionaryAttr>(targetID);
                    if (!id || failed(wholeStateID(id, rule))) return failure();
                    auto index = target(entry, id);
                    if (failed(index)) return failure();
                    if (llvm::is_contained(indices, *index) || states[*index].composed)
                        return rule.emitOpError() << "a state cannot belong to multiple compositions";
                    indices.push_back(*index);
                }
                for (auto row : operations) {
                    auto operation = dyn_cast<DictionaryAttr>(row);
                    if (!operation) return rule.emitOpError() << "composition operation row must be a dictionary";
                    if (!operation.empty()) extra += count - 1;
                }
                if (rule->getNumOperands() != extra || rule->getNumResults() != count + 1)
                    return rule.emitOpError() << "composition typed input/result inventory differs";
                for (unsigned i = 0; i < count; ++i) {
                    auto old = normal(rule->getOperand(i), entry.scope);
                    auto q = normal(states[indices[i]].storage->getResult(0), states[indices[i]].scope);
                    if (failed(old) || failed(q) || !sameEndpoint(*old, *q))
                        return rule.emitOpError() << "composition old value is not the target's committed state";
                }
                SmallVector<SmallVector<const StateCandidate *>> contributors(count);
                llvm::DenseSet<Operation *> registrations;
                extra = base;
                for (auto [ordinal, rawOperation] : llvm::enumerate(operations)) {
                    auto operation = cast<DictionaryAttr>(rawOperation);
                    uint64_t start = count + ordinal * (count + 1);
                    if (failed(bitOne(rule->getOperand(start), analysis, entry.bindings, rule, budget))) return failure();
                    if (operation.empty()) {
                        auto active = normal(rule->getOperand(start), entry.scope);
                        auto zero = succeeded(active) ? literal(*active, analysis, budget) : FailureOr<std::optional<bool>>(failure());
                        if (failed(zero) || !zero->has_value() || **zero)
                            return rule.emitOpError() << "absent compose operation must be inactive";
                        for (unsigned i = 0; i < count; ++i) {
                            auto value = normal(rule->getOperand(start + 1 + i), entry.scope);
                            auto old = normal(rule->getOperand(i), entry.scope);
                            if (failed(value) || failed(old) || !sameEndpoint(*value, *old))
                                return rule.emitOpError() << "absent compose candidate must hold old state";
                        }
                        continue;
                    }
                    if (failed(exact(operation, {"registration", "candidates"}, rule, "composition operation"))) return failure();
                    auto registration = operation.getAs<DictionaryAttr>("registration");
                    auto ordinals = operation.getAs<ArrayAttr>("candidates");
                    const TransactionWriterView *writer = nullptr;
                    if (failed(budget.debit(entry.wiring->writers.size(), rule))) return failure();
                    for (const auto &candidate : entry.wiring->writers)
                        if (candidate.registration == registration) writer = &candidate;
                    if (!writer || !ordinals || ordinals.size() != count || !registrations.insert(writer->rule).second)
                        return rule.emitOpError() << "composition operation must identify one distinct outer writer";
                    auto active = normal(rule->getOperand(start), entry.scope);
                    if (failed(active)) return failure();
                    for (unsigned i = 0; i < count; ++i) {
                        auto rawIndex = dyn_cast<IntegerAttr>(ordinals[i]);
                        if (!rawIndex || !rawIndex.getType().isSignlessInteger(64) || rawIndex.getInt() < 0 ||
                                uint64_t(rawIndex.getInt()) >= writer->candidates.size())
                            return rule.emitOpError() << "composition candidate index is invalid";
                        unsigned slot = rawIndex.getInt();
                        auto &state = states[indices[i]];
                        if (failed(budget.debit(state.candidates.size(), rule))) return failure();
                        auto contributor = llvm::find_if(state.candidates, [&](const auto &candidate) {
                            return candidate.rule == writer->rule && candidate.ordinal == slot &&
                                          candidate.occurrence == size_t(&entry - occurrences.data());
                        });
                        if (contributor == state.candidates.end()) return rule.emitOpError() << "composition candidate belongs to another state or instance";
                        auto value = normal(rule->getOperand(start + 1 + i), entry.scope);
                        auto sameEnable = sameCompositionEnable(*active, contributor->enable, rule);
                        if (failed(value) || !sameEndpoint(*value, contributor->data))
                            return rule.emitOpError() << "composition candidate differs from its writer";
                        if (failed(sameEnable) || !*sameEnable)
                            return rule.emitOpError() << "composition final commit enable differs from its writer at target " << i;
                        if (failed(allowUse(entry.scope, rule, start + 1 + i, indices[i], PrivateRoute::Data))) return failure();
                        unsigned enableInput = i == 0 ? start : extra++;
                        auto enabled = normal(rule->getOperand(enableInput), entry.scope);
                        if (failed(enabled) || !sameEndpoint(*enabled, contributor->enable) ||
                                failed(allowUse(entry.scope, rule, enableInput, indices[i], PrivateRoute::Enable))) return failure();
                        contributors[i].push_back(&*contributor);
                    }
                }
                auto &body = rule.getBody().front();
                auto yielded = cast<YieldOp>(body.getTerminator());
                Value enabled = yielded.getValues().back();
                for (unsigned op = operations.size(); op > 1; --op) {
                    auto gate = enabled.getDefiningOp<BitsBinaryOp>();
                    if (!gate || gate.getOpcode() != "or" || gate.getRhs() != body.getArgument(count + (op - 1) * (count + 1)))
                        return rule.emitOpError() << "composition enable must combine the exact final operation enables";
                    enabled = gate.getLhs();
                }
                if (enabled != body.getArgument(count)) return rule.emitOpError() << "composition first enable differs";
                for (unsigned i = 0; i < count; ++i) {
                    auto &state = states[indices[i]];
                    if (contributors[i].size() != state.candidates.size()) return rule.emitOpError() << "composition omits a state writer";
                    auto data = normal(rule->getResult(i), entry.scope);
                    auto enable = normal(rule->getResult(count), entry.scope);
                    if (failed(data) || failed(enable)) return failure();
                    state.candidates.clear();
                    state.candidates.push_back({rule, i, size_t(&entry - occurrences.data()), *data, *enable});
                    state.data = *data; state.enable = *enable; state.writer = rule;
                    state.unordered = false; state.composed = true;
                    if (failed(privateRoute(rule->getResult(i), entry.scope, indices[i], PrivateRoute::Data)) ||
                            failed(privateRoute(rule->getResult(count), entry.scope, indices[i], PrivateRoute::Enable))) return failure();
                }
            }
        }
        return success();
    }
