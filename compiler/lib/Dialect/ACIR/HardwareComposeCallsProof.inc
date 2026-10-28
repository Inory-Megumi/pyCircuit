    struct CompositionCall {
        const TransactionWriterView *writer = nullptr;
        unsigned operation = 0, start = 0;
        uint64_t guard = 0;
        SmallVector<std::pair<Value, bool>> path;
        Value active;
    };

    // Scoped endpoint adapter for the existing bounded, four-state grant proof.
    // The immutable graph includes full bindings and actual instance identity.
    LogicalResult compositionCallExclusion(const Occurrence &entry, RuleOp rule,
                                            ArrayRef<CompositionCall> calls, Value zero) {
        using Core = HardwareGrantProof;
        using Node = Core::Node;
        struct Item { std::optional<HardwareIdentityEndpoint> endpoint; Core::NodeView view; };
        SmallVector<Item, 0> nodes;
        using Key = std::tuple<size_t, const void *, const void *>;
        std::map<Key, Node> index;
        auto bind = [&](const HardwareIdentityEndpoint &endpoint) -> FailureOr<Node> {
            auto scope = occurrenceFor(endpoint.scope);
            if (failed(scope) || failed(budget.debit(orderedLookupCost(index.size()), rule))) return failure();
            Key key{*scope, endpoint.value.getAsOpaquePointer(), endpoint.resolvedType.getAsOpaquePointer()};
            auto found = index.find(key); if (found != index.end()) return found->second;
            if (failed(payScope(endpoint.scope, budget, rule)) ||
                    failed(charge(budget, rule, 1, sizeof(Item) + sizeof(Key) + 4 * sizeof(void *)))) return failure();
            Node id = nodes.size(); nodes.push_back({endpoint, {}}); index.emplace(key, id); return id;
        };
        auto valueNode = [&](Value value) -> FailureOr<Node> {
            auto endpoint = normal(value, entry.scope); if (failed(endpoint)) return failure(); return bind(*endpoint);
        };
        auto combine = [&](Node a, Node b, Core::NodeView::Kind kind) -> FailureOr<Node> {
            if (failed(charge(budget, rule, 1, sizeof(Item)))) return failure();
            Core::NodeView view; view.kind = kind; view.width = 1; view.operands.push_back(a);
            if (kind != Core::NodeView::Not) view.operands.push_back(b);
            Node id = nodes.size(); nodes.push_back({{}, std::move(view)}); return id;
        };
        std::function<FailureOr<Node>(Node, unsigned)> canonical = [&](Node id, unsigned depth) -> FailureOr<Node> {
            if (depth >= 128 || id >= nodes.size() || failed(budget.debit(1, rule))) return failure();
            if (!nodes[id].endpoint) return id;
            auto endpoint = *nodes[id].endpoint;
            auto result = dyn_cast<OpResult>(endpoint.value);
            auto writer = result ? dyn_cast<RuleOp>(result.getOwner()) : RuleOp();
            if (!writer) return id;
            auto yielded = cast<YieldOp>(writer.getBody().front().getTerminator());
            auto source = normal(yielded.getValues()[result.getResultNumber()], endpoint.scope);
            if (failed(source)) return failure();
            auto child = bind(*source); if (failed(child)) return failure();
            return canonical(*child, depth + 1);
        };
        auto inspect = [&](Node id) -> FailureOr<Core::NodeView> {
            if (id >= nodes.size() || failed(budget.debit(1, rule))) return failure();
            if (!nodes[id].endpoint) return nodes[id].view;
            auto endpoint = *nodes[id].endpoint;
            auto bindings = scopeBindings(endpoint.scope, analysis, budget, rule);
            if (failed(bindings)) return failure();
            Core::NodeView view;
            if (!isa<BitsType>(endpoint.resolvedType)) return view;
            auto width = analysis.getPackedWidth(endpoint.resolvedType, *bindings, rule);
            if (failed(width)) return failure(); view.width = *width;
            auto *operation = endpoint.value.getDefiningOp();
            if (auto literal = dyn_cast_or_null<BitsConstantOp>(operation)) {
                if (failed(payAttribute(literal.getValue(), budget, literal))) return failure();
                auto evaluated = analysis.evaluateStatic(literal.getValue(), *bindings, literal);
                if (failed(evaluated)) return failure();
                if (auto number = dyn_cast<MathIntAttr>(*evaluated)) {
                    if (failed(budget.debit(number.getCanonicalValue().size() + *width / 64 + 1, rule))) return failure();
                    llvm::APSInt integer(number.getCanonicalValue());
                    if (!integer.isNegative() && integer.getActiveBits() <= *width) view.fullyKnown = Core::Constant{number, *width};
                }
                return view;
            }
            if (auto unary = dyn_cast_or_null<BitsUnaryOp>(operation); unary && unary.getOpcode() == "not") view.kind = Core::NodeView::Not;
            else if (auto binary = dyn_cast_or_null<BitsBinaryOp>(operation)) {
                if (binary.getOpcode() == "and") view.kind = Core::NodeView::And;
                if (binary.getOpcode() == "or") view.kind = Core::NodeView::Or;
            } else if (isa_and_nonnull<BitsSelectOp>(operation)) view.kind = Core::NodeView::Select;
            else if (auto compare = dyn_cast_or_null<BitsCompareOp>(operation)) {
                if (compare.getPredicate() == "eq") view.kind = Core::NodeView::Eq;
                if (compare.getPredicate() == "ne") view.kind = Core::NodeView::Ne;
                if (compare.getPredicate() == "case_eq") {
                    auto left = normal(compare.getLhs(), endpoint.scope), right = normal(compare.getRhs(), endpoint.scope);
                    if (failed(left) || failed(right)) return failure();
                    auto width = analysis.getPackedWidth(left->resolvedType, *bindings, compare);
                    auto constant = literal(*right, analysis, budget);
                    if (failed(width) || failed(constant)) return failure();
                    if (*width == 1 && constant->has_value() && **constant) {
                        if (failed(analysis.verifyResolvedOperation(compare, *bindings))) return failure();
                        auto operand = bind(*left); if (failed(operand)) return failure();
                        view.kind = Core::NodeView::IsTrue; view.operands.push_back(*operand);
                        return view;
                    }
                }
            }
            if (view.kind != Core::NodeView::Raw) {
                if (failed(analysis.verifyResolvedOperation(operation, *bindings))) return failure();
                for (Value value : operation->getOperands()) {
                    auto child = normal(value, endpoint.scope); if (failed(child)) return failure();
                    auto operand = bind(*child); if (failed(operand)) return failure(); view.operands.push_back(*operand);
                }
            }
            return view;
        };
        auto debit = [&](uint64_t work) { return succeeded(budget.debit(work, rule)); };
        Core proof(canonical, inspect, debit);
        auto zeroNode = valueNode(zero); if (failed(zeroNode)) return failure();
        auto one = combine(*zeroNode, 0, Core::NodeView::Not); if (failed(one)) return failure();
        SmallVector<Node> paths, active;
        for (const auto &call : calls) {
            Node path = *one;
            for (auto [condition, polarity] : call.path) {
                auto conditionNode = valueNode(condition); if (failed(conditionNode)) return failure();
                if (!polarity) conditionNode = combine(*conditionNode, 0, Core::NodeView::Not);
                if (failed(conditionNode)) return failure();
                auto joined = combine(path, *conditionNode, Core::NodeView::And); if (failed(joined)) return failure(); path = *joined;
            }
            auto enabled = valueNode(call.active); if (failed(enabled)) return failure();
            if (failed(charge(budget, rule, 1, 2 * sizeof(Node)))) return failure();
            paths.push_back(path); active.push_back(*enabled);
        }
        for (size_t i = 0; i < calls.size(); ++i) for (size_t j = 0; j < i; ++j) {
            if (failed(budget.debit(1, rule))) return failure();
            bool sameWriter = calls[i].writer == calls[j].writer;
            if (!sameWriter && calls[i].operation != calls[j].operation) continue;
            auto disjoint = proof.disjoint(sameWriter ? paths[i] : active[i], sameWriter ? paths[j] : active[j]);
            if (failed(disjoint)) return rule.emitOpError()
                << "composition invocation exclusion proof failed: " << proof.failureReason();
            if (!*disjoint) return rule.emitOpError() << "composition invocation paths are not mutually exclusive";
        }
        // All path controls come from checked sampled branches. On a successful
        // transaction they are known, so E => OR(call activities) proves complete
        // coverage without simplifying X/Z paths or changing runtime checks.
        for (size_t i = 0; i < calls.size(); ++i) {
            if (failed(budget.debit(i + 1, rule))) return failure();
            if (llvm::any_of(calls.take_front(i), [&](const auto &prior) {
                    return prior.writer == calls[i].writer;
                })) continue;
            Node covered = *zeroNode;
            for (size_t j = 0; j < calls.size(); ++j) {
                if (failed(budget.debit(1, rule))) return failure();
                if (calls[i].writer != calls[j].writer) continue;
                auto joined = combine(covered, active[j], Core::NodeView::Or); if (failed(joined)) return failure(); covered = *joined;
            }
            auto missing = combine(covered, 0, Core::NodeView::Not);
            auto enabled = valueNode(rule->getOperand(calls[i].start));
            if (failed(missing) || failed(enabled)) return failure();
            auto admission = writerAdmission(entry, calls[i].writer->rule);
            if (failed(admission)) return failure();
            auto fire = valueNode((*admission)->fire);
            if (failed(fire)) return failure();
            auto boundary = canonical(*fire, 0);
            if (failed(boundary)) return failure();
            auto boundaryView = inspect(*boundary);
            if (failed(boundaryView)) return failure();
            if (!boundaryView->width || *boundaryView->width != 1)
                return rule.emitOpError() << "composition writer enable must be one bit";
            // writerAdmission authenticates the final transaction fire. Keep
            // each resource's write-intent/path mask and all checked candidate
            // origins, but widen this shared fire to an arbitrary four-state
            // bit for coverage. No admission circuit or runtime check changes.
            // The fresh proof owns its caches; exclusion and other writers
            // must never inherit this query's opaque boundary.
            Core coverage(canonical, [&](Node id) -> FailureOr<Core::NodeView> {
                if (id == *boundary) {
                    Core::NodeView view;
                    view.width = 1;
                    return view;
                }
                return inspect(id);
            }, debit);
            auto complete = coverage.disjoint(*enabled, *missing);
            // Partial invocation trees can depend on E's path facts. Retain
            // the original bounded proof when the widened query is inconclusive.
            if (failed(complete) || !*complete)
                complete = proof.disjoint(*enabled, *missing);
            if (failed(complete)) return rule.emitOpError()
                << "composition call coverage proof failed: " << proof.failureReason();
            if (!*complete) return rule.emitOpError() << "composition calls omit an active writer path";
        }
        return success();
    }

    LogicalResult composeCalls(const Occurrence &entry, RuleOp rule, DictionaryAttr contract) {
        auto writeViews = contract.getAs<ArrayAttr>("writes");
        if (writeViews) {
            if (writeViews.empty() || failed(exact(contract, {"states", "operations", "calls", "writes"}, rule, "state composition calls"))) return failure();
        } else if (failed(exact(contract, {"states", "operations", "calls"}, rule, "state composition calls"))) return failure();
        auto targets = contract.getAs<ArrayAttr>("states"), operations = contract.getAs<ArrayAttr>("operations"), rows = contract.getAs<ArrayAttr>("calls");
        if (!targets || targets.empty() || !operations || operations.empty() || !rows || rows.empty() ||
                rule->hasAttr("ac.sampled_admission") || !rule.getBody().hasOneBlock()) return rule.emitOpError() << "invalid composition call inventories";
        // Pay actual reserved storage once. charge() already multiplies count
        // by the per-element size; passing a total size would square the cost.
        using Contributors = SmallVector<const StateCandidate *>;
        if (failed(charge(budget, rule, targets.size(), sizeof(size_t) + sizeof(Contributors))) ||
                failed(charge(budget, rule, operations.size(), sizeof(Attribute) + sizeof(Value))) ||
                failed(charge(budget, rule, rows.size(), sizeof(CompositionCall))) ||
                failed(charge(budget, rule, SourceCheckBudget::multiply(targets.size(), rows.size()),
                              sizeof(const StateCandidate *)))) return failure();
        unsigned count = targets.size(), input = count;
        SmallVector<size_t> indices;
        indices.reserve(count);
        for (auto targetID : targets) {
            auto id = dyn_cast<DictionaryAttr>(targetID);
            if (!id || failed(wholeStateID(id, rule))) return failure();
            auto index = target(entry, id); if (failed(index)) return failure();
            if (failed(budget.debit(indices.size() + 1, rule))) return failure();
            if (llvm::is_contained(indices, *index) || states[*index].composed) return rule.emitOpError() << "duplicate composition target";
            indices.push_back(*index);
        }
        SmallVector<Attribute> names;
        names.reserve(operations.size());
        for (auto name : operations) {
            if (failed(budget.debit(names.size() + 1, rule))) return failure();
            if (!isa<StringAttr>(name) || llvm::is_contained(names, name)) return rule.emitOpError() << "invalid composition operation names";
            names.push_back(name);
        }
        auto &body = rule.getBody().front();
        if (body.getNumArguments() != rule->getNumOperands() || rule->getNumResults() != count + 1 || rule->getNumOperands() < count)
            return rule.emitOpError() << "composition call typed inventory differs";
        for (unsigned i = 0; i < count; ++i) {
            auto old = normal(rule->getOperand(i), entry.scope);
            auto q = normal(states[indices[i]].storage->getResult(0), states[indices[i]].scope);
            if (failed(old) || failed(q) || !sameEndpoint(*old, *q)) return rule.emitOpError() << "composition old value differs from committed state";
        }
        SmallVector<CompositionCall> calls;
        calls.reserve(rows.size());
        SmallVector<Contributors> contributors(count);
        for (auto &list : contributors) list.reserve(rows.size());
        auto ordinal = [&](DictionaryAttr row, StringRef name, uint64_t bound) -> FailureOr<uint64_t> {
            auto value = row.getAs<IntegerAttr>(name);
            if (!value || !value.getType().isSignlessInteger(64) || value.getInt() < 0 || uint64_t(value.getInt()) >= bound)
                return rule.emitOpError() << "invalid composition call " << name;
            return uint64_t(value.getInt());
        };
        for (auto raw : rows) {
            auto row = dyn_cast<DictionaryAttr>(raw);
            if (failed(exact(row, {"registration", "candidates", "operation", "guard"}, rule, "composition call"))) return failure();
            const TransactionWriterView *writer = nullptr;
            if (failed(budget.debit(entry.wiring->writers.size(), rule))) return failure();
            for (const auto &candidate : entry.wiring->writers)
                if (candidate.registration == row.getAs<DictionaryAttr>("registration")) writer = &candidate;
            auto slots = row.getAs<ArrayAttr>("candidates");
            if (!writer || !slots || slots.size() != count) return rule.emitOpError() << "composition call writer differs";
            auto sampled = writerAdmission(entry, writer->rule); if (failed(sampled)) return failure();
            auto kind = ordinal(row, "operation", operations.size()), guard = ordinal(row, "guard", (*sampled)->controls.size());
            if (failed(kind) || failed(guard) || (*sampled)->controls[*guard].kind != SampledControlKind::CallableGuard)
                return rule.emitOpError() << "composition call must identify an actual callable guard";
            if (failed(budget.debit(calls.size() + 1, rule))) return failure();
            for (const auto &prior : calls)
                if (prior.writer == writer && prior.guard == *guard) return rule.emitOpError() << "composition duplicates an invocation";
            CompositionCall call; call.writer = writer; call.operation = *kind; call.guard = *guard; call.start = input;
            if (input + 2 * count > rule->getNumOperands()) return rule.emitOpError() << "composition call captures are truncated";
            auto active = normal(rule->getOperand(input), entry.scope); if (failed(active)) return failure();
            for (unsigned i = 0; i < count; ++i) {
                auto slot = dyn_cast<IntegerAttr>(slots[i]);
                if (!slot || !slot.getType().isSignlessInteger(64) || slot.getInt() < 0 || uint64_t(slot.getInt()) >= writer->candidates.size())
                    return rule.emitOpError() << "composition candidate index is invalid";
                auto &state = states[indices[i]];
                if (failed(budget.debit(state.candidates.size(), rule))) return failure();
                auto candidate = llvm::find_if(state.candidates, [&](const auto &value) {
                    return value.rule == writer->rule && value.ordinal == uint64_t(slot.getInt()) &&
                           value.occurrence == size_t(&entry - occurrences.data());
                });
                if (candidate == state.candidates.end()) return rule.emitOpError() << "composition candidate belongs to another state or instance";
                auto enable = normal(rule->getOperand(input), entry.scope), data = normal(rule->getOperand(input + 1), entry.scope);
                auto same = sameCompositionEnable(*active, candidate->enable, rule);
                if (failed(enable) || failed(data) || failed(same) || !*same ||
                        !sameEndpoint(*enable, candidate->enable) || !sameEndpoint(*data, candidate->data))
                    return rule.emitOpError() << "composition call candidate or final enable differs";
                if (failed(allowUse(entry.scope, rule, input, indices[i], PrivateRoute::Enable)) ||
                        failed(allowUse(entry.scope, rule, input + 1, indices[i], PrivateRoute::Data))) return failure();
                if (failed(budget.debit(contributors[i].size() + 1, rule))) return failure();
                if (!llvm::is_contained(contributors[i], &*candidate)) contributors[i].push_back(&*candidate);
                input += 2;
            }
            auto path = (*sampled)->controls[*guard].executionPath;
            for (unsigned depth = 0; path.selectionControl; ++depth) {
                if (depth >= 128 || failed(budget.debit(1, rule)) || input == rule->getNumOperands()) return failure();
                const auto &control = (*sampled)->controls[*path.selectionControl];
                if (control.kind != SampledControlKind::BranchSelect) return failure();
                auto actual = normal(rule->getOperand(input), entry.scope);
                auto expected = normal(writer->rule->getResult(control.rawResult), entry.scope);
                if (failed(actual) || failed(expected) || !sameEndpoint(*actual, *expected))
                    return rule.emitOpError() << "composition invocation path control differs";
                auto terminals = effectTerminals(entry);
                if (failed(terminals)) return failure();
                auto terminal = checkTerminal(**terminals, control.id, rule);
                if (failed(terminal) || failed(charge(budget, rule,
                        orderedLookupCost(compositionControlUses.size()),
                        sizeof(CompositionControlUse) + 4 * sizeof(void *)))) return failure();
                // Only this exact raw branch-check endpoint may additionally
                // reach this authenticated composer capture. Its original
                // guard_known terminal remains mandatory and private.
                compositionControlUses.emplace(size_t(&entry - occurrences.data()),
                    rule.getOperation(), input, terminal->getOperation());
                if (failed(charge(budget, rule, 1, sizeof(std::pair<Value, bool>)))) return failure();
                call.path.push_back({body.getArgument(input++), path.whenTrue});
                path = control.executionPath;
            }
            calls.push_back(std::move(call));
        }
#include "HardwareComposeWritesInputs.inc"
        if (input != rule->getNumOperands()) return rule.emitOpError() << "composition call capture count differs";
        auto cursor = body.begin();
        if (cursor == body.end() || !isa<BitsConstantOp>(*cursor)) return rule.emitOpError() << "composition calls require inactive literal";
        Value zero = (cursor++)->getResult(0);
        auto zeroEndpoint = normal(zero, entry.scope); if (failed(zeroEndpoint)) return failure();
        auto zeroFact = literal(*zeroEndpoint, analysis, budget);
        if (failed(zeroFact) || !zeroFact->has_value() || **zeroFact) return rule.emitOpError() << "composition inactive literal differs";
        auto take = [&](StringRef name, ArrayRef<Value> operands, StringRef opcode = {}) -> FailureOr<Value> {
            if (failed(budget.debit(1 + operands.size(), rule)) || cursor == body.end()) return failure();
            Operation *op = &*cursor++;
            auto actualOpcode = op->getAttrOfType<StringAttr>("opcode");
            if (op->getName().getStringRef() != name || op->getNumResults() != 1 || !llvm::equal(op->getOperands(), operands) ||
                    (!opcode.empty() && (!actualOpcode || actualOpcode.getValue() != opcode)))
                return rule.emitOpError() << "composition invocation adapter differs";
            return op->getResult(0);
        };
        for (auto &call : calls) {
            Value active = body.getArgument(call.start);
            for (auto [condition, polarity] : call.path) {
                if (!polarity) {
                    auto inverted = take(BitsUnaryOp::getOperationName(), {condition}, "not");
                    if (failed(inverted)) return failure(); condition = *inverted;
                }
                auto gated = take(BitsBinaryOp::getOperationName(), {active, condition}, "and");
                if (failed(gated)) return failure(); active = *gated;
            }
            call.active = active;
        }
        SmallVector<Value> activities;
        activities.reserve(operations.size());
        for (unsigned kind = 0; kind < operations.size(); ++kind) {
            Value active = zero;
            SmallVector<Value> values;
            if (failed(charge(budget, rule, count, sizeof(Value)))) return failure();
            values.reserve(count);
            for (unsigned i = 0; i < count; ++i) values.push_back(body.getArgument(i));
            for (const auto &call : calls) {
                if (failed(budget.debit(1, rule))) return failure();
                if (call.operation != kind) continue;
                auto joined = take(BitsBinaryOp::getOperationName(), {active, call.active}, "or");
                if (failed(joined)) return failure(); active = *joined;
                for (unsigned i = 0; i < count; ++i) {
                    if (!isa<BitsType>(values[i].getType())) {
                        auto selected = compositionSelection(rule, cursor, entry.bindings,
                            call.active, body.getArgument(call.start + 2 * i + 1), values[i]);
                        if (failed(selected)) return failure();
                        values[i] = *selected;
                        continue;
                    }
                    auto selected = take(BitsSelectOp::getOperationName(),
                        {call.active, body.getArgument(call.start + 2 * i + 1), values[i]});
                    if (failed(selected)) return failure(); values[i] = *selected;
                }
            }
            activities.push_back(active);
        }
#include "HardwareComposeWritesProof.inc"
        if (failed(compositionCallExclusion(entry, rule, calls, zero))) return failure();
        auto yielded = cast<YieldOp>(body.getTerminator());
        Value enabled = yielded.getValues().back();
        for (unsigned op = activities.size(); op > 1; --op) {
            auto gate = enabled.getDefiningOp<BitsBinaryOp>();
            if (!gate || gate.getOpcode() != "or" || gate.getRhs() != activities[op - 1]) return rule.emitOpError() << "composition final enable differs";
            enabled = gate.getLhs();
        }
        if (enabled != activities.front()) return rule.emitOpError() << "composition first enable differs";
        for (unsigned i = 0; i < count; ++i) {
            auto &state = states[indices[i]];
            if (contributors[i].size() != state.candidates.size()) return rule.emitOpError() << "composition omits a state writer";
            auto data = normal(rule->getResult(i), entry.scope), enable = normal(rule->getResult(count), entry.scope);
            if (failed(data) || failed(enable)) return failure();
            state.candidates.clear();
            state.candidates.push_back({rule, i, size_t(&entry - occurrences.data()), *data, *enable});
            state.data = *data; state.enable = *enable; state.writer = rule;
            state.unordered = false; state.composed = true;
            if (failed(privateRoute(rule->getResult(i), entry.scope, indices[i], PrivateRoute::Data)) ||
                    failed(privateRoute(rule->getResult(count), entry.scope, indices[i], PrivateRoute::Enable))) return failure();
        }
        return success();
    }
