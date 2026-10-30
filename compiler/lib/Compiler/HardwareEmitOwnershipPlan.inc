// Occurrence-relative scopes of the original graph. Relays carry exact values;
// they do not recompute expressions or change an original resource event.
LogicalResult prepareRtlOwnershipScopes(HardwareEmitContext &context,
    const llvm::DenseSet<Operation *> &business, const llvm::DenseSet<Operation *> &protectedEnables) {
    struct Candidate { Operation *operation; SmallVector<ac::InstanceOp> path; };
    llvm::DenseMap<Operation *, SmallVector<Candidate>> candidates;
    for (auto caller : context.package.getOps<ac::ModuleOp>()) {
        if (!context.rtlActiveDefinitions.contains(caller)) continue;
        caller.walk([&](Operation *operation) {
            if (!operation->getNumResults() || operation->getNumRegions() ||
                !mlir::isMemoryEffectFree(operation) || isa<ac::InstanceOp, ac::CollectionOp>(operation) ||
                protectedEnables.contains(operation) || (context.isSynthesis() && !business.contains(operation)) ||
                isa<ac::BitsConstantOp, ac::BitsConstant4Op, ac::EnumCreateOp>(operation)) return;
            if (operation->getNumResults() == 1 &&
                rtlOwnershipSource(operation->getResult(0), &context) != operation->getResult(0)) return;
            auto owners = ac::sourceRtlOwners(operation->getLoc());
            if (owners.size() > 1) {
                context.rtlOwnershipNotes.emplace_back(llvm::json::Object{
                    {"status", "shared"}, {"source", caller.getSymName().str()},
                    {"opcode", operation->getName().getStringRef().str()}, {"owners", owners.size()},
                    {"placement", "original common ancestor; one optimized operator"}});
                return;
            }
            if (owners.empty()) return;
            auto root = owners[0].getAs<FlatSymbolRefAttr>("root");
            auto target = owners[0].getAs<FlatSymbolRefAttr>("definition");
            auto path = owners[0].getAs<ArrayAttr>("path");
            if (!root || !target || !path || path.empty() || root.getValue() != caller.getSymName()) return;
            for (auto *parent = operation->getParentOp(); parent != caller; parent = parent->getParentOp())
                if (!isa<ac::RuleOp>(parent)) {
                    context.rtlOwnershipNotes.emplace_back(llvm::json::Object{{"source", caller.getSymName().str()},
                        {"status", "retained"}, {"reason", "operation belongs to an indivisible nested region"}});
                    return;
                }
            Candidate candidate{operation, {}};
            auto current = caller;
            for (Attribute occurrence : path) {
                ac::InstanceOp selected;
                for (auto instance : current.getBody().front().getOps<ac::InstanceOp>())
                    if (instance.getOccurrence() == occurrence) selected = instance;
                auto child = selected ? dyn_cast_or_null<ac::ModuleOp>(context.analysis.resolveCallee(selected)) : ac::ModuleOp();
                if (!child) return;
                candidate.path.push_back(selected);
                current = child;
            }
            if (current.getSymName() == target.getValue()) candidates[caller].push_back(std::move(candidate));
        });
    }
    // Each variant is keyed by its parent occurrence scope, not only the
    // shared source allocation. A reused definition retains independent state.
    std::function<LogicalResult(ac::ModuleOp, RtlOwnershipPartition *)> populate;
    std::function<FailureOr<RtlOwnershipPartition *>(ac::InstanceOp, RtlOwnershipPartition *)> ensure;
    ensure = [&](ac::InstanceOp allocation, RtlOwnershipPartition *parent) -> FailureOr<RtlOwnershipPartition *> {
        if (auto existing = context.rtlPartition(allocation, parent)) return const_cast<RtlOwnershipPartition *>(existing);
        auto added = std::make_unique<RtlOwnershipPartition>();
        added->allocation = allocation;
        added->caller = allocation->getParentOfType<ac::ModuleOp>();
        added->definition = cast<ac::ModuleOp>(context.analysis.resolveCallee(allocation));
        added->parent = parent;
        auto *result = added.get();
        context.rtlPartitions.push_back(std::move(added));
        if (failed(populate(result->definition, result))) return failure();
        return result;
    };
    populate = [&](ac::ModuleOp definition, RtlOwnershipPartition *parent) -> LogicalResult {
        for (const auto &candidate : candidates[definition]) {
            auto *destination = parent;
            for (auto allocation : candidate.path) {
                auto next = ensure(allocation, destination);
                if (failed(next)) return failure();
                destination = *next;
            }
            if (destination->moved.insert(candidate.operation).second)
                destination->operations.push_back(candidate.operation);
        }
        return success();
    };
    for (auto definition : context.package.getOps<ac::ModuleOp>())
        if (context.rtlActiveDefinitions.contains(definition) && failed(populate(definition, nullptr))) return failure();

    std::function<void(ac::ModuleOp, const RtlOwnershipPartition *)> activate;
    activate = [&](ac::ModuleOp definition, const RtlOwnershipPartition *parent) {
        if (parent) {
            auto *mutableParent = const_cast<RtlOwnershipPartition *>(parent);
            if (mutableParent->active) return;
            mutableParent->active = true;
        } else if (!context.rtlBaseDefinitions.insert(definition).second) return;
        for (Operation &operation : definition.getBody().front()) {
            if (auto instance = dyn_cast<ac::InstanceOp>(operation)) {
                if (auto child = dyn_cast_or_null<ac::ModuleOp>(context.analysis.resolveCallee(instance)))
                    activate(child, context.rtlPartition(instance, parent));
            } else if (auto collection = dyn_cast<ac::CollectionOp>(operation)) {
                if (auto child = dyn_cast_or_null<ac::ModuleOp>(context.analysis.resolveCallee(collection))) activate(child, nullptr);
            }
        }
    };
    for (auto system : context.package.getOps<ac::SystemOp>())
        if (auto root = dyn_cast_or_null<ac::ModuleOp>(context.analysis.lookupDefinition(
                system.getEntry().getAs<FlatSymbolRefAttr>("callee").getValue()))) activate(root, nullptr);
    auto canonical = [&](Value value) { return rtlOwnershipSource(value, &context); };
    std::function<Value(Value, const RtlOwnershipPartition *)> lift;
    lift = [&](Value value, const RtlOwnershipPartition *scope) -> Value {
        value = canonical(value);
        if (!scope) return value;
        if (auto argument = dyn_cast<BlockArgument>(value))
            if (argument.getOwner()->getParentOp() == scope->definition) {
                auto found = scope->replacedInputs.find(argument.getArgNumber());
                if (found != scope->replacedInputs.end()) return found->second;
                return lift(scope->allocation->getOperand(argument.getArgNumber()), scope->parent);
            } else if (isa<ac::ModuleOp>(argument.getOwner()->getParentOp())) return lift(value, scope->parent);
        return value;
    };
    // Lowering-created routing adapters follow the actual local storage
    // endpoint. A shared adapter stays at its least common requested scope;
    // authored nodes and protected final enables never enter this closure.
    using AdapterKey = std::pair<Operation *, const RtlOwnershipPartition *>;
    llvm::DenseMap<AdapterKey, SmallVector<RtlOwnershipPartition *>> requests;
    SmallVector<AdapterKey> requestOrder;
    llvm::DenseSet<Operation *> routedEnables(protectedEnables.begin(), protectedEnables.end());
    for (const auto &item : context.rtlPartitions) {
        if (!item->active || !item->definition->hasAttr("ac.transaction_wiring")) continue;
        auto wiring = item->definition->getAttrOfType<DictionaryAttr>("ac.transaction_wiring");
        for (auto raw : wiring.getAs<ArrayAttr>("incoming")) {
            auto index = cast<DictionaryAttr>(raw).getAs<IntegerAttr>("enable").getInt();
            Value source = lift(item->allocation->getOperand(index), item->parent);
            if (auto *producer = source.getDefiningOp()) routedEnables.insert(producer);
        }
    }
    for (auto &item : context.rtlPartitions) {
        auto &part = *item;
        if (!part.active) continue;
        SmallVector<Value> pending;
        for (auto *operation : part.operations) llvm::append_range(pending, operation->getOperands());
        if (part.definition->hasAttr("ac.transaction_wiring")) {
            ac::detail::SourceCheckBudget budget({});
            ac::HardwareBindings bindings;
            bindings.owner = part.definition;
            auto wiring = ac::detail::parseTransactionWiring(part.definition, context.analysis, bindings, budget);
            if (failed(wiring)) return failure();
            for (const auto &incoming : wiring->incoming) {
                auto owner = incoming.stateID.getAs<DictionaryAttr>("owner");
                auto path = owner ? owner.getAs<ArrayAttr>("instance_path") : ArrayAttr();
                if (path && path.empty()) {
                    pending.push_back(part.allocation.getOperand(incoming.dataInput));
                    pending.push_back(part.allocation.getOperand(incoming.enableInput));
                }
            }
        }
        llvm::DenseSet<Value> seen;
        while (!pending.empty()) {
            Value source = lift(pending.pop_back_val(), part.parent);
            if (!seen.insert(source).second) continue;
            auto *operation = source.getDefiningOp();
            if (!operation || routedEnables.contains(operation) || !ac::sourceRtlOwners(operation->getLoc()).empty() ||
                !ac::sourceValueNames(source).empty() || operation->getNumRegions() ||
                !isa<ac::BitsBinaryOp, ac::BitsUnaryOp, ac::BitsCompareOp, ac::BitsSelectOp,
                     ac::BitsResizeOp, ac::BitsExtractOp, ac::ValueRequireOp, ac::ValueMergeOp>(operation)) continue;
            auto origin = operation->getParentOfType<ac::ModuleOp>();
            const RtlOwnershipPartition *originScope = nullptr;
            bool found = false;
            for (auto *scope = &part; scope; scope = scope->parent)
                if (scope->caller == origin) { originScope = scope->parent; found = true; break; }
            if (!found) continue;
            AdapterKey key{operation, originScope};
            auto &destinations = requests[key];
            if (destinations.empty()) requestOrder.push_back(key);
            if (!llvm::is_contained(destinations, &part)) destinations.push_back(&part);
            llvm::append_range(pending, operation->getOperands());
        }
    }
    for (const auto &key : requestOrder) {
        const auto &destinations = requests.find(key)->second;
        auto *destination = destinations.front();
        for (auto *other : destinations) {
            llvm::DenseSet<const RtlOwnershipPartition *> ancestors;
            for (auto *scope = other; scope; scope = scope->parent) ancestors.insert(scope);
            while (destination && !ancestors.contains(destination)) destination = destination->parent;
        }
        if (!destination || destination == key.second) continue;
        if (destination->moved.insert(key.first).second) destination->operations.push_back(key.first);
    }
    for (auto &item : llvm::reverse(context.rtlPartitions)) {
        item->subtree.insert(item->moved.begin(), item->moved.end());
        if (item->parent) item->parent->subtree.insert(item->subtree.begin(), item->subtree.end());
    }
    // Original D/E pins are removed only if that exact producer is now in
    // this occurrence's subtree. Global final enables remain at the ancestor.
    for (auto &item : context.rtlPartitions) {
        auto &part = *item;
        if (!part.active || !part.definition->hasAttr("ac.transaction_wiring")) continue;
        ac::detail::SourceCheckBudget budget({});
        ac::HardwareBindings bindings;
        bindings.owner = part.definition;
        auto wiring = ac::detail::parseTransactionWiring(part.definition, context.analysis, bindings, budget);
        if (failed(wiring)) return failure();
        for (const auto &incoming : wiring->incoming)
            for (unsigned index : {incoming.dataInput, incoming.enableInput}) {
                Value source = lift(part.allocation.getOperand(index), part.parent);
                if (part.subtree.contains(source.getDefiningOp())) part.replacedInputs[index] = source;
            }
    }
    auto moduleOf = [&](Value value) -> ac::ModuleOp {
        auto *owner = value.getParentRegion()->getParentOp();
        if (auto module = dyn_cast<ac::ModuleOp>(owner)) return module;
        return owner->getParentOfType<ac::ModuleOp>();
    };
    std::function<Value(Value, const RtlOwnershipPartition *)> localValue;
    localValue = [&](Value value, const RtlOwnershipPartition *scope) -> Value {
        value = canonical(value);
        if (!scope) return value;
        if (moduleOf(value) == scope->definition) return value;
        Value parentValue = localValue(value, scope->parent);
        if (auto result = dyn_cast_or_null<OpResult>(parentValue))
            if (result.getOwner() == scope->allocation)
                return canonical(cast<ac::YieldOp>(scope->definition->getRegion(0).front().back()).getValues()[result.getResultNumber()]);
        for (auto [index, operand] : llvm::enumerate(scope->allocation->getOperands())) {
            if (scope->replacedInputs.count(index) || context.rtlOmittedInput(scope->definition, index)) continue;
            if (lift(operand, scope->parent) == lift(value, scope->parent))
                return scope->definition->getRegion(0).front().getArgument(index);
        }
        if (context.rtlRootConstants.count(value) ||
            isa_and_nonnull<ac::BitsConstantOp, ac::BitsConstant4Op, ac::EnumCreateOp>(value.getDefiningOp())) return value;
        return {};
    };
    auto externalUse = [&](Value start, const RtlOwnershipPartition &part) {
        llvm::DenseSet<Value> visited;
        SmallVector<Value> pending{start};
        while (!pending.empty()) {
            Value value = pending.pop_back_val();
            if (!visited.insert(value).second) continue;
            for (OpOperand &use : value.getUses()) {
                auto *user = use.getOwner();
                if (auto rule = dyn_cast<ac::RuleOp>(user)) {
                    pending.push_back(rule.getBody().front().getArgument(use.getOperandNumber()));
                    continue;
                }
                if (isa<ac::YieldOp>(user) && isa<ac::RuleOp>(user->getParentOp())) {
                    pending.push_back(cast<ac::RuleOp>(user->getParentOp()).getResult(use.getOperandNumber()));
                    continue;
                }
                if (auto extract = dyn_cast<ac::BitsExtractOp>(user); extract && canonical(extract.getResult()) != extract.getResult()) {
                    pending.push_back(extract.getResult());
                    continue;
                }
                if (context.isSynthesis() && (isa<ac::SourceExpectOp>(user) || !business.contains(user))) continue;
                if (auto instance = dyn_cast<ac::InstanceOp>(user)) {
                    if (context.rtlOmittedInput(context.analysis.resolveCallee(instance), use.getOperandNumber())) continue;
                    bool replaced = false;
                    for (const auto &route : context.rtlPartitions)
                        if (route->active && route->allocation == instance && route->subtree.contains(start.getDefiningOp())) {
                            auto found = route->replacedInputs.find(use.getOperandNumber());
                            if (found != route->replacedInputs.end() && found->second == start) replaced = true;
                        }
                    if (replaced) {
                        auto callee = context.analysis.resolveCallee(instance);
                        for (auto [index, result] : llvm::enumerate(instance.getResults()))
                            if (context.rtlForwardedInput(callee, index) == use.getOperandNumber()) pending.push_back(result);
                        continue;
                    }
                }
                if (!part.subtree.contains(user)) return true;
            }
        }
        return false;
    };
    llvm::StringSet<> moduleNames;
    for (auto definition : context.package.getOps<ac::ModuleOp>())
        if (context.rtlBaseNeeded(definition)) moduleNames.insert(rtlIdentifierStem(context.names(definition).rtl));
    for (auto &item : context.rtlPartitions) {
        auto &part = *item;
        if (!part.active) continue;
        auto base = rtlIdentifierStem(context.names(part.definition).rtl), chosen = base;
        unsigned ordinal = 0;
        while (!moduleNames.insert(chosen).second) chosen = base + "_" + std::to_string(++ordinal);
        auto spelling = rtlIdentifier(chosen, [&] { return part.definition.emitOpError(); });
        if (failed(spelling)) return failure();
        part.moduleName = *spelling;
        llvm::StringSet<> names;
        for (auto ports : {part.definition.getInputNames(), part.definition.getOutputNames()})
            for (auto raw : ports) {
                auto name = context.rtlPortName(part.definition, cast<StringAttr>(raw).getValue());
                if (failed(name)) return failure();
                names.insert(rtlIdentifierStem(*name));
            }
        for (auto raw : part.definition.getParameters())
            names.insert(cast<DictionaryAttr>(raw).getAs<StringAttr>("name").getValue());
        for (auto raw : part.definition.getTypeParameters()) names.insert(cast<StringAttr>(raw).getValue());
        auto newName = [&](StringRef role) {
            auto name = role.str();
            unsigned suffix = 0;
            while (!names.insert(name).second) name = role.str() + "_" + std::to_string(++suffix);
            auto identifier = rtlIdentifier(name, [&] { return part.definition.emitOpError(); });
            return succeeded(identifier) ? *identifier : std::string();
        };
        // Carry static namespaces too. Symbolic widths/types retain their
        // actual owner and binding, even when caller and callee reuse a name.
        SmallVector<ac::ModuleOp> ancestors;
        for (auto *scope = &part; scope; scope = scope->parent) ancestors.push_back(scope->caller);
        for (auto owner : ancestors) {
            auto prefix = "from_" + rtlIdentifierStem(context.names(owner).rtl) + "_";
            for (auto raw : owner.getParameters()) {
                auto name = cast<DictionaryAttr>(raw).getAs<StringAttr>("name");
                part.parameters.push_back({owner, name, newName(prefix + name.getValue().str()), false});
            }
            for (auto raw : owner.getTypeParameters()) {
                auto name = cast<StringAttr>(raw);
                part.parameters.push_back({owner, name, newName(prefix + name.getValue().str()), true});
            }
        }
        // Allocate ports after the complete tree exists. Bodies below are
        // processed bottom-up so a parent can relay a child's exact cut.
    }
    for (auto &item : llvm::reverse(context.rtlPartitions)) {
        auto &part = *item;
        if (!part.active) continue;
        llvm::StringSet<> names;
        for (auto ports : {part.definition.getInputNames(), part.definition.getOutputNames()})
            for (auto raw : ports) {
                auto name = context.rtlPortName(part.definition, cast<StringAttr>(raw).getValue());
                if (failed(name)) return failure();
                names.insert(rtlIdentifierStem(*name));
            }
        for (const auto &parameter : part.parameters) names.insert(rtlIdentifierStem(parameter.alias));
        for (auto raw : part.definition.getParameters())
            names.insert(cast<DictionaryAttr>(raw).getAs<StringAttr>("name").getValue());
        for (auto raw : part.definition.getTypeParameters()) names.insert(cast<StringAttr>(raw).getValue());
        auto newName = [&](Value value, StringRef fallback) {
            std::string role = fallback.str();
            auto authored = ac::sourceValueNames(value);
            if (!authored.empty()) role = authored.front().name.getValue().str();
            else if (auto argument = dyn_cast<BlockArgument>(value)) {
                auto owner = dyn_cast<ac::ModuleOp>(argument.getOwner()->getParentOp());
                if (owner) {
                    auto port = context.rtlPortName(owner, cast<StringAttr>(owner.getInputNames()[argument.getArgNumber()]).getValue());
                    if (succeeded(port)) role = rtlIdentifierStem(*port);
                }
            } else {
                llvm::StringSet<> choices;
                for (auto origin : ac::sourceRtlRoles(value)) {
                    auto kind = origin.getAs<StringAttr>("role"), scope = origin.getAs<StringAttr>("scope");
                    auto state = origin.getAs<StringAttr>("state");
                    if (kind && scope && state && kind.getValue() == "after" && !state.getValue().empty())
                        choices.insert(state.getValue().str() + "_after_" + scope.getValue().str());
                }
                if (choices.size() == 1) role = choices.begin()->getKey().str();
            }
            auto stem = rtlIdentifierStem(role);
            role.clear();
            for (char byte : stem)
                if (llvm::isAlpha(byte) || llvm::isDigit(byte) || byte == '_') role += byte;
                else role += '_';
            if (role.empty() || llvm::isDigit(role.front()) || StringRef(role).starts_with("__")) role = "transport_" + role;
            auto token = rtlIdentifier(role, [&] { return part.definition.emitOpError(); });
            if (succeeded(token) && StringRef(*token).starts_with("\\")) role += "_signal";
            std::string name = role;
            unsigned suffix = 0;
            while (!names.insert(name).second) name = role + "_" + std::to_string(++suffix);
            auto result = rtlIdentifier(name, [&] { return part.definition.emitOpError(); });
            return succeeded(result) ? *result : std::string();
        };
        SmallVector<Value> inputs, outputs;
        for (auto *operation : part.operations) {
            for (Value input : operation->getOperands()) {
                Value source = canonical(input), lifted = lift(source, part.parent);
                if (source != lifted) part.aliases[source] = lifted;
                inputs.push_back(lifted);
            }
            llvm::append_range(outputs, operation->getResults());
        }
        for (const auto &child : context.rtlPartitions)
            if (child->active && context.rtlChildPartition(child.get(), part.definition, &part)) {
                for (const auto &port : child->captures) if (!port.local) inputs.push_back(port.value);
                for (const auto &port : child->exports) outputs.push_back(port.value);
            }
        llvm::DenseSet<Value> captured, exported;
        for (Value source : inputs) {
            if (part.subtree.contains(source.getDefiningOp()) || !captured.insert(source).second) continue;
            Value local = localValue(source, &part);
            part.captures.push_back({source, local, local ? "" : newName(source, "operand")});
        }
        llvm::DenseSet<Value> required;
        if (!context.isSynthesis()) for (const auto &check : context.sourceChecks().bindings) {
            required.insert(canonical(check.condition));
            required.insert(canonical(check.path));
        }
        if (context.isPhysical() && !context.isSynthesis())
            for (const auto &control : context.physicalProjection().controls) {
                required.insert(canonical(control.raw));
                required.insert(canonical(control.reached));
            }
        for (Value value : outputs)
            if (exported.insert(value).second && (externalUse(value, part) || required.contains(value)))
                part.exports.push_back({value, {}, newName(value, "value_result")});
    }
    // Recheck the cut from original SSA and exact hierarchy aliases. Relay
    // scopes own no new operations, and each scope has one placement per node.
    llvm::DenseMap<AdapterKey, const RtlOwnershipPartition *> placedByOccurrence;
    for (const auto &item : context.rtlPartitions) {
        const auto &part = *item;
        if (!part.active) continue;
        llvm::DenseSet<Operation *> placed;
        for (auto *operation : part.operations) {
            if (!placed.insert(operation).second) return operation->emitOpError() << "RTL scope duplicates an optimized operation";
            auto origin = operation->getParentOfType<ac::ModuleOp>();
            const RtlOwnershipPartition *originalScope = nullptr;
            for (auto *scope = &part; scope; scope = scope->parent)
                if (scope->caller == origin) { originalScope = scope->parent; break; }
            if (!placedByOccurrence.try_emplace(AdapterKey{operation, originalScope}, &part).second)
                return operation->emitOpError() << "RTL scopes duplicate an original occurrence operator";
            for (Value input : operation->getOperands()) {
                Value source = lift(canonical(input), part.parent);
                if (!part.subtree.contains(source.getDefiningOp()) &&
                    !llvm::any_of(part.captures, [&](const auto &port) { return port.value == source; }))
                    return operation->emitOpError() << "RTL scope loses an original operand";
            }
        }
        for (const auto &[index, source] : part.replacedInputs)
            if (lift(part.allocation->getOperand(index), part.parent) != source ||
                !part.subtree.contains(source.getDefiningOp()))
                return part.allocation->emitOpError() << "RTL scope changes an original D/E candidate";
        for (const auto &port : part.captures)
            if ((port.local && localValue(port.value, &part) != port.local) || (!port.local && port.name.empty()))
                return part.allocation->emitOpError() << "RTL scope changes an original boundary alias";
        // Independently walk the original consumers instead of trusting the
        // port collector. Rule forwarding is canonical identity; no live cut
        // edge can disappear behind an omitted original D/E connection.
        auto checked = context.package.walk([&](Operation *consumer) {
            if (part.subtree.contains(consumer) || isa<ac::RuleOp>(consumer) ||
                (isa<ac::YieldOp>(consumer) && isa<ac::RuleOp>(consumer->getParentOp()))) return WalkResult::advance();
            if (context.isSynthesis() && (isa<ac::SourceExpectOp>(consumer) || !business.contains(consumer)))
                return WalkResult::advance();
            if (consumer->getNumResults() == 1 && canonical(consumer->getResult(0)) != consumer->getResult(0)) return WalkResult::advance();
            for (auto [index, input] : llvm::enumerate(consumer->getOperands())) {
                Value value = canonical(input);
                if (!part.subtree.contains(value.getDefiningOp())) continue;
                if (auto instance = dyn_cast<ac::InstanceOp>(consumer)) {
                    if (context.rtlOmittedInput(context.analysis.resolveCallee(instance), index)) continue;
                    bool replaced = false;
                    for (const auto &route : context.rtlPartitions)
                        if (route->active && route->allocation == instance && route->subtree.contains(value.getDefiningOp())) {
                            auto found = route->replacedInputs.find(index);
                            if (found != route->replacedInputs.end() && found->second == value) replaced = true;
                        }
                    if (replaced) continue;
                }
                if (!llvm::any_of(part.exports, [&](const auto &port) { return port.value == value; })) {
                    consumer->emitOpError() << "RTL scope loses an original external consumer";
                    return WalkResult::interrupt();
                }
            }
            return WalkResult::advance();
        });
        if (checked.wasInterrupted()) return failure();
        unsigned depth = 0;
        for (auto *scope = &part; scope; scope = scope->parent) ++depth;
        context.rtlOwnershipNotes.emplace_back(llvm::json::Object{
            {"status", "partitioned"}, {"source", SymbolTable::getSymbolName(part.caller).getValue().str()},
            {"owner", SymbolTable::getSymbolName(part.definition).getValue().str()}, {"rtl_module", part.moduleName},
            {"receiver_depth", depth}, {"optimized_operations", part.operations.size()},
            {"captures", part.captures.size()}, {"exports", part.exports.size()},
            {"static_parameters", part.parameters.size()},
            {"validation", "original SSA, occurrence-relative aliases, exact D/E, one placement per scope"}});
    }
    for (const auto &entry : context.rtlRootConstants)
        context.rtlOwnershipNotes.emplace_back(llvm::json::Object{
            {"status", "root_default_bound"}, {"input", cast<BlockArgument>(entry.first).getArgNumber()},
            {"literal", entry.second}, {"source", "authenticated rootInputDefaults; original wrapper connection"}});
    return success();
}
