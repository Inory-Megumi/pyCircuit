// Typed row projection over the original verified graph. Shared computation
// remains a vector boundary; broadcasts are representation aliases only.
struct ReadableTableLanes {
    SmallVector<Value> roots, tables, scalars;
    llvm::DenseSet<Value> seen, materializedRoots;
    llvm::DenseSet<Value> mapArguments;
    llvm::DenseSet<Operation *> maps, blocked;
    llvm::DenseMap<Operation *, Operation *> owners;
    llvm::DenseMap<Value, ReadableAggregateChoice> choices;
    Operation *storage = nullptr;
    unsigned dataPin = 0;
    uint64_t count = 0;
    SmallVector<uint64_t> shape;
    unsigned remaining = 256;
};

std::optional<SmallVector<uint64_t>> readableTableShape(Type type, Operation *site) {
    auto table = dyn_cast<ac::TableType>(type);
    if (!table) return std::nullopt;
    SmallVector<uint64_t> result;
    for (auto raw : table.getShape()) {
        auto dim = cast<ac::StaticExprAttr>(raw);
        if (!context.isClosedStatic(dim)) return std::nullopt;
        auto text = context.staticRtlValue(dim, site);
        auto size = succeeded(text) ? readableUnsigned(*text) : std::nullopt;
        if (!size || !*size) return std::nullopt;
        result.push_back(*size);
    }
    return result;
}

Value readableBroadcast(Value value) {
    value = readableSource(value);
    if (ownershipOpaque.contains(value) || !ac::sourceValueNames(value).empty()) return {};
    if (auto splat = value.getDefiningOp<ac::TableSplatOp>()) return splat.getInput();
    if (auto create = value.getDefiningOp<ac::TableCreateOp>(); create && create->getNumOperands()) {
        Value first = readableSource(create->getOperand(0));
        if (llvm::all_of(create->getOperands(), [&](Value input) { return readableSource(input) == first; }))
            return first;
    }
    return {};
}

bool collectReadableTableChoice(Value value, const ReadableAggregateChoice &choice,
                               llvm::DenseSet<Operation *> &operations, unsigned &remaining) {
    SmallVector<Value> pending{value};
    llvm::DenseSet<Value> seen;
    while (!pending.empty()) {
        Value current = readableSource(pending.pop_back_val());
        if (current == choice.condition || current == choice.onTrue || current == choice.onFalse ||
            !seen.insert(current).second) continue;
        if (!remaining) return false;
        --remaining;
        auto *op = current.getDefiningOp();
        // Literal ordinals are already checked by aggregate-choice recovery;
        // they may also serve unrelated nodes and are not owned by this cut.
        if (isa_and_nonnull<ac::BitsConstantOp, ac::BitsConstant4Op, ac::EnumCreateOp>(op)) continue;
        if (!op || !isa<ac::TableCreateOp, ac::TableReadOp, ac::TableGetOp, ac::ValueMergeOp, ac::StructCreateOp,
                        ac::StructGetOp, ac::BitsSelectOp, ac::EnumToBitsOp,
                        ac::EnumFromBitsOp>(op)) return false;
        operations.insert(op);
        llvm::append_range(pending, op->getOperands());
    }
    return true;
}

std::optional<llvm::DenseSet<Value>> readableMapArguments(ac::TableMapOp map, unsigned result,
                                                        unsigned &remaining) {
    llvm::DenseSet<Value> arguments, visited;
    auto &body = map.getBody().front();
    SmallVector<Value> pending{cast<ac::YieldOp>(body.back()).getValues()[result]};
    while (!pending.empty()) {
        Value value = pending.pop_back_val();
        if (!visited.insert(value).second) continue;
        if (!remaining) return std::nullopt;
        --remaining;
        if (auto argument = dyn_cast<BlockArgument>(value)) {
            if (argument.getOwner() != &body) return std::nullopt;
            arguments.insert(value);
        } else {
            auto *producer = value.getDefiningOp();
            if (!producer || producer->getBlock() != &body || producer->getNumRegions()) return std::nullopt;
            llvm::append_range(pending, producer->getOperands());
        }
    }
    return arguments;
}

void planReadableTableValue(Value value, ReadableTableLanes &plan) {
    value = readableSource(value);
    if (!plan.seen.insert(value).second) return;
    auto shape = readableTableShape(value.getType(), definition);
    bool root = plan.materializedRoots.contains(value);
    if (!shape || *shape != plan.shape || ownershipOpaque.contains(value) || names.contains(value) ||
        (!root && !ac::sourceValueNames(value).empty()) || !plan.remaining) {
        plan.tables.push_back(value);
        return;
    }
    --plan.remaining;
    if (auto scalar = readableBroadcast(value)) {
        plan.scalars.push_back(scalar);
        return;
    }
    auto *op = value.getDefiningOp();
    if (op && !plan.blocked.contains(op)) {
        if (auto map = dyn_cast<ac::TableMapOp>(op)) {
            bool safe = llvm::all_of(map->getResults(), [&](Value result) {
                return !names.contains(result) && (root || ac::sourceValueNames(result).empty());
            });
            for (Operation &body : map.getBody().front())
                safe &= body.getNumRegions() == 0 && isMemoryEffectFree(&body);
            auto needed = safe ? readableMapArguments(map, cast<OpResult>(value).getResultNumber(), plan.remaining)
                               : std::nullopt;
            if (needed) {
                plan.maps.insert(op);
                plan.owners[op] = op;
                for (Value argument : *needed) plan.mapArguments.insert(argument);
                auto &body = map.getBody().front();
                unsigned index = 1;
                for (Value table : map.getTables())
                    if (plan.mapArguments.contains(body.getArgument(index++))) planReadableTableValue(table, plan);
                for (Value capture : map.getCaptures())
                    if (plan.mapArguments.contains(body.getArgument(index++))) plan.scalars.push_back(capture);
                return;
            }
        }
        if (auto choice = readableAggregateChoice(value)) {
            llvm::DenseSet<Operation *> wrappers;
            if (collectReadableTableChoice(value, *choice, wrappers, plan.remaining)) {
                plan.choices[value] = *choice;
                for (auto *wrapper : wrappers) plan.owners[wrapper] = op;
                plan.scalars.push_back(choice->condition);
                planReadableTableValue(choice->onTrue, plan);
                planReadableTableValue(choice->onFalse, plan);
                return;
            }
        }
    }
    plan.tables.push_back(value);
}

bool readableTableUsesInside(Value value, const ReadableTableLanes &plan,
                             llvm::DenseSet<Value> &seen) {
    if (!seen.insert(value).second || plan.materializedRoots.contains(readableSource(value))) return true;
    llvm::DenseSet<Value> live;
    if (!readableRtlUsed(value, live)) return true;
    for (OpOperand &use : value.getUses()) {
        auto *owner = use.getOwner();
        if (plan.owners.contains(owner)) continue;
        if (owner == plan.storage && (use.getOperandNumber() == plan.dataPin ||
                                     (plan.dataPin == 3 && use.getOperandNumber() == 2))) continue;
        if (auto rule = dyn_cast<ac::RuleOp>(owner)) {
            if (!readableTableUsesInside(rule.getBody().front().getArgument(use.getOperandNumber()), plan, seen)) return false;
        } else if (isa<ac::YieldOp>(owner) && isa<ac::RuleOp>(owner->getParentOp())) {
            auto rule = cast<ac::RuleOp>(owner->getParentOp());
            if (!readableTableUsesInside(rule.getResult(use.getOperandNumber()), plan, seen)) return false;
        } else return false;
    }
    return true;
}

std::optional<ReadableTableLanes> prepareReadableTableLanes(
        ArrayRef<Value> roots, bool materialize, ac::CollectionOp storage = {}) {
    if (roots.empty()) return std::nullopt;
    auto shape = readableTableShape(roots.front().getType(), definition);
    if (!shape) return std::nullopt;
    llvm::DenseSet<Operation *> blocked;
    for (unsigned attempt = 0; attempt != 256; ++attempt) {
        ReadableTableLanes plan;
        plan.shape = *shape;
        plan.count = 1;
        for (auto size : *shape) {
            if (size > std::numeric_limits<uint64_t>::max() / plan.count) return std::nullopt;
            plan.count *= size;
        }
        plan.blocked = blocked;
        plan.roots.assign(roots.begin(), roots.end());
        plan.storage = storage ? storage.getOperation() : nullptr;
        if (storage) plan.dataPin = storage->getNumOperands() == 5 ? 3 : 2;
        if (materialize)
            for (Value root : roots) plan.materializedRoots.insert(readableSource(root));
        for (Value root : roots) planReadableTableValue(root, plan);
        llvm::DenseSet<Operation *> invalid;
        for (auto [operation, group] : plan.owners) {
            for (Value result : operation->getResults()) {
                llvm::DenseSet<Value> visited;
                if (!readableTableUsesInside(result, plan, visited)) invalid.insert(group);
            }
        }
        if (invalid.empty()) return plan;
        unsigned previous = blocked.size();
        for (auto *operation : invalid) blocked.insert(operation);
        if (previous == blocked.size()) return std::nullopt;
    }
    return std::nullopt;
}

LogicalResult preloadReadableTableLanes(const ReadableTableLanes &plan) {
    for (Value table : plan.tables)
        if (failed(net(table))) return failure();
    for (Value scalar : plan.scalars)
        if (failed(net(scalar))) return failure();
    return success();
}

FailureOr<std::string> projectReadableTableLane(
        Value value, StringRef ordinal, StringRef stem, const ReadableTableLanes &plan,
        llvm::DenseMap<Value, std::string> &rows, llvm::DenseSet<Operation *> &boundMaps) {
    value = readableSource(value);
    if (auto found = rows.find(value); found != rows.end()) return found->second;
    auto section = readableSection(value);
    auto type = cast<ac::TableType>(value.getType());
    if (auto scalar = readableBroadcast(value);
        scalar && llvm::is_contained(plan.scalars, scalar)) {
        auto rendered = net(scalar);
        if (succeeded(rendered)) rows[value] = *rendered;
        return rendered;
    }
    if (auto choice = plan.choices.find(value); choice != plan.choices.end()) {
        auto condition = net(choice->second.condition);
        auto yes = projectReadableTableLane(choice->second.onTrue, ordinal, stem, plan, rows, boundMaps);
        auto no = projectReadableTableLane(choice->second.onFalse, ordinal, stem, plan, rows, boundMaps);
        auto itemType = context.rtlType(type.getElementType(), definition);
        if (failed(condition) || failed(yes) || failed(no) || failed(itemType)) return failure();
        auto preferred = readableRoleStem(value);
        auto id = rtlIdentifier(preferred ? *preferred : stem.str() + "_candidate", [&] { return definition.emitOpError(); });
        if (failed(id)) return failure();
        auto name = readableName(*id);
        readableDeclaration("wire", *itemType, name);
        readableAssignment(name, *condition + " ? " + *yes + " : " + *no);
        rows[value] = name;
        return name;
    }
    if (auto map = value.getDefiningOp<ac::TableMapOp>(); map && plan.maps.contains(map)) {
        if (boundMaps.insert(map).second) {
            auto &body = map.getBody().front();
            auto width = context.payloadWidth(body.getArgument(0).getType(), map, true);
            if (failed(width)) return failure();
            names[body.getArgument(0)] = "(" + *width + ")'(" + ordinal.str() + ")";
            unsigned index = 1;
            for (Value input : map.getTables()) {
                auto argument = body.getArgument(index++);
                if (!plan.mapArguments.contains(argument)) continue;
                auto row = projectReadableTableLane(input, ordinal, stem, plan, rows, boundMaps);
                if (failed(row)) return failure();
                names[argument] = *row;
            }
            for (Value capture : map.getCaptures()) {
                auto argument = body.getArgument(index++);
                if (!plan.mapArguments.contains(argument)) continue;
                auto rendered = net(capture);
                if (failed(rendered)) return failure();
                names[argument] = *rendered;
            }
        }
        auto yielded = cast<ac::YieldOp>(map.getBody().front().back()).getValues();
        auto number = cast<OpResult>(value).getResultNumber();
        auto row = net(yielded[number]);
        if (succeeded(row)) rows[value] = *row;
        return row;
    }
    auto rendered = net(value);
    if (failed(rendered)) return failure();
    auto row = readablePackedElement(*rendered, ordinal, type, definition);
    if (succeeded(row)) rows[value] = *row;
    return row;
}

void inheritReadableLaneEnvironment(NetEmitter &local) {
    local.names = names;
    local.ownershipAliases = ownershipAliases;
    local.ownershipOpaque = ownershipOpaque;
    local.readableNames = readableNames;
    local.readableRetained = readableRetained;
    local.readableInlineExpressions = readableInlineExpressions;
    local.readableInlineCosts = readableInlineCosts;
    local.readableControlViews = readableControlViews;
    local.readableControlUses = readableControlUses;
    local.readableEndpointValues = readableEndpointValues;
    local.readableRoleHints = readableRoleHints;
    local.readableAmbiguousBindings = readableAmbiguousBindings;
    local.readableAuthoredNames = readableAuthoredNames;
    local.readablePurposes = readablePurposes;
    local.readableValueOrdinals = readableValueOrdinals;
    local.readableSections.inherit(readableSections);
    local.next = next;
}

void collectReadableLaneEnvironment(NetEmitter &local, StringRef scope) {
    llvm::append_range(readableFactProofs, local.readableFactProofs);
    for (auto [value, view] : local.readableControlViews) readableControlViews.try_emplace(value, view);
    for (auto [value, expression] : local.names)
        if (!names.contains(value)) {
            names[value] = expression;
            readableLaneScopes[value] = scope.str();
        }
    readableNames = std::move(local.readableNames);
    next = local.next;
}

void readableLaneBody(StringRef body) {
    SmallVector<StringRef> lines;
    body.split(lines, '\n');
    for (auto line : lines)
        if (!line.empty()) out << "  " << line << "\n";
}

FailureOr<std::string> readableTableLaneNet(Value value, bool &accepted) {
    auto *operation = value.getDefiningOp();
    if (!isa<ac::TableMapOp, ac::TableCreateOp>(operation)) return failure();
    SmallVector<Value> roots;
    if (isa<ac::TableMapOp>(operation)) {
        for (Value result : operation->getResults()) {
            llvm::DenseSet<Value> seen;
            if (result == value || readableRtlUsed(result, seen)) roots.push_back(result);
        }
    } else roots.push_back(value);
    auto plan = prepareReadableTableLanes(roots, true);
    if (!plan || plan->maps.empty() || !plan->owners.contains(operation)) return failure();
    accepted = true;
    SmallVector<std::string> outputs;
    for (Value root : roots) {
        auto type = context.rtlType(root.getType(), operation);
        if (failed(type)) return failure();
        auto name = sourceNetName(root);
        readableDeclaration("wire", *type, name);
        names[root] = name;
        outputs.push_back(name);
    }
    if (failed(preloadReadableTableLanes(*plan))) return failure();
    auto stem = rtlIdentifierStem(outputs.front());
    auto ordinal = readableName(stem + "_lane");
    auto block = readableName(stem + "_rows");
    std::string text;
    llvm::raw_string_ostream buffer(text);
    NetEmitter local(context, definition, buffer, ownership);
    inheritReadableLaneEnvironment(local);
    llvm::DenseMap<Value, std::string> rows;
    llvm::DenseSet<Operation *> boundMaps;
    for (auto [index, root] : llvm::enumerate(roots)) {
        auto row = local.projectReadableTableLane(root, ordinal, stem, *plan, rows, boundMaps);
        if (failed(row)) return failure();
        auto target = readablePackedElement(outputs[index], ordinal, cast<ac::TableType>(root.getType()), operation);
        if (failed(target)) return failure();
        auto section = local.readableSection(root);
        local.out << "  assign " << *target << " = " << *row << ";\n";
    }
    collectReadableLaneEnvironment(local, block);
    local.finishReadableLayout();
    out << "  for (genvar " << ordinal << " = 0; " << ordinal << " < " << plan->count
        << "; ++" << ordinal << ") begin : " << block << "\n";
    readableLaneBody(text);
    out << "  end\n";
    return names.lookup(value);
}

FailureOr<std::string> readableCollectionPin(Value value, StringRef ordinal) {
    if (auto scalar = readableBroadcast(value)) return net(scalar);
    auto text = net(value);
    if (failed(text)) return failure();
    return readablePackedElement(*text, ordinal, cast<ac::TableType>(value.getType()), definition);
}

LogicalResult emitReadableCollectionLanes(ac::CollectionOp collection, const ReadableTableLanes &plan) {
    bool enabled = plan.dataPin == 3;
    auto q = net(collection.getResult(0));
    if (failed(q)) return failure();
    auto stem = rtlIdentifierStem(*q);
    auto ordinal = readableName(stem + "_lane");
    auto block = readableName(stem + "_update");
    auto clock = readableCollectionPin(collection.getOperand(0), ordinal);
    auto reset = readableCollectionPin(collection.getOperand(1), ordinal);
    Value initialValue = collection.getOperand(enabled ? 4 : 3);
    auto initialScalar = readableBroadcast(initialValue);
    auto initial = physicalInitializer(initialScalar ? initialScalar : initialValue);
    if (failed(clock) || failed(reset) || failed(initial) || failed(preloadReadableTableLanes(plan)))
        return failure();
    auto table = cast<ac::TableType>(collection.getResult(0).getType());
    auto old = readablePackedElement(*q, ordinal, table, collection);
    auto resetValue = initialScalar ? initial : readablePackedElement(*initial, ordinal, table, collection);
    if (failed(old) || failed(resetValue)) return failure();
    std::string text;
    llvm::raw_string_ostream buffer(text);
    NetEmitter local(context, definition, buffer, ownership);
    inheritReadableLaneEnvironment(local);
    llvm::DenseMap<Value, std::string> rows;
    llvm::DenseSet<Operation *> boundMaps;
    auto data = local.projectReadableTableLane(collection.getOperand(plan.dataPin), ordinal, stem, plan, rows, boundMaps);
    auto enable = enabled ? local.projectReadableTableLane(collection.getOperand(2), ordinal, stem, plan, rows, boundMaps)
                          : FailureOr<std::string>(std::string("1'b1"));
    if (failed(data) || failed(enable)) return failure();
    auto section = local.readableSections.select("commit", "Register update", 3000);
    local.out << "  always_ff @(posedge " << *clock << ") begin\n"
           << "    if (" << context.rtlReset(*reset) << ")\n"
           << "      " << *old << " <= " << *resetValue << ";\n"
           << (enabled ? "    else if (" + *enable + ")\n" : "    else\n")
           << "      " << *old << " <= " << *data << ";\n  end\n";
    collectReadableLaneEnvironment(local, block);
    local.finishReadableLayout();
    out << "  for (genvar " << ordinal << " = 0; " << ordinal << " < " << plan.count
        << "; ++" << ordinal << ") begin : " << block << "\n";
    readableLaneBody(text);
    out << "  end\n";
    return success();
}

bool readableRtlUsed(Value value, llvm::DenseSet<Value> &seen) {
    if (!seen.insert(value).second) return false;
    for (OpOperand &use : value.getUses()) {
        auto *owner = use.getOwner();
        if (auto rule = dyn_cast<ac::RuleOp>(owner)) {
            if (readableRtlUsed(rule.getBody().front().getArgument(use.getOperandNumber()), seen)) return true;
        } else if (auto map = dyn_cast<ac::TableMapOp>(owner)) {
            if (readableRtlUsed(map.getBody().front().getArgument(1 + use.getOperandNumber()), seen)) return true;
        } else if (isa<ac::YieldOp>(owner) && isa<ac::RuleOp, ac::TableMapOp>(owner->getParentOp())) {
            if (readableRtlUsed(owner->getParentOp()->getResult(use.getOperandNumber()), seen)) return true;
        } else if (!owner->getNumRegions() && owner->getNumResults() && isMemoryEffectFree(owner)) {
            for (Value result : owner->getResults())
                if (readableRtlUsed(result, seen)) return true;
        } else return true;
    }
    return false;
}

bool readableUnusedTableResult(Value value, Value requested) {
    if (!context.isPhysical() || value == requested) return false;
    auto *op = value.getDefiningOp();
    if (!isa<ac::TableMapOp>(op) &&
        !(isa<ac::ValueMergeOp>(op) && cast<OpResult>(value).getResultNumber() == 1)) return false;
    llvm::DenseSet<Value> seen;
    return !readableRtlUsed(value, seen);
}
