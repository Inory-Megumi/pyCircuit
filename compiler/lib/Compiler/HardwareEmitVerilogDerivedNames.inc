// Display-only use/slot names. These queries must never call net(), add uses,
// attach authored bindings, or participate in an inlining/materialization test.
SmallVector<Value> readableOrderedValues() {
    SmallVector<Value> ordered;
    definition.walk([&](Operation *operation) {
        for (Value result : operation->getResults()) ordered.push_back(result);
        for (Region &region : operation->getRegions())
            for (Block &block : region)
                for (BlockArgument argument : block.getArguments()) ordered.push_back(argument);
    });
    if (ownership) {
        llvm::DenseSet<Value> present(ordered.begin(), ordered.end());
        auto append = [&](Value value) { if (present.insert(value).second) ordered.push_back(value); };
        for (auto *operation : ownership->operations) {
            for (Value value : operation->getResults()) append(value);
            for (Value value : operation->getOperands()) {
                auto source = rtlOwnershipSource(value);
                append(source);
                if (auto alias = ownership->aliases.find(source); alias != ownership->aliases.end()) append(alias->second);
            }
        }
        for (const auto &port : ownership->captures) append(port.value);
        for (const auto &port : ownership->exports) append(port.value);
    }
    return ordered;
}

std::string readableScopedStem(Value value, StringRef stem) {
    if (auto scope = readableMethodScope(readableSource(value));
        scope && stem != *scope && !stem.starts_with(*scope + "_"))
        return *scope + "_" + stem.str();
    return stem.str();
}

std::optional<std::string> readablePrimitiveResultStem(Value value) {
    auto result = dyn_cast<OpResult>(value);
    if (!result || !isa<ac::InstanceOp>(result.getOwner())) return std::nullopt;
    auto instance = cast<ac::InstanceOp>(result.getOwner());
    auto *callee = context.analysis.resolveCallee(instance);
    if (!callee || isa<ac::ModuleOp>(callee) || isReadableRegister(instance)) return std::nullopt;
    auto outputs = callee->getAttrOfType<ArrayAttr>("output_names");
    if (!outputs || result.getResultNumber() >= outputs.size()) return std::nullopt;
    auto port = context.rtlPortName(callee, cast<StringAttr>(outputs[result.getResultNumber()]).getValue());
    if (failed(port)) return std::nullopt;
    return instance.getInstanceName().str() + "_" + rtlIdentifierStem(*port);
}

std::optional<uint64_t> readableSmallInteger(Value value, unsigned depth = 0) {
    value = readableSource(value);
    auto width = readableWidth(value);
    if (depth > 16 || !width || *width > 64) return std::nullopt;
    std::optional<uint64_t> number;
    auto *operation = value.getDefiningOp();
    if (auto constant = dyn_cast_or_null<ac::BitsConstantOp>(operation)) {
        if (!context.isClosedStatic(constant.getValue())) return std::nullopt;
        auto text = context.staticRtlValue(constant.getValue(), constant);
        uint64_t integer = 0;
        if (succeeded(text) && !StringRef(*text).getAsInteger(10, integer)) number = integer;
    }
    if (auto pattern = dyn_cast_or_null<ac::BitsConstant4Op>(operation)) {
        uint64_t integer = 0;
        if (!pattern.getPattern().getAsInteger(2, integer)) number = integer;
    }
    if (auto resize = dyn_cast_or_null<ac::BitsResizeOp>(operation))
        if (resize.getMode() != "sext") number = readableSmallInteger(resize.getOperand(), depth + 1);
    if (auto extract = dyn_cast_or_null<ac::BitsExtractOp>(operation)) {
        auto input = readableSmallInteger(extract.getInput(), depth + 1);
        auto low = context.staticRtlValue(extract.getLow(), extract);
        uint64_t offset = 0;
        if (input && succeeded(low) && !StringRef(*low).getAsInteger(10, offset))
            number = offset < 64 ? *input >> offset : 0;
    }
    if (number && *width < 64) *number &= (uint64_t(1) << *width) - 1;
    return number;
}

std::optional<std::string> readableComparisonStem(Value value) {
    auto compare = value.getDefiningOp<ac::BitsCompareOp>();
    if (!compare) return std::nullopt;
    auto number = readableSmallInteger(compare.getRhs());
    Value subject = compare.getLhs();
    StringRef predicate = compare.getPredicate();
    if (!number) {
        number = readableSmallInteger(compare.getLhs());
        subject = compare.getRhs();
        predicate = llvm::StringSwitch<StringRef>(predicate)
            .Case("ult", "ugt").Case("ugt", "ult").Case("ule", "uge").Case("uge", "ule")
            .Case("slt", "sgt").Case("sgt", "slt").Case("sle", "sge").Case("sge", "sle").Default(predicate);
    }
    if (!number) return std::nullopt;
    auto anchor = readableNameAnchor(subject);
    if (!anchor) return std::nullopt;
    auto comparison = llvm::StringSwitch<StringRef>(predicate)
        .Case("eq", "is").Case("ne", "is_not").Case("case_eq", "exactly")
        .Cases({"ugt", "sgt"}, "above").Cases({"ult", "slt"}, "below")
        .Cases({"uge", "sge"}, "at_least").Cases({"ule", "sle"}, "at_most").Default(predicate);
    return *anchor + "_" + comparison.str() + "_" + std::to_string(*number);
}

std::optional<std::string> readableNameAnchor(Value value, unsigned depth = 0) {
    if (depth > 16) return std::nullopt;
    auto bindings = ac::sourceValueNames(value);
    if (!bindings.empty()) return readableBindingName(value, bindings);
    Value source = readableSource(value);
    if (source != value) return readableNameAnchor(source, depth + 1);
    if (auto hint = readableRoleHints.find(value); hint != readableRoleHints.end()) return hint->second;
    if (auto role = readableRoleStem(value)) return role;
    if (auto pin = readablePrimitiveResultStem(value)) return pin;
    if (auto argument = dyn_cast<BlockArgument>(value)) {
        if (argument.getOwner()->getParentOp() == definition)
            return cast<StringAttr>(definition.getInputNames()[argument.getArgNumber()]).getValue().str();
        return std::nullopt;
    }
    auto *operation = value.getDefiningOp();
    if (auto get = dyn_cast_or_null<ac::StructGetOp>(operation)) {
        auto owner = readableNameAnchor(get.getOperand(), depth + 1);
        return owner ? *owner + "_" + get.getField().str() : readableScopedStem(value, get.getField());
    }
    if (auto match = dyn_cast_or_null<ac::TableMatchOp>(operation))
        if (auto input = readableNameAnchor(match.getInput(), depth + 1)) return *input + "_match_mask";
    if (isa_and_nonnull<ac::TableChooseOp>(operation)) return readableAuxiliaryStem(value);
    if (operation && isa<ac::InstanceOp, ac::CollectionOp>(operation))
        if (auto name = operation->getAttrOfType<StringAttr>("instance_name")) {
            if (auto instance = dyn_cast<ac::InstanceOp>(operation)) {
                auto *callee = context.analysis.resolveCallee(instance);
                unsigned slot = cast<OpResult>(value).getResultNumber();
                if (auto projection = context.rtlOutputProjection(callee, slot)) {
                    auto outputs = callee->getAttrOfType<ArrayAttr>("output_names");
                    std::string stem = name.getValue().str() + "_" + cast<StringAttr>(outputs[projection->output]).getValue().str();
                    for (const auto &field : projection->fields) stem += "_" + field;
                    return stem;
                }
                if (auto module = dyn_cast_or_null<ac::ModuleOp>(callee)) {
                    auto layout = ac::getModulePortLayout(module);
                    if (succeeded(layout) && slot >= layout->sourceOutputCount) {
                        auto port = context.rtlPortName(callee, cast<StringAttr>(module.getOutputNames()[slot]).getValue());
                        if (succeeded(port)) return name.getValue().str() + "_" + rtlIdentifierStem(*port);
                    }
                }
            }
            return name.getValue().str();
        }
    if (isa_and_nonnull<ac::BitsResizeOp, ac::EnumToBitsOp>(operation))
        return readableNameAnchor(operation->getOperand(0), depth + 1);
    return std::nullopt;
}

std::optional<std::string> readableOperationStem(Value value) {
    auto *operation = value.getDefiningOp();
    if (isa_and_nonnull<ac::StructGetOp, ac::TableMatchOp>(operation)) return readableNameAnchor(value);
    if (isa_and_nonnull<ac::TableReadOp, ac::TableGetOp>(operation)) {
        if (cast<OpResult>(value).getResultNumber() != 0) return std::nullopt;
        auto input = readableNameAnchor(operation->getOperand(0));
        return (input ? *input : readableScopedStem(value, "table")) + "_read_value";
    }
    if (auto fold = dyn_cast_or_null<ac::TableFoldOp>(operation)) {
        auto input = readableNameAnchor(fold.getInput());
        return (input ? *input : "table") + "_" + fold.getKind().str() + "_reduction";
    }
    if (isa_and_nonnull<ac::TableMapOp>(operation)) {
        // Retain the existing upstream storage information as well as the
        // downstream purpose plan. A scalar queue payload is not a table owner.
        llvm::DenseSet<Value> visited;
        llvm::StringSet<> storage;
        SmallVector<Value> pending{value};
        unsigned remaining = 256;
        while (!pending.empty()) {
            if (!remaining) return std::nullopt;
            --remaining;
            Value current = readableSource(pending.pop_back_val());
            if (!visited.insert(current).second) continue;
            auto *producer = current.getDefiningOp();
            if (!producer) continue;
            if (isa<ac::InstanceOp, ac::CollectionOp>(producer)) {
                if (isa<ac::TableType>(current.getType()))
                    if (auto name = producer->getAttrOfType<StringAttr>("instance_name")) storage.insert(name.getValue());
                continue;
            }
            for (Value input : producer->getOperands())
                if (isa<ac::TableType, ac::StructType>(input.getType())) pending.push_back(input);
        }
        if (storage.size() == 1)
            return storage.begin()->getKey().str() + "_mapped_" + std::to_string(readableValueOrdinals.lookup(value));
    }
    return std::nullopt;
}

// Result-slot contracts, not the spelling of a producing operation. In
// particular TableGet.in_range is a predicate, not the fetched payload.
std::optional<std::string> readableAuxiliaryStem(Value value) {
    auto result = dyn_cast<OpResult>(value);
    if (!result) return std::nullopt;
    auto *operation = result.getOwner();
    unsigned slot = result.getResultNumber();
    if (auto get = dyn_cast<ac::TableGetOp>(operation); get && slot == 1) {
        auto index = readableNameAnchor(get.getIndex());
        auto payload = readableNameAnchor(get.getValue());
        auto base = index ? *index : payload ? *payload + "_index" : readableScopedStem(value, "read_index");
        return base + "_in_range";
    }
    if (auto decode = dyn_cast<ac::EnumFromBitsOp>(operation); decode && slot == 1) {
        auto input = readableNameAnchor(decode.getInput());
        return (input ? *input : readableScopedStem(value, "enum_input")) + "_is_member";
    }
    if (auto choose = dyn_cast<ac::TableChooseOp>(operation)) {
        auto mask = readableNameAnchor(choose.getMask());
        auto count = static_cast<unsigned>(choose.getCount());
        auto base = (mask ? *mask : readableScopedStem(value, "selection")) + "_choice_";
        return base + std::to_string(slot % count) + (slot < count ? "_index" : "_valid");
    }
    if (auto merge = dyn_cast<ac::ValueMergeOp>(operation); merge && slot == 1) {
        auto base = readableNameAnchor(merge.getNext());
        return (base ? *base : readableScopedStem(value, "update")) + "_has_write";
    }
    return std::nullopt;
}

std::string readableValuePart(StringRef base, StringRef part) {
    if (base.ends_with("_value")) return base.drop_back(6).str() + part.str() + "_value";
    return base.str() + part.str();
}

// Follow only typed construction/forwarding edges toward a real consumer.
// Ambiguity, unrelated uses, cycles or the display-walk bound fall back to a
// nominal type name. There is no first-consumer/first-method ownership guess.
std::optional<std::string> readableConstructionUse(Value value, unsigned &budget, unsigned depth = 0) {
    if (depth > 16 || !budget) return std::nullopt;
    --budget;
    llvm::StringSet<> choices;
    bool incomplete = false;
    for (OpOperand &use : value.getUses()) {
        if (!budget) return std::nullopt;
        --budget;
        auto *owner = use.getOwner();
        unsigned ordinal = use.getOperandNumber();
        Value consumer;
        std::string part;
        if (auto yield = dyn_cast<ac::YieldOp>(owner)) {
            auto *parent = yield->getParentOp();
            if (parent == definition) {
                choices.insert(cast<StringAttr>(definition.getOutputNames()[ordinal]).getValue().str() + "_value");
                continue;
            }
            if (isa<ac::RuleOp, ac::TableMapOp>(parent) && ordinal < parent->getNumResults()) {
                consumer = parent->getResult(ordinal);
                if (isa<ac::TableMapOp>(parent)) part = "_element";
            }
        } else if (auto splat = dyn_cast<ac::TableSplatOp>(owner)) {
            consumer = splat.getResult(); part = "_element";
        } else if (auto create = dyn_cast<ac::TableCreateOp>(owner)) {
            consumer = create.getResult(); part = "_element_" + std::to_string(ordinal);
        } else if (auto create = dyn_cast<ac::StructCreateOp>(owner)) {
            auto type = cast<ac::StructType>(create.getResult().getType());
            auto declaration = context.analysis.lookupStruct(type);
            if (declaration && ordinal < declaration.getFields().size()) {
                auto field = cast<DictionaryAttr>(declaration.getFields()[ordinal]).getAs<StringAttr>("name");
                consumer = create.getResult(); part = "_" + field.getValue().str();
            }
        } else if (isa<ac::InstanceOp, ac::CollectionOp>(owner)) {
            auto *callee = isa<ac::InstanceOp>(owner)
                ? context.analysis.resolveCallee(cast<ac::InstanceOp>(owner))
                : context.analysis.resolveCallee(cast<ac::CollectionOp>(owner));
            auto kind = context.analysis.getPrimitiveKind(callee);
            if ((kind == "dff" && ordinal == 2) || (kind == "dffe" && ordinal == 3))
                choices.insert(owner->getAttrOfType<StringAttr>("instance_name").getValue().str() + "_next_value");
            else incomplete = true;
            continue;
        }
        if (!consumer) { incomplete = true; continue; }
        auto anchor = readableNameAnchor(consumer);
        if (!anchor) anchor = readableConstructionUse(consumer, budget, depth + 1);
        if (anchor) choices.insert(readableValuePart(*anchor, part));
        else incomplete = true;
    }
    if (!incomplete && choices.size() == 1) return choices.begin()->getKey().str();
    return std::nullopt;
}

std::optional<std::string> readableConstructionStem(Value value) {
    auto *operation = value.getDefiningOp();
    if (!isa_and_nonnull<ac::StructCreateOp, ac::TableCreateOp, ac::TableSplatOp>(operation))
        return std::nullopt;
    unsigned budget = 256;
    if (auto use = readableConstructionUse(value, budget)) return use;
    std::string typeName = "table";
    if (auto record = dyn_cast<ac::StructType>(value.getType())) {
        auto qualified = record.getName().getValue();
        auto local = qualified.rsplit('.').second;
        typeName = (local.empty() ? qualified : local).str();
    }
    // A multiply used anonymous constructor has one neutral shared name,
    // never a clone named for each consumer. Unemitted nodes stay unemitted.
    return (value.hasOneUse() ? "" : "shared_") + typeName + "_value";
}

void reserveReadableAuthoredNames() {
    auto reserve = [&](StringRef spelling) {
        auto id = rtlIdentifier(spelling, [&] { return definition.emitOpError(); });
        if (succeeded(id)) readableAuthoredNames.insert(rtlIdentifierStem(*id));
    };
    for (Value value : readableOrderedValues()) {
        if (auto *operation = value.getDefiningOp())
            if (auto name = operation->getAttrOfType<StringAttr>("instance_name")) reserve(name.getValue());
        auto bindings = ac::sourceValueNames(value);
        if (bindings.empty()) continue;
        reserve(readableBindingName(value, bindings));
        for (const auto &binding : bindings) reserve(binding.name.getValue());
    }
}

// Build a read-only consumer-purpose plan before emitting a single expression.
// The IDs are exactly those in rtl-names.json, independent of print order and
// identifier spelling. No operand/use, author binding or ownership cut changes.
SmallVector<Value> readablePurposeInputs(Value value) {
    auto *operation = value.getDefiningOp();
    if (!operation) return {};
    // Stop at a field projection: the whole record is not a dependency of
    // this individual field. Constructor names have a separate typed plan.
    if (isa<ac::StructGetOp>(operation)) return {};
    if (auto get = dyn_cast<ac::TableGetOp>(operation);
        get && cast<OpResult>(value).getResultNumber() == 1) return {get.getIndex()};
    if (auto choose = dyn_cast<ac::TableChooseOp>(operation)) return {choose.getMask()};
    if (auto merge = dyn_cast<ac::ValueMergeOp>(operation);
        merge && cast<OpResult>(value).getResultNumber() == 1)
        return SmallVector<Value>(merge.getGuards());
    auto inputs = operation->getOperands();
    if (isa<ac::ValueRequireOp>(operation)) inputs = inputs.drop_front();
    return SmallVector<Value>(inputs);
}

void initializeReadablePurposes() {
    auto ordered = readableOrderedValues();
    for (auto [index, value] : llvm::enumerate(ordered)) readableValueOrdinals[value] = index;
    auto seed = [&](Value value, StringRef purpose) {
        auto anchor = readableNameAnchor(readableSource(value));
        SmallVector<std::pair<Value, std::string>> pending{{value, anchor ? *anchor : purpose.str()}};
        // Each value accepts at most two distinct contexts across all seeds.
        // Thus the whole module walk is bounded by its actual graph size;
        // ambiguity stays neutral instead of choosing whichever seed ran first.
        while (!pending.empty()) {
            auto [raw, label] = pending.pop_back_val();
            Value current = readableSource(raw);
            // Do not let downstream seed order consume a nearer anchor's
            // context slots before that anchor propagates its own context.
            if (current != readableSource(value) && readableNameAnchor(current)) continue;
            auto &labels = readablePurposes[current];
            if (labels.contains(label) || labels.size() == 2) continue;
            labels.insert(label);
            if (ownershipOpaque.contains(current)) continue;
            auto *operation = current.getDefiningOp();
            if (!operation || isa<ac::InstanceOp, ac::CollectionOp>(operation) ||
                operation->getNumRegions() || !isMemoryEffectFree(operation)) continue;
            auto record = dyn_cast<ac::StructCreateOp>(operation);
            auto declaration = record ? context.analysis.lookupStruct(cast<ac::StructType>(current.getType())) : ac::StructOp();
            for (auto [index, input] : llvm::enumerate(readablePurposeInputs(current))) {
                auto next = label;
                if (declaration && index < declaration.getFields().size()) {
                    auto field = cast<DictionaryAttr>(declaration.getFields()[index]).getAs<StringAttr>("name");
                    next += "_" + field.getValue().str();
                }
                pending.emplace_back(input, std::move(next));
            }
        }
    };
    for (Value value : ordered)
        if (auto anchor = readableNameAnchor(value)) seed(value, *anchor);
    auto yield = cast<ac::YieldOp>(definition.getBody().front().back());
    for (auto [index, value] : llvm::enumerate(yield.getValues()))
        seed(value, cast<StringAttr>(definition.getOutputNames()[index]).getValue());
    definition.walk([&](Operation *operation) {
        if (!isa<ac::InstanceOp, ac::CollectionOp>(operation)) return;
        auto *callee = isa<ac::InstanceOp>(operation)
            ? context.analysis.resolveCallee(cast<ac::InstanceOp>(operation))
            : context.analysis.resolveCallee(cast<ac::CollectionOp>(operation));
        auto ports = callee ? callee->getAttrOfType<ArrayAttr>("input_names") : ArrayAttr();
        auto owner = operation->getAttrOfType<StringAttr>("instance_name").getValue().str();
        if (StringRef(owner).starts_with("__pyc_call_"))
            if (auto module = dyn_cast_or_null<ac::ModuleOp>(callee))
                owner = rtlIdentifierStem(context.names(module).rtl) + "_inst_" + StringRef(owner).drop_front(11).str();
        if (!ports || ports.size() != operation->getNumOperands()) return;
        for (auto [index, input] : llvm::enumerate(operation->getOperands())) {
            auto port = context.rtlPortName(callee, cast<StringAttr>(ports[index]).getValue());
            seed(input, owner + "_" + (succeeded(port) ? rtlIdentifierStem(*port) : cast<StringAttr>(ports[index]).getValue().str()));
        }
    });
}

std::string readablePurposeStem(Value value) {
    auto found = readablePurposes.find(readableSource(value));
    std::string stem;
    if (found != readablePurposes.end() && found->second.size() == 1)
        stem = found->second.begin()->getKey().str() + "_";
    else if (found != readablePurposes.end() && found->second.size() > 1) {
        if (readableWidth(value) == 1) {
            SmallVector<std::string> uses;
            for (const auto &entry : found->second) uses.push_back(entry.getKey().str());
            llvm::sort(uses);
            return join(uses, "_and_") + (readableControlView(value).domain <= 3 ? "_shared_check" : "_shared_path");
        }
        stem = "shared_";
    }
    stem += readableWidth(value) == 1 ? "predicate_" : "value_";
    return stem + std::to_string(readableValueOrdinals.lookup(value));
}

std::string readableDerivedName(StringRef stem) {
    auto id = rtlIdentifier(readableGeneratedStem(stem), [&] { return definition.emitOpError(); });
    return readableName(succeeded(id) ? *id : "value");
}
