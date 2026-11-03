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

// The completed plan owns every anonymous hardware value. Source names are
// available during preparation without walking producers or consumers again.
std::optional<std::string> readableNameAnchor(Value value) {
    if (auto node = presentation.find(value)) {
        if (!node->label.empty()) return node->label;
        if (!node->anchor.empty()) return node->anchor;
    }
    auto bindings = ac::sourceValueNames(value);
    if (!bindings.empty()) return readableBindingName(value, bindings);
    return std::nullopt;
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

std::string readableSemanticKind(Value value) {
    auto *op = value.getDefiningOp();
    if (!op) return "input";
    if (auto binary = dyn_cast<ac::BitsBinaryOp>(op))
        return llvm::StringSwitch<std::string>(binary.getOpcode())
            .Case("add", "sum").Case("sub", "difference").Case("mul", "product")
            .Case("and", "conditions").Case("or", "alternatives").Case("xor", "xor_value")
            .Case("udiv", "quotient").Case("urem", "remainder").Default(binary.getOpcode().str() + "_value");
    if (auto compare = dyn_cast<ac::BitsCompareOp>(op))
        return llvm::StringSwitch<std::string>(compare.getPredicate())
            .Cases({"eq", "case_eq"}, "matches").Case("ne", "differs")
            .Cases({"ult", "slt"}, "below").Cases({"ugt", "sgt"}, "above")
            .Cases({"ule", "sle"}, "at_most").Cases({"uge", "sge"}, "at_least").Default("comparison");
    if (isa<ac::ValueRequireOp>(op)) return "requirement";
    if (isa<ac::BitsSelectOp, ac::ValueMergeOp>(op)) return "choice";
    if (isa<ac::BitsConstantOp, ac::BitsConstant4Op, ac::EnumCreateOp>(op)) return "constant";
    if (isa<ac::BitsResizeOp>(op)) return "resized";
    if (isa<ac::BitsExtractOp>(op)) return "slice";
    if (isa<ac::BitsConcatOp>(op)) return "packed_value";
    if (isa<ac::BitsUnaryOp>(op)) return "inverted";
    if (auto get = dyn_cast<ac::StructGetOp>(op)) return get.getField().str();
    if (isa<ac::StructCreateOp>(op)) return "record";
    if (isa<ac::TableGetOp, ac::TableReadOp>(op))
        return cast<OpResult>(value).getResultNumber() ? "in_range" : "entry";
    if (isa<ac::TableMapOp>(op)) return "mapped_entries";
    if (isa<ac::TableMatchOp>(op)) return "match_mask";
    if (isa<ac::TableViewOp>(op)) return "entry_view";
    if (isa<ac::TableIndexOp>(op)) return "entry_index";
    if (isa<ac::TableSplatOp>(op)) return "broadcast_value";
    if (isa<ac::TableCreateOp>(op)) return "entries";
    if (isa<ac::TableFoldOp>(op)) return "reduction";
    if (auto choose = dyn_cast<ac::TableChooseOp>(op))
        return cast<OpResult>(value).getResultNumber() < choose.getCount() ? "selected_index" : "has_match";
    if (isa<ac::EnumToBitsOp>(op)) return "encoding";
    if (isa<ac::EnumFromBitsOp>(op)) return cast<OpResult>(value).getResultNumber() ? "valid_encoding" : "decoded_value";
    auto spelling = op->getName().getStringRef().rsplit('.').second;
    return spelling.empty() ? "computed_result" : spelling.str() + "_result";
}

bool readableTableOperation(Operation *op) {
    return isa_and_nonnull<ac::TableCreateOp, ac::TableSplatOp, ac::TableMapOp,
        ac::TableViewOp, ac::TableIndexOp, ac::TableReadOp, ac::TableGetOp,
        ac::TableMatchOp, ac::TableChooseOp, ac::TableFoldOp, ac::ValueMergeOp>(op);
}

LogicalResult preparePresentationGraph() {
    RtlPresentationPlan::Hooks hooks;
    hooks.canonical = [&](Value value) { return readableSource(value); };
    hooks.terminal = [&](Value value) {
        return ownershipOpaque.contains(value) || isa<BlockArgument>(value) ||
            isa_and_nonnull<ac::InstanceOp, ac::CollectionOp>(value.getDefiningOp());
    };
    hooks.oneBit = [&](Value value) { return readableWidth(value) == 1; };
    hooks.authored = [&](Value value) { return !ac::sourceValueNames(value).empty(); };
    hooks.literal = [&](Value value) {
        if (auto literal = readableLiteral(value))
            for (unsigned bit = 0; bit < 4; ++bit)
                if (*literal == std::string("1'b") + "01xz"[bit] ||
                    (bit < 2 && *literal == std::string("1'd") + "01"[bit])) return bit;
        return 4u;
    };
    hooks.inputs = [&](Value value) {
        SmallVector<Value> inputs;
        auto *op = value.getDefiningOp();
        if (!op) return inputs;
        if (auto get = dyn_cast<ac::TableGetOp>(op)) {
            if (cast<OpResult>(value).getResultNumber() == 1) return SmallVector<Value>{get.getIndex()};
            // Payload routing consumes the original in-range result as well
            // as the address and table. This result is not a new helper SSA.
            return SmallVector<Value>{get.getInput(), get.getIndex(), get.getResult(1)};
        }
        auto operands = op->getOperands();
        if (isa<ac::ValueRequireOp>(op)) operands = operands.drop_front();
        llvm::append_range(inputs, operands);
        for (Region &region : op->getRegions())
            for (Block &block : region)
                if (auto yield = dyn_cast<ac::YieldOp>(block.getTerminator())) llvm::append_range(inputs, yield.getValues());
        return inputs;
    };
    hooks.companions = [&](Value value) {
        SmallVector<Value> result;
        auto *op = value.getDefiningOp();
        if (readableTableOperation(op))
            for (Value sibling : op->getResults())
                if (sibling != value && !readableUnusedTableResult(sibling, value)) result.push_back(sibling);
        return result;
    };
    hooks.operation = [&](Value value) -> std::string {
        auto *op = value.getDefiningOp();
        if (auto binary = dyn_cast_or_null<ac::BitsBinaryOp>(op))
            if (llvm::is_contained(ArrayRef<StringRef>{"and", "or", "xor"}, binary.getOpcode())) return binary.getOpcode().str();
        if (auto compare = dyn_cast_or_null<ac::BitsCompareOp>(op))
            if (llvm::is_contained(ArrayRef<StringRef>{"eq", "ne", "case_eq"}, compare.getPredicate())) return compare.getPredicate().str();
        if (isa_and_nonnull<ac::BitsUnaryOp>(op)) return "not";
        if (isa_and_nonnull<ac::BitsSelectOp>(op)) return "select";
        if (isa_and_nonnull<ac::ValueRequireOp>(op)) return "require";
        return {};
    };
    hooks.kind = [&](Value value) { return readableSemanticKind(value); };
    hooks.inputRole = [&](Value value, unsigned slot) -> std::string {
        auto *op = value.getDefiningOp();
        if (auto create = dyn_cast_or_null<ac::StructCreateOp>(op)) {
            auto declaration = context.analysis.lookupStruct(cast<ac::StructType>(create.getResult().getType()));
            if (declaration && slot < declaration.getFields().size())
                return cast<DictionaryAttr>(declaration.getFields()[slot]).getAs<StringAttr>("name").getValue().str();
        }
        if (isa_and_nonnull<ac::TableSplatOp>(op)) return "element";
        if (isa_and_nonnull<ac::TableCreateOp>(op)) return "element_" + std::to_string(slot);
        return {};
    };
    hooks.inlineable = [&](Value value) {
        auto *op = value.getDefiningOp();
        if (!ac::sourceValueNames(value).empty() || (!readableWidth(value) && !isa_and_nonnull<ac::StructGetOp>(op))) return false;
        if (auto binary = dyn_cast_or_null<ac::BitsBinaryOp>(op))
            if (binary.getOpcode() == "udiv" || binary.getOpcode() == "urem") return false;
        return isa_and_nonnull<ac::BitsUnaryOp, ac::BitsBinaryOp, ac::BitsCompareOp, ac::BitsSelectOp,
            ac::BitsConcatOp, ac::BitsResizeOp, ac::ValueRequireOp, ac::StructGetOp, ac::BitsExtractOp>(op);
    };
    return presentation.analyze(readableOrderedValues(), std::move(hooks));
}

SmallVector<RtlPresentationPlan::Root> presentationRoots() {
    SmallVector<RtlPresentationPlan::Root> roots;
    auto yield = cast<ac::YieldOp>(definition.getBody().front().back());
    for (auto [index, value] : llvm::enumerate(yield.getValues())) {
        if (context.rtlOmittedOutput(definition, index) || context.rtlForwardedInput(definition, index)) continue;
        auto port = context.rtlPortName(definition, cast<StringAttr>(definition.getOutputNames()[index]).getValue());
        roots.push_back({value, succeeded(port) ? rtlIdentifierStem(*port) : "output", ""});
    }
    if (ownership)
        for (const auto &port : ownership->exports) roots.push_back({port.value, port.name, ""});
    for (Operation &operation : definition.getBody().front()) {
        if (!isa<ac::InstanceOp, ac::CollectionOp>(operation)) continue;
        auto *callee = isa<ac::InstanceOp>(operation) ? context.analysis.resolveCallee(cast<ac::InstanceOp>(operation))
                                                    : context.analysis.resolveCallee(cast<ac::CollectionOp>(operation));
        auto ports = callee->getAttrOfType<ArrayAttr>("input_names");
        auto owner = context.rtlAllocationStem(&operation);
        auto part = isa<ac::InstanceOp>(operation) ? context.rtlPartition(cast<ac::InstanceOp>(operation), ownership) : nullptr;
        for (auto [index, input] : llvm::enumerate(operation.getOperands())) {
            if (context.rtlOmittedInput(callee, index) || (part && part->replacedInputs.count(index))) continue;
            auto port = context.rtlPortName(callee, cast<StringAttr>(ports[index]).getValue());
            roots.push_back({input, owner + "_" + (succeeded(port) ? rtlIdentifierStem(*port) : "input"), ""});
        }
        if (part)
            for (const auto &port : part->captures) if (!port.local) roots.push_back({port.value, owner + "_" + port.name, ""});
        if (part)
            for (const auto &port : part->exports) roots.push_back({port.value, owner + "_" + port.name, ""});
        auto outputs = callee->getAttrOfType<ArrayAttr>("output_names");
        for (auto [index, value] : llvm::enumerate(operation.getResults())) {
            if (context.rtlForwardedInput(callee, index) || context.rtlOmittedOutput(callee, index)) continue;
            auto port = context.rtlPortName(callee, cast<StringAttr>(outputs[index]).getValue());
            roots.push_back({value, owner + "_" + (succeeded(port) ? rtlIdentifierStem(*port) : "output"), ""});
        }
    }
    if (context.hasPhysicalChecks()) {
        for (const auto &binding : context.sourceChecks().bindings)
            if (binding.definition == definition) {
                roots.push_back({binding.condition, "assertion_condition", ""});
                roots.push_back({binding.path, "assertion_path", ""});
            }
        for (const auto &control : context.physicalProjection().controls)
            if (control.definition == definition) {
                roots.push_back({control.raw, "control_value", ""});
                roots.push_back({control.reached, "control_reached", ""});
            }
    }
    return roots;
}

RtlPresentationPlan::Description presentationDescription(Value value) {
    RtlPresentationPlan::Description result;
    llvm::StringSet<> scopes;
    bool boundary = ownershipOpaque.contains(value) || isa<BlockArgument>(value) ||
        isa_and_nonnull<ac::InstanceOp, ac::CollectionOp>(value.getDefiningOp());
    for (auto origin : readableScopedRoles(value)) {
        auto identity = origin.getAs<DictionaryAttr>("root_identity");
        auto root = origin.getAs<StringAttr>("root_scope");
        if (boundary) continue;
        if (auto scope = origin.getAs<StringAttr>("scope")) scopes.insert(scope.getValue());
        if (!identity || !root) continue;
        if (result.owner && result.owner != identity) result.sharedOwner = true;
        result.owner = identity;
        result.rootScope = root.getValue().str();
    }
    if (result.sharedOwner) { result.owner = {}; result.rootScope.clear(); }
    if (scopes.size() == 1) result.scope = scopes.begin()->getKey().str();
    auto anchor = [&](StringRef name, unsigned rank) {
        if (rank > result.rank) { result.anchor = name.str(); result.rank = rank; }
    };
    auto bindings = ac::sourceValueNames(value);
    if (!bindings.empty()) { anchor(readableBindingName(value, bindings), 10); return result; }
    if (ownershipOpaque.contains(value)) {
        if (auto spelling = names.find(value); spelling != names.end()) anchor(spelling->second, 5);
        return result;
    }
    if (!boundary)
        if (auto role = readableRoleStem(value)) {
            unsigned rank = 2;
            for (auto origin : readableScopedRoles(value))
                if (auto kind = origin.getAs<StringAttr>("role")) {
                    if (kind.getValue() == "admission" || kind.getValue() == "effect_event" || kind.getValue() == "state_enable") rank = 8;
                    else if (kind.getValue() == "after" || kind.getValue() == "write_value") rank = std::max(rank, 6u);
                }
            anchor(*role, rank);
        }
    // These hints were attached to actual storage E operands, not inferred
    // from Boolean spelling. Keep the endpoint role on a broadcast scalar.
    if (readableEndpointValues.contains(value))
        if (auto hint = readableRoleHints.find(value); hint != readableRoleHints.end()) anchor(hint->second, 7);
    if (auto argument = dyn_cast<BlockArgument>(value)) {
        if (argument.getOwner()->getParentOp() == definition) {
            auto port = context.rtlPortName(definition, cast<StringAttr>(definition.getInputNames()[argument.getArgNumber()]).getValue());
            if (succeeded(port)) anchor(rtlIdentifierStem(*port), 5);
        }
        return result;
    }
    if (auto *allocation = value.getDefiningOp(); isa_and_nonnull<ac::InstanceOp, ac::CollectionOp>(allocation)) {
        auto *callee = isa<ac::InstanceOp>(allocation)
            ? context.analysis.resolveCallee(cast<ac::InstanceOp>(allocation))
            : context.analysis.resolveCallee(cast<ac::CollectionOp>(allocation));
        auto kind = context.analysis.getPrimitiveKind(callee);
        auto owner = context.rtlAllocationStem(allocation);
        if (kind == "dff" || kind == "dffe") anchor(owner, 5);
        else {
            auto outputs = callee->getAttrOfType<ArrayAttr>("output_names");
            unsigned slot = cast<OpResult>(value).getResultNumber();
            auto port = context.rtlPortName(callee, cast<StringAttr>(outputs[slot]).getValue());
            if (succeeded(port)) anchor(owner + "_" + rtlIdentifierStem(*port), 5);
        }
        return result;
    }
    if (auto get = value.getDefiningOp<ac::StructGetOp>()) {
        auto input = presentation.find(get.getOperand());
        if (input && !input->anchor.empty()) anchor(input->anchor + "_" + get.getField().str(), 5);
    }
    // Slot contracts stay distinct from a producer's data result. These are
    // local typed relations to planned inputs, not recursive naming searches.
    auto inputAnchor = [&](Value input) -> std::optional<std::string> {
        if (auto node = presentation.find(input); node && !node->anchor.empty()) return node->anchor;
        return std::nullopt;
    };
    if (auto get = value.getDefiningOp<ac::TableGetOp>(); get && cast<OpResult>(value).getResultNumber() == 1)
        if (auto index = inputAnchor(get.getIndex())) anchor(*index + "_in_range", 5);
    if (auto decode = value.getDefiningOp<ac::EnumFromBitsOp>(); decode && cast<OpResult>(value).getResultNumber() == 1)
        if (auto input = inputAnchor(decode.getInput())) anchor(*input + "_is_member", 5);
    if (auto match = value.getDefiningOp<ac::TableMatchOp>())
        if (auto input = inputAnchor(match.getInput())) anchor(*input + "_match_mask", 5);
    if (auto choose = value.getDefiningOp<ac::TableChooseOp>()) {
        if (auto mask = inputAnchor(choose.getMask())) {
            unsigned slot = cast<OpResult>(value).getResultNumber(), count = choose.getCount();
            anchor(*mask + "_choice_" + std::to_string(slot % count) + (slot < count ? "_index" : "_valid"), 5);
        }
    }
    if (auto merge = value.getDefiningOp<ac::ValueMergeOp>(); merge && cast<OpResult>(value).getResultNumber() == 1)
        anchor("update_has_write", 3);
    return result;
}

// The typed plan is mandatory for hardware profiles. Managed ABI uses
// its original naming path and does not prepare a hardware presentation.
void initializeReadablePurposes() {
    if (context.isPhysical() &&
        failed(presentation.plan([&](Value value) { return presentationDescription(value); }, readableExpressionLimit)))
        definition.emitOpError() << "RTL presentation plan has an unclassified runtime root";
}

std::string readablePurposeStem(Value value) {
    if (auto node = presentation.find(value); node && !node->label.empty()) return node->label;
    return readableSemanticKind(value);
}

std::string readableDerivedName(StringRef stem) {
    auto id = rtlIdentifier(readableGeneratedStem(stem), [&] { return definition.emitOpError(); });
    return readableName(succeeded(id) ? *id : "value");
}
