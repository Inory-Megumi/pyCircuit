// Names and source-call annotations only. No method spelling selects behavior.
std::optional<std::string> readableRoleStem(Value value) {
    unsigned priority = 0;
    llvm::StringSet<> choices;
    llvm::StringSet<> kinds;
    for (auto origin : ac::sourceRtlRoles(value)) {
        auto role = origin.getAs<StringAttr>("role"), scope = origin.getAs<StringAttr>("scope");
        auto state = origin.getAs<StringAttr>("state");
        if (!role || !scope) continue;
        unsigned rank = 0;
        std::string name;
        if (role.getValue() == "after" && state && !state.getValue().empty()) {
            rank = 4; name = state.getValue().str() + "_after_" + scope.getValue().str();
        } else if (role.getValue() == "index_match" && state) {
            rank = 3; name = scope.getValue().str() + "_" + state.getValue().str() + "_hit";
        } else if (role.getValue() == "lane_value" && state) {
            rank = 3; name = scope.getValue().str() + "_" + state.getValue().str() + "_lane_value";
        } else if (role.getValue() == "write_value" && state) {
            rank = 2; name = scope.getValue().str() + "_" + state.getValue().str() + "_value";
        } else if (role.getValue() == "condition") {
            rank = 2; name = scope.getValue().str() + "_condition";
            auto *operation = readableSource(value).getDefiningOp();
            if (auto get = dyn_cast_or_null<ac::StructGetOp>(operation)) {
                if (auto owner = readableNameAnchor(get.getOperand()))
                    name = scope.getValue().str() + "_" + *owner + "_" + get.getField().str();
                else name = scope.getValue().str() + "_" + get.getField().str();
            }
            if (auto compare = dyn_cast_or_null<ac::BitsCompareOp>(operation)) {
                if (auto subject = readableComparisonStem(value)) name = scope.getValue().str() + "_" + *subject;
            }
        }
        if (!rank || rank < priority) continue;
        if (rank > priority) { choices.clear(); kinds.clear(); priority = rank; }
        choices.insert(name);
        kinds.insert(role.getValue());
    }
    if (choices.size() == 1) return choices.begin()->getKey().str();
    if (choices.size() > 1) {
        if (kinds.size() != 1) return "shared_value";
        return llvm::StringSwitch<std::optional<std::string>>(kinds.begin()->getKey())
            .Case("after", "shared_candidate")
            .Case("index_match", "shared_index_match")
            .Case("lane_value", "shared_lane_value")
            .Case("write_value", "shared_write_value")
            .Case("condition", "shared_condition").Default("shared_value");
    }
    return std::nullopt;
}

std::optional<std::string> readableMethodScope(Value value) {
    llvm::StringSet<> scopes;
    for (auto origin : ac::sourceRtlRoles(value))
        if (auto role = origin.getAs<StringAttr>("role"); role && role.getValue() == "source")
            if (auto scope = origin.getAs<StringAttr>("scope")) scopes.insert(scope.getValue());
    if (scopes.size() == 1) return scopes.begin()->getKey().str();
    return std::nullopt;
}

std::string readableBindingName(Value value, ArrayRef<ac::SourceValueName> bindings) {
    // Call-result bindings name the original shared value, without cloning it.
    llvm::StringSet<> calls;
    for (auto origin : ac::sourceRtlRoles(value)) {
        auto role = origin.getAs<StringAttr>("role"), name = origin.getAs<StringAttr>("name");
        if (role && role.getValue() == "binding" && name &&
            llvm::any_of(bindings, [&](const auto &binding) { return binding.name == name; })) calls.insert(name.getValue());
    }
    if (calls.size() == 1) return calls.begin()->getKey().str();
    auto raw = bindings.front().name.getValue();
    if (readableAmbiguousBindings.contains(raw))
        if (auto scope = readableMethodScope(value)) return *scope + "_" + raw.str();
    return raw.str();
}

void initializeReadableRoles() {
    if (!context.isPhysical()) return;
    llvm::StringMap<llvm::StringSet<>> scopes;
    definition.walk([&](Operation *operation) {
        for (Value value : operation->getResults()) {
            auto scope = readableMethodScope(value);
            for (auto binding : ac::sourceValueNames(value)) scopes[binding.name.getValue()].insert(scope ? *scope : "");
        }
    });
    for (const auto &entry : scopes)
        if (entry.second.size() > 1) readableAmbiguousBindings.insert(entry.first());
    reserveReadableAuthoredNames();
    initializeReadableControlUses();
    for (Operation &operation : definition.getBody().front()) {
        if (!isa<ac::InstanceOp, ac::CollectionOp>(operation)) continue;
        auto *callee = isa<ac::CollectionOp>(operation)
            ? context.analysis.resolveCallee(cast<ac::CollectionOp>(operation))
            : context.analysis.resolveCallee(cast<ac::InstanceOp>(operation));
        if (context.analysis.getPrimitiveKind(callee) != "dffe") continue;
        Value enable = readableSource(operation.getOperand(2));
        if (isa<ac::TableType>(enable.getType()))
            if (auto scalar = readableBroadcast(enable)) enable = readableSource(scalar);
        auto state = operation.getAttrOfType<StringAttr>("instance_name");
        auto hint = state.getValue().str() + "_write_enable";
        readableEndpointValues.insert(enable);
        auto [found, inserted] = readableRoleHints.try_emplace(enable, hint);
        if (!inserted && found->second != hint) found->second = "shared_write_enable";
        if (auto binary = enable.getDefiningOp<ac::BitsBinaryOp>(); binary && binary.getOpcode() == "and") {
            // This is an exact conjunct of the storage E pin, not a new
            // eligibility/grant signal. Only a generated, known Boolean term
            // next to a possibly unknown activity term is called a check.
            for (unsigned index = 0; index < 2; ++index) {
                auto term = readableControlView(binary->getOperand(index));
                auto activity = readableControlView(binary->getOperand(1 - index));
                if (!term.value || term.literal < 4 || term.domain > 3 || activity.domain <= 3 ||
                    !ac::sourceValueNames(term.value).empty()) continue;
                auto check = state.getValue().str() + "_update_checks";
                auto [entry, added] = readableRoleHints.try_emplace(term.value, check);
                if (!added && entry->second != check) entry->second = "shared_update_checks";
            }
        }
    }
    for (auto instance : definition.getBody().front().getOps<ac::InstanceOp>()) {
        if (isReadableRegister(instance)) continue;
        auto *callee = context.analysis.resolveCallee(instance);
        auto ports = callee ? callee->getAttrOfType<ArrayAttr>("input_names") : ArrayAttr();
        if (!ports || ports.size() != instance->getNumOperands()) continue;
        for (auto [index, raw] : llvm::enumerate(instance->getOperands())) {
            if (readableWidth(raw) != 1) continue;
            auto pin = readableControlView(raw);
            auto port = context.rtlPortName(callee, cast<StringAttr>(ports[index]).getValue());
            if (failed(port)) continue;
            auto endpoint = instance.getInstanceName().str() + "_" + rtlIdentifierStem(*port);
            if (pin.value && pin.literal == 4 && ac::sourceValueNames(pin.value).empty() && !readableRoleStem(pin.value) &&
                !isa_and_nonnull<ac::InstanceOp, ac::CollectionOp>(pin.value.getDefiningOp()) &&
                !isa<BlockArgument>(pin.value)) readableRoleHints.try_emplace(pin.value, endpoint);
            auto binary = pin.value ? pin.value.getDefiningOp<ac::BitsBinaryOp>() : ac::BitsBinaryOp();
            if (!binary || binary.getOpcode() != "and" || readableWidth(raw) != 1) continue;
            for (unsigned side = 0; side < 2; ++side) {
                auto term = readableControlView(binary->getOperand(side));
                auto activity = readableControlView(binary->getOperand(1 - side));
                if (!term.value || term.literal < 4 || term.domain > 3 || activity.domain <= 3 ||
                    !ac::sourceValueNames(term.value).empty()) continue;
                readableRoleHints.try_emplace(term.value, endpoint + "_checks");
                if (activity.value && activity.literal == 4 && ac::sourceValueNames(activity.value).empty() && !readableRoleStem(activity.value))
                    readableRoleHints.try_emplace(activity.value, endpoint + "_path");
            }
        }
    }
    for (auto rule : definition.getBody().front().getOps<ac::RuleOp>()) {
        if (!rule->getNumResults()) continue;
        for (auto origin : ac::sourceRtlRoles(rule->getResult(0))) {
            auto role = origin.getAs<StringAttr>("role"), scope = origin.getAs<StringAttr>("scope");
            auto calls = origin.getAs<ArrayAttr>("calls");
            if (role && role.getValue() == "flow" && scope) readableSections.noteRoot(scope.getValue());
            if (calls)
                for (auto raw : calls)
                    if (auto method = cast<DictionaryAttr>(raw).getAs<StringAttr>("callee"))
                        readableSections.noteMethod(method.getValue());
            if (!role || role.getValue() != "flow" || !scope || !calls || calls.empty()) continue;
            auto section = readableSections.select("source_calls", "Source call order", 1);
            auto comment = [](StringRef input) {
                std::string text;
                llvm::raw_string_ostream stream(text);
                llvm::printEscapedString(input, stream);
                return text;
            };
            out << "  // Source rule " << comment(scope.getValue()) << ": calls in lexical order (conditions remain below).\n";
            unsigned shown = 0;
            for (auto raw : calls) {
                if (shown++ == 32) { out << "  //   Remaining calls are recorded in rtl-names.json.\n"; break; }
                auto call = cast<DictionaryAttr>(raw);
                out << "  //   " << comment(call.getAs<StringAttr>("caller").getValue()) << " -> "
                    << comment(call.getAs<StringAttr>("callee").getValue());
                if (auto versions = call.getAs<ArrayAttr>("versions"))
                    for (auto rawVersion : versions) {
                        auto version = cast<DictionaryAttr>(rawVersion);
                        out << "  updates " << comment(version.getAs<StringAttr>("state").getValue());
                    }
                out << ".\n";
            }
        }
    }
    initializeReadablePurposes();
}

llvm::json::Value readableRoleJson(Attribute attribute, unsigned depth = 0) {
    if (depth > 16) return nullptr;
    if (auto string = dyn_cast<StringAttr>(attribute)) return string.getValue().str();
    if (auto integer = dyn_cast<IntegerAttr>(attribute)) return integer.getInt();
    if (auto array = dyn_cast<ArrayAttr>(attribute)) {
        llvm::json::Array values;
        for (auto value : array) values.push_back(readableRoleJson(value, depth + 1));
        return values;
    }
    if (auto dictionary = dyn_cast<DictionaryAttr>(attribute)) {
        llvm::json::Object values;
        for (auto item : dictionary) values[item.getName().strref()] = readableRoleJson(item.getValue(), depth + 1);
        return values;
    }
    std::string text;
    llvm::raw_string_ostream stream(text);
    attribute.print(stream);
    return text;
}
