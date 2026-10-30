// Repeated concrete module occurrences have an array of interfaces and a
// generate loop. This groups spelling only: every original occurrence retains
// its own module/state, input expression and lane in the navigation map.
struct ReadableInstanceArray {
    SmallVector<ac::InstanceOp> instances;
    ac::ModuleOp callee;
    std::string block, lane, member, parameters;
    SmallVector<std::string> outputs;
};

bool readableArrayConcreteType(Type type, unsigned depth = 0) {
    if (depth > 32) return false;
    if (auto bits = dyn_cast<ac::BitsType>(type)) return context.isClosedStatic(bits.getWidth());
    if (isa<ac::EnumType>(type)) return true;
    if (auto table = dyn_cast<ac::TableType>(type))
        return llvm::all_of(table.getShape(), [&](Attribute dim) { return context.isClosedStatic(cast<ac::StaticExprAttr>(dim)); }) &&
            readableArrayConcreteType(table.getElementType(), depth + 1);
    if (auto record = dyn_cast<ac::StructType>(type)) {
        auto declaration = context.analysis.lookupStruct(record);
        return declaration && llvm::all_of(declaration.getFields(), [&](Attribute raw) {
            return readableArrayConcreteType(cast<DictionaryAttr>(raw).getAs<TypeAttr>("type").getValue(), depth + 1);
        });
    }
    return false;
}

bool readableArrayCandidate(ac::InstanceOp instance) {
    auto module = dyn_cast_or_null<ac::ModuleOp>(context.analysis.resolveCallee(instance));
    if (!module || context.rtlPartition(instance, ownership)) return false;
    // Keep authored result identities and open layouts on their
    // established paths. Forwarded/private identity results stay bypassed.
    return llvm::all_of(instance->getResults(), [&](Value result) {
        return ac::sourceValueNames(result).empty() && readableArrayConcreteType(result.getType());
    }) && llvm::all_of(instance->getOperandTypes(), [&](Type type) { return readableArrayConcreteType(type); });
}

LogicalResult initializeReadableInstanceArrays() {
    if (!context.isSynthesis()) return success();
    SmallVector<ac::InstanceOp> available;
    for (auto instance : definition.getBody().front().getOps<ac::InstanceOp>())
        if (readableArrayCandidate(instance)) available.push_back(instance);
    llvm::DenseSet<Operation *> consumed;
    for (auto first : available) {
        if (consumed.contains(first)) continue;
        ReadableInstanceArray group;
        group.callee = cast<ac::ModuleOp>(context.analysis.resolveCallee(first));
        auto parameters = context.rtlInstanceParameters(first);
        if (failed(parameters)) return failure();
        group.parameters = *parameters;
        for (auto candidate : available) {
            if (consumed.contains(candidate) || group.instances.size() == 64 ||
                context.analysis.resolveCallee(candidate) != group.callee ||
                candidate->getAttr("parameters") != first->getAttr("parameters") ||
                candidate->getAttr("type_arguments") != first->getAttr("type_arguments") ||
                candidate->getResultTypes() != first->getResultTypes() ||
                candidate->getOperandTypes() != first->getOperandTypes()) continue;
            auto candidateParameters = context.rtlInstanceParameters(candidate);
            if (failed(candidateParameters)) return failure();
            if (*candidateParameters == group.parameters) group.instances.push_back(candidate);
        }
        if (group.instances.size() < 3) continue;
        // A common authored stem is presentation only; membership above used
        // callee identity, concrete types and exact parameter bindings.
        std::string stem = first.getInstanceName().str();
        for (auto instance : group.instances)
            while (!stem.empty() && !instance.getInstanceName().starts_with(stem)) stem.pop_back();
        while (!stem.empty() && (llvm::isDigit(stem.back()) || stem.back() == '_')) stem.pop_back();
        if (stem.empty()) stem = rtlIdentifierStem(context.names(group.callee).rtl) + "_instances";
        group.block = readableDerivedName(stem);
        group.lane = readableDerivedName(stem + "_index");
        group.member = readableDerivedName("unit_inst");
        auto ports = group.callee.getOutputNames();
        for (auto [index, result] : llvm::enumerate(first->getResults())) {
            if (context.rtlForwardedInput(group.callee, index) || context.rtlOmittedOutput(group.callee, index)) { group.outputs.emplace_back(); continue; }
            auto raw = readableSource(cast<ac::YieldOp>(group.callee.getBody().front().back()).getValues()[index]);
            auto layout = ac::getModulePortLayout(group.callee);
            if (failed(layout)) return failure();
            if (auto argument = dyn_cast<BlockArgument>(raw))
                if (index >= layout->sourceOutputCount && argument.getOwner()->getParentOp() == group.callee) {
                    group.outputs.emplace_back(); continue;
                }
            auto port = context.rtlPortName(group.callee, cast<StringAttr>(ports[index]).getValue());
            auto type = context.rtlType(result.getType(), first);
            if (failed(port) || failed(type)) return failure();
            auto signal = readableDerivedName(stem + "_" + rtlIdentifierStem(*port));
            readableDeclaration("wire", *type, signal + " [0:" + std::to_string(group.instances.size() - 1) + "]");
            group.outputs.push_back(signal);
            for (auto [lane, instance] : llvm::enumerate(group.instances))
                names[instance->getResult(index)] = signal + "[" + std::to_string(lane) + "]";
        }
        unsigned groupIndex = readableInstanceArrays.size();
        for (auto [lane, instance] : llvm::enumerate(group.instances)) {
            consumed.insert(instance);
            readableInstanceArrayLanes[instance] = {groupIndex, lane};
            readableInstanceNames[instance] = group.block + "[" + std::to_string(lane) + "]." + group.member;
        }
        readableInstanceArrays.push_back(std::move(group));
    }
    return success();
}

LogicalResult emitReadableInstanceArray(unsigned index) {
    auto &group = readableInstanceArrays[index];
    auto section = readableSections.select("array:" + group.block, "Instance array: " + group.block, 3000);
    SmallVector<std::pair<std::string, std::string>> connections;
    auto first = group.instances.front();
    for (auto [portIndex, raw] : llvm::enumerate(group.callee.getInputNames())) {
        if (context.rtlOmittedInput(group.callee, portIndex)) continue;
        auto port = context.rtlPortName(group.callee, cast<StringAttr>(raw).getValue());
        if (failed(port)) return failure();
        SmallVector<std::string> inputs;
        for (auto instance : group.instances) {
            auto input = net(instance->getOperand(portIndex));
            if (failed(input)) return failure();
            inputs.push_back(*input);
        }
        if (llvm::all_of(inputs, [&](StringRef input) { return input == inputs.front(); })) {
            connections.emplace_back(*port, inputs.front());
            continue;
        }
        auto type = context.rtlType(first->getOperand(portIndex).getType(), first);
        if (failed(type)) return failure();
        auto signal = readableDerivedName(rtlIdentifierStem(group.block) + "_" + rtlIdentifierStem(*port));
        readableDeclaration("wire", *type, signal + " [0:" + std::to_string(group.instances.size() - 1) + "]");
        for (auto [lane, input] : llvm::enumerate(inputs))
            readableAssignment(signal + "[" + std::to_string(lane) + "]", input, false);
        connections.emplace_back(*port, signal + "[" + group.lane + "]");
    }
    for (auto [portIndex, signal] : llvm::enumerate(group.outputs)) {
        if (signal.empty()) continue;
        auto port = context.rtlPortName(group.callee, cast<StringAttr>(group.callee.getOutputNames()[portIndex]).getValue());
        if (failed(port)) return failure();
        connections.emplace_back(*port, signal + "[" + group.lane + "]");
    }
    for (auto [lane, instance] : llvm::enumerate(group.instances))
        out << "  // " << group.block << "[" << lane << "]." << group.member << ": " << instance.getInstanceName() << ".\n";
    out << "  for (genvar " << group.lane << " = 0; " << group.lane << " < " << group.instances.size()
        << "; ++" << group.lane << ") begin : " << group.block << "\n    "
        << context.names(group.callee).rtl << group.parameters << " " << group.member << " (\n";
    for (auto [ordinal, connection] : llvm::enumerate(connections))
        out << "      ." << connection.first << "(" << connection.second << ")"
            << (ordinal + 1 == connections.size() ? "\n" : ",\n");
    out << "    );\n  end\n";
    return success();
}
