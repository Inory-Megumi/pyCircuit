// Read-only projection of compiler-private transport. Public outputs, check
// companions and collections keep their original ABI. Scope variants apply
// the same exact source-field relation to both sides of a projected output.
bool readablePrivateOutput(const HardwareEmitContext &context, ac::ModuleOp module, unsigned output) {
    if (!context.isSynthesis()) return false;
    auto layout = ac::getModulePortLayout(module);
    if (failed(layout) || output < layout->sourceOutputCount ||
        llvm::is_contained(layout->outputValidity, static_cast<int64_t>(output))) return false;
    for (auto [payload, validity] : layout->routedOutputValidity)
        if (output == payload || output == validity) return false;
    auto package = context.package;
    for (auto system : package.getOps<ac::SystemOp>())
        if (system.getEntry().getAs<FlatSymbolRefAttr>("callee").getValue() == module.getSymName()) return false;
    bool supported = true;
    package.walk([&](ac::CollectionOp instance) {
        if (context.analysis.resolveCallee(instance) == module) supported = false;
    });
    return supported;
}

std::optional<RtlOutputProjection> HardwareEmitContext::rtlOutputProjection(Operation *definition, unsigned output) const {
    auto key = std::make_pair(definition, output);
    if (auto found = rtlOutputProjections_.find(key); found != rtlOutputProjections_.end()) return found->second;
    auto compute = [&]() -> std::optional<RtlOutputProjection> {
    auto module = dyn_cast<ac::ModuleOp>(definition);
    if (!module || !readablePrivateOutput(*this, module, output)) return std::nullopt;
    auto layout = ac::getModulePortLayout(module);
    auto yield = cast<ac::YieldOp>(module.getBody().front().back());
    Value target = rtlOwnershipSource(yield.getValues()[output], this);
    for (unsigned index = 0; index < layout->sourceOutputCount; ++index) {
        struct Entry { Value value; SmallVector<std::string> path; };
        SmallVector<Entry> pending{{yield.getValues()[index], {}}};
        unsigned budget = 256;
        while (!pending.empty() && budget--) {
            auto entry = pending.pop_back_val();
            entry.value = rtlOwnershipSource(entry.value, this);
            if (entry.value == target) return RtlOutputProjection{index, std::move(entry.path)};
            Value projected = target;
            SmallVector<std::string> suffix;
            unsigned remaining = 32;
            while (remaining--) {
                auto get = projected.getDefiningOp<ac::StructGetOp>();
                if (!get) break;
                suffix.push_back(get.getField().str());
                projected = rtlOwnershipSource(get.getOperand(), this);
                if (projected == entry.value) {
                    llvm::append_range(entry.path, llvm::reverse(suffix));
                    return RtlOutputProjection{index, std::move(entry.path)};
                }
            }
            auto create = entry.value.getDefiningOp<ac::StructCreateOp>();
            if (!create) continue;
            auto record = analysis.lookupStruct(cast<ac::StructType>(entry.value.getType()));
            if (!record) continue;
            for (auto [field, input] : llvm::enumerate(create->getOperands())) {
                auto path = entry.path;
                path.push_back(cast<DictionaryAttr>(record.getFields()[field]).getAs<StringAttr>("name").getValue().str());
                pending.push_back({input, std::move(path)});
            }
        }
    }
    return std::nullopt;
    };
    auto result = compute();
    rtlOutputProjections_.try_emplace(key, result);
    return result;
}

bool HardwareEmitContext::rtlOmittedOutput(Operation *definition, unsigned output) const {
    auto key = std::make_pair(definition, output);
    if (auto found = rtlOmittedOutputs_.find(key); found != rtlOmittedOutputs_.end()) return found->second;
    auto compute = [&]() -> bool {
    auto module = dyn_cast<ac::ModuleOp>(definition);
    if (!module || !readablePrivateOutput(*this, module, output)) return false;
    if (rtlOutputProjection(module, output)) return true;
    bool used = false, found = false;
    auto scope = package;
    scope.walk([&](ac::InstanceOp instance) {
        if (used || analysis.resolveCallee(instance) != module) return;
        found = true;
        SmallVector<Value> pending{instance.getResult(output)};
        llvm::DenseSet<Value> visited;
        unsigned budget = 256;
        while (!pending.empty()) {
            if (!budget--) { used = true; return; }
            Value value = pending.pop_back_val();
            if (!visited.insert(value).second) continue;
            for (OpOperand &use : value.getUses()) {
                auto *owner = use.getOwner();
                if (auto rule = dyn_cast<ac::RuleOp>(owner))
                    pending.push_back(rule.getBody().front().getArgument(use.getOperandNumber()));
                else if (isa<ac::YieldOp>(owner) && isa<ac::RuleOp>(owner->getParentOp()))
                    pending.push_back(cast<ac::RuleOp>(owner->getParentOp()).getResult(use.getOperandNumber()));
                else if (isa<ac::ValueRequireOp>(owner) && use.getOperandNumber() == 0) continue;
                else { used = true; return; }
            }
        }
    });
    return found && !used;
    };
    bool result = compute();
    rtlOmittedOutputs_.try_emplace(key, result);
    return result;
}

std::optional<std::string> readableResourceInputStem(ac::ModuleOp module, unsigned input) {
    auto wiring = module->getAttrOfType<DictionaryAttr>("ac.queue_wiring");
    auto incoming = wiring ? wiring.getAs<ArrayAttr>("incoming") : ArrayAttr();
    if (!incoming) return std::nullopt;
    for (auto raw : incoming) {
        auto binding = cast<DictionaryAttr>(raw);
        auto path = binding.getAs<IntegerAttr>("path"), data = binding.getAs<IntegerAttr>("data");
        bool isPath = path && path.getInt() == input;
        bool isData = data && data.getInt() == input;
        if (!isPath && !isData) continue;
        auto queue = binding.getAs<DictionaryAttr>("queue");
        auto declaration = queue ? queue.getAs<DictionaryAttr>("declaration") : DictionaryAttr();
        auto owner = queue ? queue.getAs<DictionaryAttr>("owner") : DictionaryAttr();
        auto ownerPath = owner ? owner.getAs<ArrayAttr>("instance_path") : ArrayAttr();
        if (!declaration || !ownerPath || !ownerPath.empty()) continue;
        for (auto instance : module.getBody().front().getOps<ac::InstanceOp>())
            if (instance.getOccurrence() == declaration) {
                auto kind = binding.getAs<StringAttr>("kind");
                if (kind) return instance.getInstanceName().str() + "_" + kind.getValue().str() + (isData ? "_data" : "");
            }
    }
    return std::nullopt;
}

std::optional<std::string> readableStateInputStem(const HardwareEmitContext &context, ac::ModuleOp module, unsigned input) {
    auto wiring = module->getAttrOfType<DictionaryAttr>("ac.transaction_wiring");
    auto incoming = wiring ? wiring.getAs<ArrayAttr>("incoming") : ArrayAttr();
    if (!incoming) return std::nullopt;
    for (auto raw : incoming) {
        auto binding = cast<DictionaryAttr>(raw);
        auto data = binding.getAs<IntegerAttr>("data"), enable = binding.getAs<IntegerAttr>("enable");
        bool isData = data && data.getInt() == input, isEnable = enable && enable.getInt() == input;
        if (!isData && !isEnable) continue;
        auto state = binding.getAs<DictionaryAttr>("state");
        auto owner = state ? state.getAs<DictionaryAttr>("owner") : DictionaryAttr();
        auto path = owner ? owner.getAs<ArrayAttr>("instance_path") : ArrayAttr();
        auto declaration = state ? state.getAs<DictionaryAttr>("declaration") : DictionaryAttr();
        if (!path || !declaration) continue;
        std::string prefix;
        auto current = module;
        for (Attribute occurrence : path) {
            ac::InstanceOp selected;
            for (auto instance : current.getBody().front().getOps<ac::InstanceOp>())
                if (instance.getOccurrence() == occurrence) selected = instance;
            auto child = selected ? dyn_cast_or_null<ac::ModuleOp>(context.analysis.resolveCallee(selected)) : ac::ModuleOp();
            if (!child) return std::nullopt;
            prefix += selected.getInstanceName().str() + "_";
            current = child;
        }
        for (auto storage : current.getBody().front().getOps<ac::InstanceOp>())
            if (storage.getOccurrence() == declaration)
                return prefix + storage.getInstanceName().str() + (isEnable ? "_enable" : "_next");
    }
    return std::nullopt;
}
