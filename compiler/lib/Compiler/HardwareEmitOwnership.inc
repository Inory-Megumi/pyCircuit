// A typed cut of the already verified, optimized graph. Moving a node changes
// its presentation scope, never its opcode, operands, width or storage event.
Value rtlOwnershipSource(Value value, const HardwareEmitContext *context) {
    llvm::DenseSet<Value> seen;
    while (seen.insert(value).second) {
        if (auto argument = dyn_cast<BlockArgument>(value)) {
            if (auto rule = dyn_cast<ac::RuleOp>(argument.getOwner()->getParentOp())) {
                value = rule.getCaptures()[argument.getArgNumber()];
                continue;
            }
        }
        if (auto rule = value.getDefiningOp<ac::RuleOp>()) {
            value = cast<ac::YieldOp>(rule.getBody().front().back()).getValues()[cast<OpResult>(value).getResultNumber()];
            continue;
        }
        if (auto extract = value.getDefiningOp<ac::BitsExtractOp>(); extract && context) {
            auto inType = dyn_cast<ac::BitsType>(extract.getInput().getType());
            auto outType = dyn_cast<ac::BitsType>(value.getType());
            if (inType && outType && context->isClosedStatic(extract.getLow()) &&
                context->isClosedStatic(inType.getWidth()) && context->isClosedStatic(outType.getWidth())) {
                auto low = context->staticRtlValue(extract.getLow(), extract);
                auto a = context->staticRtlValue(inType.getWidth(), extract);
                auto b = context->staticRtlValue(outType.getWidth(), extract);
                if (succeeded(low) && succeeded(a) && succeeded(b) && *low == "0" && *a == *b) {
                    value = extract.getInput();
                    continue;
                }
            }
        }
        break;
    }
    return value;
}

const RtlOwnershipPartition *HardwareEmitContext::rtlPartition(
    ac::InstanceOp allocation, const RtlOwnershipPartition *parent) const {
    for (const auto &partition : rtlPartitions)
        if (partition->allocation == allocation && partition->parent == parent) return partition.get();
    return nullptr;
}

bool HardwareEmitContext::rtlChildPartition(const RtlOwnershipPartition *child, ac::ModuleOp caller,
                                           const RtlOwnershipPartition *parent) const {
    return child->caller == caller && child->parent == parent;
}

bool HardwareEmitContext::rtlBaseNeeded(ac::ModuleOp definition) const {
    return !isPhysical() || rtlBaseDefinitions.contains(definition);
}

#include "HardwareEmitOwnershipPlan.inc"

LogicalResult prepareRtlOwnership(HardwareEmitContext &context) {
    context.package.walk([&](Operation *operation) {
        for (Value value : operation->getResults())
            context.rtlOriginalValueIds.try_emplace(value, context.rtlOriginalValueIds.size());
        for (Region &region : operation->getRegions())
            for (Block &block : region)
                for (BlockArgument argument : block.getArguments())
                    context.rtlOriginalValueIds.try_emplace(argument, context.rtlOriginalValueIds.size());
    });
    SmallVector<ac::ModuleOp> pendingModules;
    for (auto system : context.package.getOps<ac::SystemOp>())
        if (auto root = dyn_cast_or_null<ac::ModuleOp>(context.analysis.lookupDefinition(
                system.getEntry().getAs<FlatSymbolRefAttr>("callee").getValue()))) {
            pendingModules.push_back(root);
            // Managed definitions keep their complete native-compatible
            // interface; the existing wrapper supplies root defaults.
            if (!context.isPhysical()) continue;
            auto layout = ac::getModulePortLayout(root);
            auto bindings = context.rootBindings();
            if (failed(layout) || failed(bindings)) return failure();
            for (auto [offset, raw] : llvm::enumerate(layout->rootInputDefaults)) {
                unsigned index = layout->sourceInputCount + offset;
                auto width = context.analysis.getPackedWidth(root.getFunctionType().getInput(index), *bindings, root);
                if (failed(width)) return failure();
                auto value = cast<IntegerAttr>(raw).getInt();
                context.rtlRootConstants[root.getBody().front().getArgument(index)] =
                    std::to_string(*width) + "'d" + std::to_string(value);
            }
        }
    while (!pendingModules.empty()) {
        auto module = pendingModules.pop_back_val();
        if (!context.rtlActiveDefinitions.insert(module).second) continue;
        for (Operation &operation : module.getBody().front()) {
            Operation *callee = nullptr;
            if (auto instance = dyn_cast<ac::InstanceOp>(operation)) callee = context.analysis.resolveCallee(instance);
            else if (auto collection = dyn_cast<ac::CollectionOp>(operation)) callee = context.analysis.resolveCallee(collection);
            if (auto child = dyn_cast_or_null<ac::ModuleOp>(callee)) pendingModules.push_back(child);
        }
    }
    llvm::DenseSet<Operation *> protectedFinalEnables;
    for (auto caller : context.package.getOps<ac::ModuleOp>()) {
        if (!context.rtlActiveDefinitions.contains(caller)) continue;
        llvm::DenseMap<Value, llvm::DenseSet<Operation *>> recipients;
        for (auto allocation : caller.getBody().front().getOps<ac::InstanceOp>()) {
            auto *callee = context.analysis.resolveCallee(allocation);
            if (context.analysis.getPrimitiveKind(callee) == "dffe") {
                recipients[rtlOwnershipSource(allocation.getOperand(2), &context)].insert(allocation);
                continue;
            }
            auto child = dyn_cast_or_null<ac::ModuleOp>(callee);
            if (!child || !child->hasAttr("ac.transaction_wiring")) continue;
            ac::detail::SourceCheckBudget budget({});
            ac::HardwareBindings bindings;
            bindings.owner = child;
            auto wiring = ac::detail::parseTransactionWiring(child, context.analysis, bindings, budget);
            if (failed(wiring)) return failure();
            for (const auto &incoming : wiring->incoming)
                recipients[rtlOwnershipSource(allocation.getOperand(incoming.enableInput), &context)].insert(allocation);
        }
        for (const auto &entry : recipients)
            if (entry.second.size() > 1 && entry.first.getDefiningOp()) protectedFinalEnables.insert(entry.first.getDefiningOp());
        for (auto rule : caller.getBody().front().getOps<ac::RuleOp>()) {
            auto admission = rule->getAttrOfType<DictionaryAttr>("ac.sampled_admission");
            if (!admission) continue;
            bool resources = false;
            for (StringRef key : {"resources", "queue_proposals", "memory_proposals"})
                if (auto entries = admission.getAs<ArrayAttr>(key); entries && !entries.empty()) resources = true;
            auto fire = admission.getAs<IntegerAttr>("fire_result");
            if (resources && fire) {
                auto value = rtlOwnershipSource(rule.getResult(fire.getInt()), &context);
                if (auto *operation = value.getDefiningOp()) protectedFinalEnables.insert(operation);
            }
        }
    }
    llvm::DenseSet<Operation *> businessConsumers;
    if (context.isSynthesis()) {
        SmallVector<Value> pending;
        llvm::DenseSet<Value> seen;
        for (auto module : context.package.getOps<ac::ModuleOp>()) {
            if (!context.rtlActiveDefinitions.contains(module)) continue;
            auto yield = cast<ac::YieldOp>(module.getBody().front().back());
            businessConsumers.insert(yield);
            for (auto [index, value] : llvm::enumerate(yield.getValues()))
                if (!context.rtlForwardedInput(module, index)) pending.push_back(value);
            for (Operation &operation : module.getBody().front()) {
                if (!isa<ac::InstanceOp, ac::CollectionOp>(operation)) continue;
                businessConsumers.insert(&operation);
                auto *callee = isa<ac::InstanceOp>(operation)
                    ? context.analysis.resolveCallee(cast<ac::InstanceOp>(operation))
                    : context.analysis.resolveCallee(cast<ac::CollectionOp>(operation));
                for (auto [index, value] : llvm::enumerate(operation.getOperands()))
                    if (!context.rtlOmittedInput(callee, index)) pending.push_back(value);
            }
        }
        while (!pending.empty()) {
            Value value = rtlOwnershipSource(pending.pop_back_val(), &context);
            if (!seen.insert(value).second) continue;
            auto *operation = value.getDefiningOp();
            if (!operation) continue;
            businessConsumers.insert(operation);
            llvm::append_range(pending, operation->getOperands());
            for (Region &region : operation->getRegions())
                for (Block &block : region)
                    if (auto yield = dyn_cast<ac::YieldOp>(block.getTerminator()))
                        llvm::append_range(pending, yield.getValues());
        }
    }
    return prepareRtlOwnershipScopes(context, businessConsumers, protectedFinalEnables);
}
