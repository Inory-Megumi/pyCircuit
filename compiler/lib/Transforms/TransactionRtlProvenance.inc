// Run only after the complete detached transaction candidate has passed its
// owning source/correspondence verifier. These Locations carry no SSA uses or
// semantic attributes; they do not change admission, scheduling or commit.
void retainTransactionRtlProvenance(const PreparedTransactionLowering &prepared,
                                    detail::MaterializedTransactionLowering &candidate) {
    Builder builder(prepared.original->getContext());
    auto owner = [&](ac::ModuleOp root, ac::ModuleOp definition, ArrayAttr path) {
        return builder.getDictionaryAttr({
            builder.getNamedAttr("root", FlatSymbolRefAttr::get(root.getSymNameAttr())),
            builder.getNamedAttr("definition", FlatSymbolRefAttr::get(definition.getSymNameAttr())),
            builder.getNamedAttr("path", path)});
    };
    // IRMapping is pointer-keyed. Traverse immutable source order instead so
    // shared values receive Location overlays in the same order in every
    // process, including independent System compilations for each backend.
    prepared.original->walk([&](Operation *operation) {
        if (operation->getNumRegions() ||
            isa<ac::SourceStateOp, ac::SourceStateReadOp, ac::InstanceOp, ac::CollectionOp>(operation) ||
            operation->getParentOfType<ac::SourceMethodOp>()) return;
        auto module = operation->getParentOfType<ac::ModuleOp>();
        if (!module) return;
        for (Value source : operation->getResults()) {
            Value mapped = candidate.packageMap.lookupOrNull(source);
            if (!mapped) continue;
            auto target = dyn_cast<OpResult>(mapped);
            if (!target || operation->getName() != target.getOwner()->getName()) continue;
            ac::retainSourceRtlOwner(target.getOwner(), owner(module, module, builder.getArrayAttr({})));
        }
    });
    for (auto [ordinal, preparation] : llvm::enumerate(prepared.transactions)) {
        const auto &plan = *preparation.plan;
        auto &actual = candidate.transactions[ordinal];
        auto routingModule = plan.routingModule;
        auto scope = [&](unsigned frame) {
            auto method = plan.frames[frame].method;
            auto transaction = plan.transaction;
            return method ? method.getSymNameAttr() : transaction.getNameAttr();
        };
        auto role = [&](Value value, unsigned frame, StringRef kind, StringRef state = {}, StringRef name = {}) {
            if (!value) return;
            auto definition = plan.instances[plan.frames[frame].anchor].definition;
            ac::retainSourceRtlRole(value, builder.getDictionaryAttr({
                builder.getNamedAttr("scope", scope(frame)),
                builder.getNamedAttr("definition", definition.getSymNameAttr()),
                builder.getNamedAttr("root", routingModule.getSymNameAttr()),
                builder.getNamedAttr("path", plan.instances[plan.frames[frame].anchor].occurrencePath),
                builder.getNamedAttr("frame", builder.getI64IntegerAttr(frame)),
                builder.getNamedAttr("role", builder.getStringAttr(kind)),
                builder.getNamedAttr("state", builder.getStringAttr(state)),
                builder.getNamedAttr("name", builder.getStringAttr(name))}));
        };
        auto stateName = [&](unsigned id) { auto state = plan.owners[id].declaration; return state.getInstanceName(); };
        auto frameOwner = [&](unsigned frame) {
            const auto &instance = plan.instances[plan.frames[frame].anchor];
            return owner(plan.routingModule, instance.definition, instance.occurrencePath);
        };
        auto stateOwner = [&](unsigned state) {
            const auto &instance = plan.instances[plan.owners[state].anchor];
            return owner(plan.routingModule, instance.definition, instance.occurrencePath);
        };
        for (auto [frame, mapping] : llvm::enumerate(actual.frames)) {
            auto method = plan.frames[frame].method;
            if (!method) continue;
            auto provenance = frameOwner(frame);
            method.walk([&](Operation *operation) {
                if (operation->getParentOfType<ac::SourceMethodOp>() != method) return;
                for (Value source : operation->getResults()) {
                    Value mapped = mapping.lookupOrNull(source);
                    if (!mapped) continue;
                    auto target = dyn_cast<OpResult>(mapped);
                    if (!target || operation->getName() != target.getOwner()->getName()) continue;
                    ac::retainSourceRtlOwner(target.getOwner(), provenance);
                    role(target, frame, "source");
                }
            });
        }
        for (const auto &branch : plan.branches)
            role(actual.boundValues[branch.condition], branch.frame, "condition");
        for (auto [id, ref] : llvm::enumerate(plan.values)) {
            auto method = plan.frames[ref.frame].method;
            Value sourceValue = ref.value;
            auto *parent = sourceValue.getParentRegion()->getParentOp();
            if (method && (parent == method || parent->getParentOfType<ac::SourceMethodOp>() == method))
                role(actual.boundValues[id], ref.frame, "source");
        }
        for (auto [id, join] : llvm::enumerate(plan.joins))
            role(actual.stateJoins[id].value, plan.branches[join.branch].frame, "after", stateName(join.owner));
        for (auto [id, write] : llvm::enumerate(plan.writes)) {
            auto state = stateName(write.owner);
            role(actual.boundValues[write.selectedPayload.value_or(write.value)], write.frame, "write_value", state);
            role(actual.conditionalWrites[id].value, write.frame, "after", state);
            if (id >= actual.selectedWrites.size()) continue;
            for (auto *operation : actual.selectedWrites[id].generated) {
                if (auto compare = dyn_cast<ac::BitsCompareOp>(operation);
                    compare && compare.getPredicate() == "eq" && operation->getParentOfType<ac::TableMapOp>())
                    role(operation->getResult(0), write.frame, "index_match", state);
                if (isa<ac::ValueMergeOp>(operation)) role(operation->getResult(0), write.frame, "lane_value", state);
            }
        }
        SmallVector<Attribute> calls;
        for (const auto &call : plan.calls) {
            SmallVector<Attribute> versions;
            for (const auto &after : call.exitVersions) {
                auto before = llvm::find_if(call.entryVersions, [&](const auto &entry) { return entry.owner == after.owner; });
                if (before == call.entryVersions.end() || before->version == after.version) continue;
                auto state = stateName(after.owner);
                role(actual.versions[after.version].data, call.callee, "after", state);
                versions.push_back(builder.getDictionaryAttr({
                    builder.getNamedAttr("state", builder.getStringAttr(state)),
                    builder.getNamedAttr("before", builder.getI64IntegerAttr(before->version)),
                    builder.getNamedAttr("after", builder.getI64IntegerAttr(after.version))}));
            }
            for (const auto &result : call.results)
                for (const auto &binding : ac::sourceValueNames(plan.values[result.result].value))
                    role(actual.boundValues[result.result], call.caller, "binding", {}, binding.name.getValue());
            calls.push_back(builder.getDictionaryAttr({
                builder.getNamedAttr("caller", scope(call.caller)),
                builder.getNamedAttr("callee", scope(call.callee)),
                builder.getNamedAttr("versions", builder.getArrayAttr(versions))}));
        }
        if (actual.rule->getNumResults())
            ac::retainSourceRtlRole(actual.rule->getResult(0), builder.getDictionaryAttr({
                builder.getNamedAttr("scope", scope(plan.rootFrame)),
                builder.getNamedAttr("role", builder.getStringAttr("flow")),
                builder.getNamedAttr("calls", builder.getArrayAttr(calls))}));
        for (auto [id, branch] : llvm::enumerate(plan.branchResults))
            for (auto *operation : actual.branchResults[id].generated)
                ac::retainSourceRtlOwner(operation, frameOwner(branch.frame));
        for (auto [id, branch] : llvm::enumerate(plan.joins))
            for (auto *operation : actual.stateJoins[id].generated)
                ac::retainSourceRtlOwner(operation, stateOwner(branch.owner));
        for (auto [id, write] : llvm::enumerate(plan.writes))
            for (auto *operation : actual.conditionalWrites[id].generated)
                ac::retainSourceRtlOwner(operation, stateOwner(write.owner));
        for (auto [id, output] : llvm::enumerate(preparation.outputs))
            for (auto *operation : actual.commits[id].data.generated)
                ac::retainSourceRtlOwner(operation, stateOwner(output.binding.owner));
    }
    for (auto &composition : candidate.compositions) {
        auto definition = composition.source.composer->getParentOfType<ac::ModuleOp>();
        SmallVector<Attribute> path;
        for (auto instance : composition.source.path) path.push_back(instance.getOccurrence());
        auto provenance = owner(composition.source.module, definition, builder.getArrayAttr(path));
        ac::retainSourceRtlOwner(composition.rule, provenance);
        for (auto *operation : composition.generated) ac::retainSourceRtlOwner(operation, provenance);
    }
}
