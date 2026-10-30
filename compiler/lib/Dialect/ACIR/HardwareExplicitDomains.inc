// Synthesis-only identity for explicitly supplied domain pins. This follows
// actual occurrence arguments and ordered record fields, never signal names.
llvm::DenseMap<std::pair<Value, ArrayAttr>, unsigned> explicitRootPins;
llvm::DenseSet<unsigned> clockPins;
if (!explicitDomains) clockPins.insert(1);
std::function<FailureOr<unsigned>(Value, uint64_t, unsigned, ArrayRef<StringAttr>)> explicitPin;
explicitPin = [&](Value value, uint64_t owner, unsigned depth,
                  ArrayRef<StringAttr> path) -> FailureOr<unsigned> {
    const auto &occurrence = inventory.owners[owner];
    auto *site = value.getDefiningOp();
    if (!site) site = value.getParentBlock()->getParentOp();
    if (depth > 256 || failed(budget.debit(1 + path.size(), site)))
        return site->emitOpError() << "explicit domain identity exceeds bounded traversal";
    if (auto argument = dyn_cast<BlockArgument>(value)) {
        auto *parent = argument.getOwner()->getParentOp();
        if (auto rule = dyn_cast<RuleOp>(parent))
            return explicitPin(rule.getCaptures()[argument.getArgNumber()], owner, depth + 1, path);
        if (parent != occurrence.definition) return 0u;
        if (occurrence.parent)
            return explicitPin(occurrence.path.back().allocation->getOperand(argument.getArgNumber()),
                               *occurrence.parent, depth + 1, path);
        Type leaf = argument.getType();
        for (auto field : path) {
            auto resolved = resolveType(leaf, occurrence.bindings, site);
            if (failed(resolved)) return failure();
            auto record = dyn_cast<StructType>(*resolved);
            auto declaration = record ? lookupStruct(record) : StructOp();
            if (!declaration) return 0u;
            bool found = false;
            for (auto raw : declaration.getFields()) {
                auto entry = cast<DictionaryAttr>(raw);
                if (entry.getAs<StringAttr>("name") != field) continue;
                leaf = entry.getAs<TypeAttr>("type").getValue();
                found = true;
                break;
            }
            if (!found) return 0u;
        }
        auto resolved = resolveType(leaf, occurrence.bindings, site);
        if (failed(resolved)) return failure();
        if (!isa<BitsType>(*resolved)) return 0u;
        auto width = getPackedWidth(*resolved, occurrence.bindings, site);
        if (failed(width)) return failure();
        if (*width != 1) return 0u;
        SmallVector<Attribute> fields(path.begin(), path.end());
        auto key = std::make_pair(value, ArrayAttr::get(value.getContext(), fields));
        auto found = explicitRootPins.find(key);
        if (found != explicitRootPins.end()) return found->second;
        if (explicitRootPins.size() >= std::numeric_limits<unsigned>::max() - 3)
            return site->emitOpError() << "too many explicit domain pins";
        unsigned identity = 3 + explicitRootPins.size();
        explicitRootPins.try_emplace(key, identity);
        return identity;
    }
    if (auto get = value.getDefiningOp<StructGetOp>()) {
        SmallVector<StringAttr> fields{StringAttr::get(value.getContext(), get.getField())};
        llvm::append_range(fields, path);
        return explicitPin(get->getOperand(0), owner, depth + 1, fields);
    }
    if (auto create = value.getDefiningOp<StructCreateOp>(); create && !path.empty()) {
        auto declaration = lookupStruct(cast<StructType>(value.getType()));
        for (auto [index, raw] : llvm::enumerate(declaration.getFields()))
            if (cast<DictionaryAttr>(raw).getAs<StringAttr>("name") == path.front())
                return explicitPin(create->getOperand(index), owner, depth + 1, path.drop_front());
        return 0u;
    }
    if (auto result = dyn_cast<OpResult>(value)) {
        if (auto rule = dyn_cast<RuleOp>(result.getOwner()))
            return explicitPin(cast<YieldOp>(rule.getBody().front().back()).getValues()[result.getResultNumber()],
                               owner, depth + 1, path);
        if (isa<InstanceOp, CollectionOp>(result.getOwner())) {
            auto found = children.find({owner, result.getOwner()});
            if (found == children.end()) return 0u;
            unsigned common = 0;
            for (auto child : found->second) {
                auto definition = inventory.owners[child].definition;
                auto values = cast<YieldOp>(definition.getBody().front().back()).getValues();
                auto id = explicitPin(values[result.getResultNumber()], child, depth + 1, path);
                if (failed(id)) return failure();
                if (!*id || (common && common != *id)) return 0u;
                common = *id;
            }
            return common;
        }
    }
    if (auto extract = value.getDefiningOp<BitsExtractOp>(); extract && path.empty()) {
        auto low = evaluateStatic(extract.getLow(), occurrence.bindings, extract);
        auto input = getPackedWidth(extract.getInput().getType(), occurrence.bindings, extract);
        auto output = getPackedWidth(value.getType(), occurrence.bindings, extract);
        if (failed(low) || failed(input) || failed(output)) return failure();
        auto integer = dyn_cast<MathIntAttr>(*low);
        if (integer && llvm::APSInt(integer.getCanonicalValue()).isZero() && *input == *output)
            return explicitPin(extract.getInput(), owner, depth + 1, path);
    }
    if (auto splat = value.getDefiningOp<TableSplatOp>())
        return explicitPin(splat.getInput(), owner, depth + 1, path);
    if (auto create = value.getDefiningOp<TableCreateOp>()) {
        unsigned common = 0;
        for (auto element : create->getOperands()) {
            auto id = explicitPin(element, owner, depth + 1, path);
            if (failed(id)) return failure();
            if (!*id || (common && common != *id)) return 0u;
            common = *id;
        }
        return common;
    }
    return 0u;
};
