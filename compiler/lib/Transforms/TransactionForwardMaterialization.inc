FailureOr<Value> projectForwardLeaf(Value value, ArrayAttr fields,
    const ac::HardwareAnalysis &hardware, const ac::HardwareBindings &bindings,
    Operation *site, OpBuilder &builder, SourceCheckBudget &budget) {
    for (Attribute raw : fields) {
        auto structure = dyn_cast<ac::StructType>(value.getType());
        auto declaration = structure ? hardware.lookupStruct(structure) : ac::StructOp();
        Type type;
        if (!declaration || !charge(budget, site, 32 + declaration.getFields().size())) return failure();
        for (Attribute rawField : declaration.getFields()) {
            auto field = cast<DictionaryAttr>(rawField);
            if (field.getAs<StringAttr>("name") == raw) type = field.getAs<TypeAttr>("type").getValue();
        }
        auto resolved = type ? hardware.resolveType(type, bindings, site) : FailureOr<Type>(failure());
        if (failed(resolved)) return failure();
        OperationState state(ac::sourceIdentityLocation(site->getLoc()), ac::StructGetOp::getOperationName());
        state.addOperands(value); state.addTypes(*resolved);
        state.addAttribute("field", raw);
        value = builder.create(state)->getResult(0);
    }
    return value;
}
