// Render the verified packed layout without changing lane order or bounds.
std::optional<uint64_t> readableUnsigned(StringRef spelling) {
    uint64_t number = 0;
    if (spelling.starts_with("-") || spelling.getAsInteger(10, number))
        return std::nullopt;
    return number;
}

std::optional<uint64_t> readableConstantIndex(Value value) {
    value = readableSource(value);
    auto constant = value.getDefiningOp<ac::BitsConstantOp>();
    auto width = readableWidth(value);
    if (!constant || !width || !context.isClosedStatic(constant.getValue()))
        return std::nullopt;
    auto text = context.staticRtlValue(constant.getValue(), constant);
    if (failed(text)) return std::nullopt;
    auto number = readableUnsigned(*text);
    // A source integer outside the Bits representation may wrap. Keep the
    // existing sized RTL comparison rather than folding the untruncated value.
    if (!number || (*width < 64 && *number >= (uint64_t{1} << *width)))
        return std::nullopt;
    return number;
}

std::string readableTableBoundWidth(StringRef count, StringRef indexWidth) {
    auto n = readableUnsigned(count), k = readableUnsigned(indexWidth);
    if (n && k && *n && *n < std::numeric_limits<uint64_t>::max()) {
        uint64_t bits = llvm::APInt(64, *n).getActiveBits();
        return std::to_string(std::max(*k, bits));
    }
    auto b = "$clog2(64'(" + count.str() + ") + 64'd1)";
    return "((" + indexWidth.str() + ") > (" + b + ") ? (" +
           indexWidth.str() + ") : (" + b + "))";
}

FailureOr<std::string> readablePackedElement(StringRef value, StringRef ordinal,
                                             ac::TableType type, Operation *site) {
    auto dimensions = context.rtlTableDimensions(type, site);
    if (failed(dimensions)) return failure();
    if (!dimensions->empty())
        return value.str() + "[" + ordinal.str() + "]";
    auto count = context.shapeSize(type.getShape(), site, true);
    auto width = context.payloadWidth(type.getElementType(), site, true);
    if (failed(count) || failed(width)) return failure();
    auto n = readableUnsigned(*count), w = readableUnsigned(*width);
    auto i = readableUnsigned(ordinal);
    if (n && w && i && *n && *w && *i < *n &&
        *n <= std::numeric_limits<uint64_t>::max() / *w) {
        uint64_t low = (*n - 1 - *i) * *w;
        return value.str() + "[" + std::to_string(low + *w - 1) + ":" +
               std::to_string(low) + "]";
    }
    if (n && w)
        return value.str() + "[(" + *count + "-1-(" + ordinal.str() + "))*" +
               *width + " +: " + *width + "]";
    return value.str() + "[((" + *count + ")-1-(" + ordinal.str() + "))*(" +
           *width + ") +: (" + *width + ")]";
}
