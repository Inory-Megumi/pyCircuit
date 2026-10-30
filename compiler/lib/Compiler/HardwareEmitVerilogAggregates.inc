// Formatting only replaces whitespace outside strings with line breaks.
// Escaped SV identifiers retain a whitespace terminator at every boundary.
void readableAssignment(StringRef target, StringRef expression, bool procedural = false) {
    std::string prefix = std::string("  ") + (procedural ? "always_comb " : "assign ") +
        target.str() + " = ";
    // A typed select plan already owns its line/branch boundaries.
    if (expression.contains('\n')) {
        out << prefix << expression << ";\n";
        return;
    }
    if (!context.isPhysical() || prefix.size() + expression.size() <= 112) {
        out << prefix << expression << ";\n";
        return;
    }
    out << prefix << "\n    ";
    size_t start = 0, column = 4;
    bool quoted = false, escapedStringByte = false;
    for (size_t i = 0; i <= expression.size(); ++i) {
        if (i < expression.size()) {
            char byte = expression[i];
            if (quoted) {
                if (!escapedStringByte && byte == '"') quoted = false;
                escapedStringByte = !escapedStringByte && byte == '\\';
            } else if (byte == '"') {
                quoted = true;
            }
            if (byte != ' ' || quoted) continue;
        }
        auto word = expression.slice(start, i < expression.size() ? i + 1 : i);
        if (column > 4 && column + word.size() > 112) {
            out << "\n    ";
            column = 4;
        }
        out << word;
        column += word.size();
        start = i + 1;
    }
    out << ";\n";
}

// Recover aggregate choices from the verified per-field representation.
// No operation is rewritten and no shared selector is duplicated.
struct ReadableAggregateChoice {
    Value condition;
    Value onTrue;
    Value onFalse;
};

bool readablePrivateValue(Value value) {
    if (!ac::sourceValueNames(value).empty()) return false;
    llvm::DenseSet<Value> visited;
    return readableUseCount(value, visited) == 1;
}

Value readableChoiceCarrier(Value value) {
    value = readableSource(value);
    for (unsigned depth = 0; depth != 8; ++depth) {
        if (!readablePrivateValue(value)) break;
        if (auto decode = value.getDefiningOp<ac::EnumFromBitsOp>()) {
            llvm::DenseSet<Value> seen;
            if (readableRtlUsed(decode.getResult(1), seen)) break;
        }
        Value operand = readableEnumOperand(value);
        if (operand == value) break;
        value = readableSource(operand);
    }
    return value;
}

std::optional<ReadableAggregateChoice> readableRecordChoice(Value value, unsigned depth = 0) {
    if (depth > 32) return std::nullopt;
    value = readableSource(value);
    auto create = value.getDefiningOp<ac::StructCreateOp>();
    auto type = dyn_cast<ac::StructType>(value.getType());
    auto declaration = type ? context.analysis.lookupStruct(type) : ac::StructOp();
    if (!create || !declaration || create->getNumOperands() == 0)
        return std::nullopt;
    auto fields = declaration.getFields();
    if (fields.size() != create->getNumOperands()) return std::nullopt;
    std::optional<ReadableAggregateChoice> choice;
    for (auto [raw, input] : llvm::zip(fields, create->getOperands())) {
        input = readableSource(input);
        if (!readablePrivateValue(input)) return std::nullopt;
        std::optional<ReadableAggregateChoice> fieldChoice;
        Value selected = readableChoiceCarrier(input);
        if (auto select = selected.getDefiningOp<ac::BitsSelectOp>();
            select && readablePrivateValue(selected)) {
            fieldChoice = ReadableAggregateChoice{readableSource(select->getOperand(0)),
                readableChoiceCarrier(select->getOperand(1)), readableChoiceCarrier(select->getOperand(2))};
        } else if (isa<ac::StructType>(input.getType())) {
            fieldChoice = readableRecordChoice(input, depth + 1);
        }
        if (!fieldChoice) return std::nullopt;
        auto a = fieldChoice->onTrue, b = fieldChoice->onFalse;
        auto left = a.getDefiningOp<ac::StructGetOp>();
        auto right = b.getDefiningOp<ac::StructGetOp>();
        auto field = cast<DictionaryAttr>(raw).getAs<StringAttr>("name");
        if (!left || !right || left.getField() != field.getValue() ||
            right.getField() != field.getValue() ||
            !ac::sourceValueNames(a).empty() || !ac::sourceValueNames(b).empty())
            return std::nullopt;
        ReadableAggregateChoice part{fieldChoice->condition,
            readableSource(left->getOperand(0)), readableSource(right->getOperand(0))};
        if (part.onTrue.getType() != type || part.onFalse.getType() != type)
            return std::nullopt;
        if (!choice) choice = part;
        else if (choice->condition != part.condition || choice->onTrue != part.onTrue ||
                 choice->onFalse != part.onFalse) return std::nullopt;
    }
    return choice;
}

std::optional<ReadableAggregateChoice> readableAggregateChoice(Value value) {
    // Current lowering can retain the original whole-value choice as one
    // merge instead of decomposing it into per-field selects. Render that
    // exact choice only when its independent enable result is not live.
    if (auto merge = value.getDefiningOp<ac::ValueMergeOp>();
        merge && value == merge->getResult(0) && merge.getPaths().size() == 1 &&
        cast<ArrayAttr>(merge.getPaths()[0]).empty() &&
        merge.getGuards().size() == 1 && merge.getValues().size() == 1) {
        llvm::DenseSet<Value> visited;
        if (!readableRtlUsed(merge->getResult(1), visited))
            return ReadableAggregateChoice{readableSource(merge.getGuards().front()),
                readableSource(merge.getValues().front()), readableSource(merge.getBase())};
    }
    // Rule results must first forward to the actual producer. Otherwise its
    // authored binding could be replaced by an anonymous wrapper name.
    if (!value.getDefiningOp() ||
        !isa<ac::StructCreateOp, ac::TableCreateOp>(value.getDefiningOp()))
        return std::nullopt;
    if (auto record = readableRecordChoice(value)) return record;
    auto create = readableSource(value).getDefiningOp<ac::TableCreateOp>();
    if (!create || create->getNumOperands() == 0) return std::nullopt;
    auto element = cast<ac::TableType>(value.getType()).getElementType();
    std::optional<ReadableAggregateChoice> choice;
    for (auto [index, input] : llvm::enumerate(create->getOperands())) {
        input = readableSource(input);
        if (!readablePrivateValue(input)) return std::nullopt;
        auto part = readableRecordChoice(input);
        if (!part && isa<ac::BitsType, ac::EnumType>(element)) {
            Value selected = readableChoiceCarrier(input);
            if (auto select = selected.getDefiningOp<ac::BitsSelectOp>()) {
                Value a = readableChoiceCarrier(select->getOperand(1)), b = readableChoiceCarrier(select->getOperand(2));
                if (a.getType() == element && b.getType() == element &&
                    readablePrivateValue(selected))
                    part = ReadableAggregateChoice{readableSource(select->getOperand(0)), a, b};
            }
        }
        if (!part) return std::nullopt;
        auto left = part->onTrue.getDefiningOp<ac::TableGetOp>();
        auto right = part->onFalse.getDefiningOp<ac::TableGetOp>();
        if (!left || !right || readableConstantIndex(left.getIndex()) != index ||
            readableConstantIndex(right.getIndex()) != index ||
            left.getInput().getType() != value.getType() ||
            right.getInput().getType() != value.getType()) return std::nullopt;
        ReadableAggregateChoice table{part->condition,
            readableSource(left.getInput()), readableSource(right.getInput())};
        if (!choice) choice = table;
        else if (choice->condition != table.condition || choice->onTrue != table.onTrue ||
                 choice->onFalse != table.onFalse) return std::nullopt;
    }
    return choice;
}

FailureOr<std::string> emitReadableAggregateChoice(
    Value value, const ReadableAggregateChoice &choice) {
    auto type = context.rtlType(value.getType(), value.getDefiningOp());
    if (failed(type)) return failure();
    auto name = sourceNetName(value);
    names.try_emplace(value, name);
    readableDeclaration("wire", *type, name);
    // Only a whole typed vector choice accepts a packed replication here.
    // Lane consumers use scalar projection instead, preserving struct/rank
    // indexing and the existing packed element order.
    auto operand = [&](Value input) -> FailureOr<std::string> {
        if (isa<ac::TableType>(value.getType())) {
            if (auto scalar = readableBroadcast(input)) {
                auto shape = readableTableShape(input.getType(), definition);
                auto text = net(scalar);
                if (shape && succeeded(text)) {
                    uint64_t count = 1;
                    for (auto size : *shape) {
                        if (size > std::numeric_limits<uint64_t>::max() / count) return failure();
                        count *= size;
                    }
                    return "{" + std::to_string(count) + "{" + *text + "}}";
                }
            }
        }
        return net(input);
    };
    auto condition = net(choice.condition), onTrue = operand(choice.onTrue), onFalse = operand(choice.onFalse);
    if (failed(condition) || failed(onTrue) || failed(onFalse)) return failure();
    readableAssignment(name, *condition + " ? " + *onTrue + " : " + *onFalse);
    return name;
}
