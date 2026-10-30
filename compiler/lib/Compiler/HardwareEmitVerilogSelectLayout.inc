// Presentation over verified SSA. No Boolean rewrite or state inference.
struct ReadableSelectLayout {
    Value value;
    Value boundary;
    ac::BitsSelectOp select;
    std::unique_ptr<ReadableSelectLayout> yes, no;
    bool wireBoundary = false;
    std::string condition, text;
};

std::unique_ptr<ReadableSelectLayout> planReadableSelect(
        Value value, unsigned width, unsigned &remaining, bool root = false) {
    auto node = std::make_unique<ReadableSelectLayout>();
    node->value = value;
    Value source = readableSource(value);
    llvm::DenseSet<Value> visited;
    while (visited.insert(source).second) {
        if (ownershipOpaque.contains(source) ||
            (!root && (!ac::sourceValueNames(value).empty() ||
                       !ac::sourceValueNames(source).empty())))
            return node;
        Value operand = readableEnumOperand(source);
        if (operand == source) break;
        source = readableSource(operand);
    }
    auto select = source.getDefiningOp<ac::BitsSelectOp>();
    if (!select || readableWidth(source) != width) return node;
    // Preserve the established known-condition facts/structured simplifier,
    // as well as producers which an earlier rendering decision retained.
    if (!root && (names.contains(source) || readableRetained.contains(source) ||
                  readableKnownBit(select->getOperand(0))))
        return node;
    llvm::DenseSet<Value> uses;
    if (!root && readableUseCount(source, uses) != 1) return node;
    if (!remaining) {
        node->wireBoundary = true;
        node->boundary = source;
        return node;
    }
    --remaining;
    node->select = select;
    node->yes = planReadableSelect(select->getOperand(1), width, remaining);
    node->no = planReadableSelect(select->getOperand(2), width, remaining);
    return node;
}

LogicalResult prepareReadableSelect(ReadableSelectLayout &node) {
    if (!node.select) {
        if (node.wireBoundary) readableRetained.insert(node.boundary);
        auto rendered = net(node.value);
        if (failed(rendered)) return failure();
        node.text = *rendered;
        return success();
    }
    auto condition = net(node.select->getOperand(0));
    if (failed(condition) || failed(prepareReadableSelect(*node.yes)) ||
        failed(prepareReadableSelect(*node.no)))
        return failure();
    node.condition = *condition;
    if (!node.yes->select && !node.no->select &&
        !StringRef(*condition).contains('\n') && !node.yes->text.empty() &&
        !node.no->text.empty() && !StringRef(node.yes->text).contains('\n') &&
        !StringRef(node.no->text).contains('\n')) {
        auto compact = "(" + *condition + " ? " + node.yes->text + " : " + node.no->text + ")";
        if (compact.size() <= 96) node.text = std::move(compact);
    }
    return success();
}

std::string renderReadableSelect(const ReadableSelectLayout &node, unsigned indent) {
    std::string padding(indent, ' ');
    if (!node.select) return padding + node.text;
    const auto *current = &node;
    std::string text;
    while (current->select) {
        auto &yes = *current->yes;
        text += padding + current->condition + " ? ";
        if (!yes.text.empty()) text += yes.text;
        else text += "(\n" + renderReadableSelect(yes, indent + 4) + "\n" + padding + ")";
        text += " :\n";
        current = current->no.get();
    }
    return text + padding + current->text;
}

FailureOr<std::string> readableSelectExpression(Value value) {
    auto select = value.getDefiningOp<ac::BitsSelectOp>();
    auto width = readableWidth(value);
    // The established known-condition structured printer keeps its behavior.
    if (!select || !width || ownershipOpaque.contains(value) ||
        readableKnownBit(select->getOperand(0)))
        return failure();
    unsigned remaining = 32;
    auto plan = planReadableSelect(value, *width, remaining, true);
    if (!plan->select) return failure();
    llvm::DenseSet<Value> uses;
    bool materialize = readableRetained.contains(value) ||
        !ac::sourceValueNames(value).empty() || readableUseCount(value, uses) != 1;
    std::string name;
    if (materialize) {
        name = sourceNetName(value, "selected_value");
        names.try_emplace(value, name);
    }
    if (failed(prepareReadableSelect(*plan))) return failure();
    // Every expanded arm has the same verified unsigned width. Leaf rendering
    // retains its own arithmetic/resize bounds; one outer size seals context.
    auto expression = std::to_string(*width) + "'(" +
        (plan->text.empty() ? "\n" + renderReadableSelect(*plan, 4) + "\n  " : plan->text) + ")";
    if (materialize) {
        auto type = context.rtlType(value.getType(), select);
        if (failed(type)) return failure();
        readableDeclaration("wire", *type, name);
        readableAssignment(name, expression);
        return name;
    }
    names.try_emplace(value, expression);
    return expression;
}
