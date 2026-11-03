// A read-only presentation of one-bit control DAGs. This is not an IR pass:
// surviving producers keep their SSA identity and net() memoization. Each
// projection below is checked over the Cartesian product of the operands'
// conservative four-state domains (at most 4^3 cases per operation).
struct ReadableControlView {
    Value value;
    unsigned domain = 15;
    unsigned literal = 4;
};

static unsigned readableControlResult(StringRef operation, ArrayRef<unsigned> inputs) {
    unsigned a = inputs[0], b = inputs.size() > 1 ? inputs[1] : 0;
    if (operation == "not") return a < 2 ? 1 - a : 2;
    if (operation == "and") return a == 0 || b == 0 ? 0 : a == 1 && b == 1 ? 1 : 2;
    if (operation == "or") return a == 1 || b == 1 ? 1 : a == 0 && b == 0 ? 0 : 2;
    if (operation == "xor") return a < 2 && b < 2 ? a ^ b : 2;
    if (operation == "case_eq") return a == b;
    if (operation == "eq" || operation == "ne")
        return a < 2 && b < 2 ? unsigned((a == b) == (operation == "eq")) : 2;
    if (operation == "require")
        return b == 1 ? a : b == 0 ? 1 : a == 1 ? 1 : 2;
    unsigned c = inputs[2];
    return a == 1 ? b : a == 0 ? c : b == c ? b : 2;
}

ReadableControlView readableControlView(Value raw) {
    Value value = readableSource(raw);
    auto view = presentation.view(value);
    ReadableControlView result{view.value, view.domain, view.literal};
    readableControlViews[value] = result;
    return result;
}

FailureOr<std::string> readableControlProjection(Value value) {
    if (readableWidth(value) != 1 || !ac::sourceValueNames(value).empty()) return failure();
    auto view = readableControlView(value);
    if (view.literal < 4) return std::string("1'b") + "01xz"[view.literal];
    if (view.value != readableSource(value)) return net(view.value);
    return failure();
}

void initializeReadableControlUses() {
    if (failed(presentation.census(presentationRoots()))) return;
    for (Value value : readableOrderedValues())
        if (auto node = presentation.find(value); node && node->oneBit)
            readableControlUses[node->value] = node->uses;
}

bool readablePrivateControl(Value value) {
    value = readableSource(value);
    return ac::sourceValueNames(value).empty() && !ownershipOpaque.contains(value) &&
        readableWidth(value) == 1 && readableControlUses.lookup(value) == 1;
}

// Requirements are a conjunction, with conditional requirements represented by
// a known Boolean selector and a true alternative. Only private nodes are
// opened. Shared nontrivial predicates remain one wire used by every consumer.
struct ReadableRequirementClause {
    SmallVector<Value> guards;
    Value term;
};

void readableRequirement(Value value, SmallVector<Value> guards,
                         SmallVector<ReadableRequirementClause> &clauses, unsigned depth = 0) {
    auto view = readableControlView(value);
    if (view.literal == 1) return;
    value = view.value;
    auto *operation = value ? value.getDefiningOp() : nullptr;
    if (depth < 32 && value && readablePrivateControl(value)) {
        if (auto binary = dyn_cast_or_null<ac::BitsBinaryOp>(operation))
            if (binary.getOpcode() == "and" && view.domain <= 3) {
                readableRequirement(binary.getLhs(), guards, clauses, depth + 1);
                readableRequirement(binary.getRhs(), guards, clauses, depth + 1);
                return;
            }
        Value condition, requirement;
        if (auto select = dyn_cast_or_null<ac::BitsSelectOp>(operation))
            if (readableControlView(select->getOperand(2)).literal == 1) {
                condition = select->getOperand(0); requirement = select->getOperand(1);
            }
        if (auto require = dyn_cast_or_null<ac::ValueRequireOp>(operation)) {
            condition = require->getOperand(2); requirement = require->getOperand(1);
        }
        if (condition && readableControlView(condition).domain <= 3) {
            guards.push_back(condition);
            readableRequirement(requirement, std::move(guards), clauses, depth + 1);
            return;
        }
    }
    clauses.push_back({std::move(guards), value});
}

unsigned readableRequirementSize(Value value, bool root = false, unsigned depth = 0) {
    auto view = readableControlView(value);
    if (depth > 32 || view.literal < 4 || !view.value || (!root && !readablePrivateControl(view.value))) return 1;
    auto *operation = view.value.getDefiningOp();
    bool open = isa_and_nonnull<ac::BitsSelectOp, ac::ValueRequireOp>(operation);
    if (auto binary = dyn_cast_or_null<ac::BitsBinaryOp>(operation)) open = binary.getOpcode() == "and";
    if (!open || view.domain > 3) return 1;
    auto inputs = operation->getOperands();
    if (isa<ac::ValueRequireOp>(operation)) inputs = inputs.drop_front();
    unsigned size = 1;
    for (Value input : inputs) {
        size += readableRequirementSize(input, false, depth + 1);
        if (size > 8) break;
    }
    return size;
}

FailureOr<std::string> readableRequirementBlock(Value value) {
    auto *operation = value.getDefiningOp();
    auto binary = dyn_cast_or_null<ac::BitsBinaryOp>(operation);
    if (!binary || binary.getOpcode() != "and" || !ac::sourceValueNames(value).empty() ||
        readableControlView(value).domain > 3 || readableRequirementSize(value, true) <= 8)
        return failure();
    auto name = sourceNetName(value);
    names.try_emplace(value, name);
    SmallVector<ReadableRequirementClause> clauses;
    // Open the root even if shared, exactly once, after publishing its name.
    readableRequirement(binary.getLhs(), {}, clauses);
    readableRequirement(binary.getRhs(), {}, clauses);
    std::string body;
    SmallVector<Value> path;
    bool initialized = false;
    for (const auto &clause : clauses) {
        unsigned common = 0;
        while (common < path.size() && common < clause.guards.size() &&
               readableSource(path[common]) == readableSource(clause.guards[common])) ++common;
        while (path.size() > common) {
            path.pop_back();
            body += std::string(4 + 4 * path.size(), ' ') + "end\n";
        }
        if (!initialized && !clause.guards.empty()) {
            body += "    " + name + " = 1'b1;\n";
            initialized = true;
        }
        while (path.size() < clause.guards.size()) {
            auto condition = clause.guards[path.size()];
            auto guard = net(condition);
            if (failed(guard)) return failure();
            body += std::string(4 + 4 * path.size(), ' ') + "if (" + *guard + ") begin\n";
            path.push_back(condition);
        }
        ReadableFacts facts;
        for (Value guard : path) readableAssume(guard, true, facts);
        auto term = readableConditionalTerm(clause.term, facts);
        if (failed(term)) return failure();
        body += std::string(4 + 4 * path.size(), ' ') + name + " = " +
            (initialized ? name + " && " : "") + *term + ";\n";
        initialized = true;
    }
    while (!path.empty()) {
        path.pop_back();
        body += std::string(4 + 4 * path.size(), ' ') + "end\n";
    }
    readableDeclaration("", "logic", name);
    out << "  always_comb begin\n" << body << "  end\n";
    return name;
}
