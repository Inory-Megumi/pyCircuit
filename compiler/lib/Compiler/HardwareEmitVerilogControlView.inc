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

ReadableControlView readableControlView(Value raw, unsigned depth = 0) {
    Value value = readableSource(raw);
    if (auto found = readableControlViews.find(value); found != readableControlViews.end()) return found->second;
    ReadableControlView result{value};
    if (depth > 128 || readableWidth(value) != 1 || ownershipOpaque.contains(value)) return result;
    auto publish = [&] {
        readableControlViews.try_emplace(value, result);
        return result;
    };
    if (auto literal = readableLiteral(value)) {
        for (unsigned bit = 0; bit < 4; ++bit)
            if (*literal == std::string("1'b") + "01xz"[bit] ||
                (bit < 2 && *literal == std::string("1'd") + "01"[bit])) {
                result.domain = 1u << bit;
                result.literal = bit;
                return publish();
            }
    }
    auto *operation = value.getDefiningOp();
    if (!operation) return publish();
    StringRef opcode;
    if (auto binary = dyn_cast<ac::BitsBinaryOp>(operation))
        if (llvm::is_contained(ArrayRef<StringRef>{"and", "or", "xor"}, binary.getOpcode())) opcode = binary.getOpcode();
    if (auto unary = dyn_cast<ac::BitsUnaryOp>(operation))
        if (unary.getOpcode() == "not") opcode = "not";
    if (auto compare = dyn_cast<ac::BitsCompareOp>(operation)) {
        result.domain = compare.getPredicate() == "case_eq" ? 3 : 7;
        if (llvm::is_contained(ArrayRef<StringRef>{"eq", "ne", "case_eq"}, compare.getPredicate())) opcode = compare.getPredicate();
    }
    if (isa<ac::BitsSelectOp>(operation)) opcode = "select";
    if (isa<ac::ValueRequireOp>(operation)) opcode = "require";
    auto operands = operation->getOperands();
    if (opcode == "require") operands = operands.drop_front();
    if (opcode.empty() || operands.empty() || operands.size() > 3 ||
        !llvm::all_of(operands, [&](Value input) { return readableWidth(input) == 1; })) return publish();
    SmallVector<ReadableControlView> inputs;
    for (Value input : operands) inputs.push_back(readableControlView(input, depth + 1));
    unsigned domain = 0, projections = (1u << inputs.size()) - 1;
    for (unsigned tuple = 0; tuple < (1u << (2 * inputs.size())); ++tuple) {
        SmallVector<unsigned, 3> bits;
        bool possible = true;
        for (auto [index, input] : llvm::enumerate(inputs)) {
            unsigned bit = (tuple >> (2 * index)) & 3;
            bits.push_back(bit);
            possible &= bool(input.domain & (1u << bit));
            for (unsigned earlier = 0; earlier < index; ++earlier)
                if (input.literal == 4 && inputs[earlier].literal == 4 && input.value == inputs[earlier].value)
                    possible &= bit == bits[earlier];
        }
        if (!possible) continue;
        unsigned bit = readableControlResult(opcode, bits);
        domain |= 1u << bit;
        for (unsigned index = 0; index < inputs.size(); ++index)
            if (bit != bits[index]) projections &= ~(1u << index);
    }
    result.domain = domain;
    // Authored identities remain visible even when their payload is constant.
    if (ac::sourceValueNames(value).empty()) {
        if (llvm::isPowerOf2_32(domain)) {
            result.literal = llvm::Log2_32(domain);
        } else {
            for (unsigned index = 0; index < inputs.size(); ++index)
                if (projections & (1u << index)) { result = inputs[index]; break; }
        }
    }
    return publish();
}

FailureOr<std::string> readableControlProjection(Value value) {
    if (readableWidth(value) != 1 || !ac::sourceValueNames(value).empty()) return failure();
    auto view = readableControlView(value);
    if (view.literal < 4) return std::string("1'b") + "01xz"[view.literal];
    if (view.value != readableSource(value)) return net(view.value);
    return failure();
}

void initializeReadableControlUses() {
    // Count the actual presentation edges from outputs, primitive/module pins
    // and retained checks. Verifier witnesses are not runtime consumers. Walk
    // each producer once, but count every incoming edge before that cut.
    llvm::DenseSet<Value> visited;
    std::function<void(Value)> visit = [&](Value raw) {
        Value value = readableSource(raw);
        if (readableWidth(value) == 1) {
            auto view = readableControlView(value);
            if (view.literal < 4) return;
            value = view.value;
            ++readableControlUses[value];
        }
        if (!visited.insert(value).second || ownershipOpaque.contains(value)) return;
        auto *operation = value.getDefiningOp();
        if (!operation || isa<ac::InstanceOp, ac::CollectionOp>(operation)) return;
        auto operands = operation->getOperands();
        if (isa<ac::ValueRequireOp>(operation)) operands = operands.drop_front();
        for (Value input : operands) visit(input);
        for (Region &region : operation->getRegions())
            for (Block &block : region)
                if (!block.empty())
                    if (auto yield = dyn_cast<ac::YieldOp>(block.back()))
                        for (Value input : yield.getValues()) visit(input);
    };
    for (Value value : cast<ac::YieldOp>(definition.getBody().front().back()).getValues()) visit(value);
    if (ownership)
        for (const auto &port : ownership->exports) visit(port.value);
    for (Operation &operation : definition.getBody().front())
        if (isa<ac::InstanceOp, ac::CollectionOp>(operation))
            for (Value input : operation.getOperands()) visit(input);
    if (context.hasPhysicalChecks()) {
        for (const auto &binding : context.sourceChecks().bindings)
            if (binding.definition == definition) { visit(binding.condition); visit(binding.path); }
        for (const auto &control : context.physicalProjection().controls)
            if (control.definition == definition) { visit(control.raw); visit(control.reached); }
    }
}

bool readablePrivateControl(Value value) {
    value = readableSource(value);
    return ac::sourceValueNames(value).empty() && !ownershipOpaque.contains(value) &&
        readableWidth(value) == 1 && readableControlUses.lookup(value) == 1;
}

std::optional<std::string> readableControlAtomStem(Value value, unsigned depth = 0) {
    value = readableSource(value);
    if (depth > 5) return std::nullopt;
    if (auto function = readableFunction(value); function && function->leaf && function->leaf != value) {
        std::string suffix;
        if (function->values == std::array<unsigned, 4>{0, 1, 0, 0}) suffix = "_active";
        if (function->values == std::array<unsigned, 4>{1, 0, 0, 0}) suffix = "_zero";
        if (function->values == std::array<unsigned, 4>{1, 1, 0, 0}) suffix = "_known";
        if (!suffix.empty())
            if (auto anchor = readableNameAnchor(function->leaf)) return *anchor + suffix;
    }
    if (auto anchor = readableNameAnchor(value)) return anchor;
    if (auto binary = value.getDefiningOp<ac::BitsBinaryOp>(); binary && binary.getOpcode() == "and") {
        auto left = readableControlAtomStem(binary.getLhs(), depth + 1), right = readableControlAtomStem(binary.getRhs(), depth + 1);
        if (left && right && left->size() + right->size() < 80) return *left + "_and_" + *right;
    }
    if (auto unary = value.getDefiningOp<ac::BitsUnaryOp>(); unary && unary.getOpcode() == "not")
        if (auto input = readableControlAtomStem(unary.getOperand(), depth + 1)) return "not_" + *input;
    return std::nullopt;
}

std::optional<std::string> readableControlRelationStem(Value value, unsigned depth = 0) {
    value = readableSource(value);
    if (depth > 6 || readableWidth(value) != 1) return std::nullopt;
    if (auto atom = readableControlAtomStem(value)) return atom;
    auto *operation = value.getDefiningOp();
    if (!operation) return std::nullopt;
    if (auto compare = dyn_cast<ac::BitsCompareOp>(operation); compare && compare.getPredicate() == "case_eq") {
        auto bit = readableBit(compare.getRhs());
        if (bit)
            if (auto input = readableControlRelationStem(compare.getLhs(), depth + 1)) return *input + (*bit ? "_active" : "_zero");
    }
    Value condition, term;
    if (auto select = dyn_cast<ac::BitsSelectOp>(operation))
        if (readableControlView(select->getOperand(2)).literal == 1) {
            condition = select->getOperand(0); term = select->getOperand(1);
        }
    if (auto require = dyn_cast<ac::ValueRequireOp>(operation)) {
        condition = require->getOperand(2); term = require->getOperand(1);
    }
    if (condition) {
        auto guard = readableControlRelationStem(condition, depth + 1);
        auto requirement = readableControlRelationStem(term, depth + 1);
        if (guard && requirement && guard->size() + requirement->size() < 112)
            return *requirement + "_when_" + *guard;
    }
    if (auto binary = dyn_cast<ac::BitsBinaryOp>(operation))
        if (binary.getOpcode() == "and" || binary.getOpcode() == "or") {
            auto left = readableControlRelationStem(binary.getLhs(), depth + 1), right = readableControlRelationStem(binary.getRhs(), depth + 1);
            if (left && right && left->size() + right->size() < 112)
                return *left + (binary.getOpcode() == "and" ? "_and_" : "_or_") + *right;
        }
    return std::nullopt;
}

std::optional<std::string> readableGuardedControlStem(Value value) {
    if (readableWidth(value) != 1) return std::nullopt;
    auto *operation = value.getDefiningOp();
    Value condition, term;
    if (auto select = dyn_cast_or_null<ac::BitsSelectOp>(operation))
        if (readableControlView(select->getOperand(2)).literal == 1) {
            condition = select->getOperand(0); term = select->getOperand(1);
        }
    if (auto require = dyn_cast_or_null<ac::ValueRequireOp>(operation)) {
        condition = require->getOperand(2); term = require->getOperand(1);
    }
    if (!condition || readableControlView(condition).domain > 3) return std::nullopt;
    auto guard = readableControlAtomStem(condition), requirement = readableControlAtomStem(term);
    if (!guard || !requirement) return std::nullopt;
    if (guard->size() + requirement->size() > 104) return *requirement + "_guarded";
    return *requirement + "_when_" + *guard;
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
