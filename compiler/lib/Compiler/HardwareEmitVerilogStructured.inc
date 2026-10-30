// Exact one-input four-state functions expose Boolean normalization shells.
// Unsupported/multi-input functions keep their original verified DAG.
struct ReadableBitFunction {
    Value leaf;
    std::array<unsigned, 4> values;
};

std::optional<ReadableBitFunction> readableFunction(Value value, unsigned &budget) {
    if (!budget || readableWidth(value) != 1)
        return std::nullopt;
    --budget;
    value = readableSource(value);
    if (ownershipOpaque.contains(value)) return ReadableBitFunction{value, {0, 1, 2, 3}};
    if (auto literal = readableLiteral(value)) {
        unsigned bit = 4;
        if (*literal == "1'd0" || *literal == "1'b0") bit = 0;
        if (*literal == "1'd1" || *literal == "1'b1") bit = 1;
        if (*literal == "1'bx") bit = 2;
        if (*literal == "1'bz") bit = 3;
        if (bit < 4)
            return ReadableBitFunction{{}, {bit, bit, bit, bit}};
    }
    auto *op = value.getDefiningOp();
    auto binary = dyn_cast_or_null<ac::BitsBinaryOp>(op);
    auto compare = dyn_cast_or_null<ac::BitsCompareOp>(op);
    auto unary = dyn_cast_or_null<ac::BitsUnaryOp>(op);
    bool supported = (unary && unary.getOpcode() == "not") ||
        isa_and_nonnull<ac::BitsSelectOp,
                                     ac::ValueRequireOp>(op) ||
        (binary && (binary.getOpcode() == "and" || binary.getOpcode() == "or" ||
                    binary.getOpcode() == "xor")) ||
        (compare && (compare.getPredicate() == "eq" || compare.getPredicate() == "ne" ||
                     compare.getPredicate() == "case_eq"));
    if (!supported)
        return ReadableBitFunction{value, {0, 1, 2, 3}};
    SmallVector<ReadableBitFunction> inputs;
    Value leaf;
    auto operands = op->getOperands();
    if (isa<ac::ValueRequireOp>(op))
        operands = operands.drop_front();
    for (Value input : operands) {
        auto function = readableFunction(input, budget);
        if (!function || (leaf && function->leaf && leaf != function->leaf))
            return std::nullopt;
        if (function->leaf) leaf = function->leaf;
        inputs.push_back(*function);
    }
    ReadableBitFunction result{leaf, {}};
    for (unsigned i = 0; i < 4; ++i) {
        unsigned a = inputs[0].values[i];
        unsigned b = inputs.size() > 1 ? inputs[1].values[i] : 0;
        unsigned bit = 2;
        if (isa<ac::BitsUnaryOp>(op)) bit = a < 2 ? 1 - a : 2;
        if (binary) {
            if (binary.getOpcode() == "and") bit = a == 0 || b == 0 ? 0 : a == 1 && b == 1 ? 1 : 2;
            if (binary.getOpcode() == "or") bit = a == 1 || b == 1 ? 1 : a == 0 && b == 0 ? 0 : 2;
            if (binary.getOpcode() == "xor") bit = a < 2 && b < 2 ? a ^ b : 2;
        }
        if (compare) {
            if (compare.getPredicate() == "case_eq") bit = a == b;
            else if (a < 2 && b < 2) bit = (a == b) == (compare.getPredicate() == "eq");
        }
        if (isa<ac::BitsSelectOp>(op)) {
            unsigned c = inputs[2].values[i];
            bit = a == 1 ? b : a == 0 ? c : b == c ? b : 2;
        }
        if (isa<ac::ValueRequireOp>(op))
            bit = b == 1 ? a : b == 0 ? 1 : a == 1 ? 1 : 2;
        result.values[i] = bit;
    }
    return result;
}

std::optional<ReadableBitFunction> readableFunction(Value value) {
    unsigned budget = 256;
    return readableFunction(value, budget);
}

bool readableKnownBit(Value value, unsigned depth = 0) {
    if (ownershipOpaque.contains(readableSource(value))) return false;
    if (depth > 32 || readableWidth(value) != 1)
        return false;
    if (readableControlView(value).domain <= 3) return true;
    if (auto function = readableFunction(value))
        if (llvm::all_of(function->values, [](unsigned bit) { return bit < 2; }))
            return true;
    value = readableSource(value);
    auto *op = value.getDefiningOp();
    if (!op) return false;
    if (auto compare = dyn_cast<ac::BitsCompareOp>(op))
        if (compare.getPredicate() == "case_eq") return true;
    bool binaryBoolean = false;
    if (auto binary = dyn_cast<ac::BitsBinaryOp>(op))
        binaryBoolean = binary.getOpcode() == "and" || binary.getOpcode() == "or" || binary.getOpcode() == "xor";
    auto unary = dyn_cast<ac::BitsUnaryOp>(op);
    if (binaryBoolean || (unary && unary.getOpcode() == "not") ||
        isa<ac::BitsSelectOp, ac::ValueRequireOp>(op)) {
        auto operands = op->getOperands();
        if (isa<ac::ValueRequireOp>(op)) operands = operands.drop_front();
        return llvm::all_of(operands, [&](Value input) { return readableKnownBit(input, depth + 1); });
    }
    return false;
}

FailureOr<std::string> readableCanonicalBit(Value value) {
    auto function = readableFunction(value);
    if (!function) return failure();
    auto bits = function->values;
    if (llvm::all_of(bits, [&](unsigned bit) { return bit == bits[0]; }))
        return std::string("1'b") + "01xz"[bits[0]];
    if (!function->leaf || function->leaf == readableSource(value)) return failure();
    if (bits == std::array<unsigned, 4>{0, 1, 2, 3}) return net(function->leaf);
    std::string suffix, expression;
    if (bits == std::array<unsigned, 4>{0, 1, 0, 0}) suffix = "active";
    if (bits == std::array<unsigned, 4>{1, 0, 0, 0}) suffix = "zero";
    if (bits == std::array<unsigned, 4>{1, 1, 0, 0}) suffix = "known";
    if (suffix.empty()) return failure();
    unsigned key = 0;
    for (unsigned i = 0; i < 4; ++i) key |= bits[i] << (2 * i);
    auto identity = std::make_pair(function->leaf, key);
    if (auto found = readableBitNames.find(identity); found != readableBitNames.end())
        return found->second;
    auto leaf = net(function->leaf);
    if (failed(leaf)) return failure();
    if (suffix == "known") expression = "((" + *leaf + " === 1'b0) || (" + *leaf + " === 1'b1))";
    else expression = "(" + *leaf + (suffix == "active" ? " === 1'b1)" : " === 1'b0)");
    auto anchor = readableNameAnchor(function->leaf);
    auto name = readableDerivedName((anchor ? *anchor : readablePurposeStem(function->leaf)) + "_" + suffix);
    readableDeclaration("wire", "", name, expression);
    readableBitNames.try_emplace(identity, name);
    return name;
}

struct ReadableFacts : llvm::DenseMap<Value, bool> {
    ReadableFacts() : llvm::DenseMap<Value, bool>() {}
    SmallVector<std::pair<Value, bool>> assumptions;
};

struct ReadableFactProof {
    Value selector;
    unsigned domain;
    SmallVector<std::pair<Value, bool>> facts, assumptions;
};

FailureOr<std::string> readableAssignment(Value value) {
    return net(value);
}

std::optional<bool> readableFact(Value value, const ReadableFacts &facts) {
    if (auto known = readableBit(value)) return known;
    auto function = readableFunction(value);
    if (function && function->leaf) {
        auto found = facts.find(function->leaf);
        if (found != facts.end()) {
            unsigned bit = function->values[found->second ? 1 : 0];
            if (bit < 2) return bit == 1;
        }
    }
    unsigned budget = 256;
    unsigned domain = readableFactDomain(value, facts, budget);
    if (domain == 1 || domain == 2) {
        ReadableFactProof proof{readableSource(value), domain, {}, facts.assumptions};
        for (auto [leaf, truth] : facts) proof.facts.emplace_back(leaf, truth);
        readableFactProofs.push_back(std::move(proof));
    }
    return domain == 1 ? std::optional<bool>(false) : domain == 2 ? std::optional<bool>(true) : std::nullopt;
}

unsigned readableFactDomain(Value value, const ReadableFacts &facts, unsigned &budget) {
    value = readableSource(value);
    if (!budget || ownershipOpaque.contains(value) || readableWidth(value) != 1) return 15;
    --budget;
    if (auto found = facts.find(value); found != facts.end()) return found->second ? 2 : 1;
    if (auto function = readableFunction(value); function && function->leaf)
        if (auto found = facts.find(function->leaf); found != facts.end())
            return 1u << function->values[found->second ? 1 : 0];
    auto view = readableControlView(value);
    if (view.literal < 4) return 1u << view.literal;
    if (view.value != value) return readableFactDomain(view.value, facts, budget);
    auto *operation = value.getDefiningOp();
    if (!operation) return view.domain;
    StringRef opcode;
    if (auto binary = dyn_cast<ac::BitsBinaryOp>(operation))
        if (llvm::is_contained(ArrayRef<StringRef>{"and", "or", "xor"}, binary.getOpcode())) opcode = binary.getOpcode();
    if (auto unary = dyn_cast<ac::BitsUnaryOp>(operation); unary && unary.getOpcode() == "not") opcode = "not";
    if (auto compare = dyn_cast<ac::BitsCompareOp>(operation))
        if (llvm::is_contained(ArrayRef<StringRef>{"eq", "ne", "case_eq"}, compare.getPredicate())) opcode = compare.getPredicate();
    if (isa<ac::BitsSelectOp>(operation)) opcode = "select";
    if (isa<ac::ValueRequireOp>(operation)) opcode = "require";
    auto inputs = operation->getOperands();
    if (opcode == "require") inputs = inputs.drop_front();
    if (opcode.empty() || inputs.empty() || inputs.size() > 3 ||
        !llvm::all_of(inputs, [&](Value input) { return readableWidth(input) == 1; })) return view.domain;
    SmallVector<unsigned> domains;
    for (Value input : inputs) domains.push_back(readableFactDomain(input, facts, budget));
    unsigned result = 0;
    for (unsigned tuple = 0; tuple < (1u << (2 * inputs.size())); ++tuple) {
        SmallVector<unsigned> bits;
        bool possible = true;
        for (unsigned index = 0; index < inputs.size(); ++index) {
            unsigned bit = (tuple >> (2 * index)) & 3;
            bits.push_back(bit);
            possible &= bool(domains[index] & (1u << bit));
        }
        if (possible) result |= 1u << readableControlResult(opcode, bits);
    }
    return result;
}

void readableAssume(Value value, bool truth, ReadableFacts &facts, unsigned depth = 0) {
    if (!depth) facts.assumptions.emplace_back(value, truth);
    if (ownershipOpaque.contains(readableSource(value))) return;
    if (depth > 32) return;
    if (auto function = readableFunction(value)) {
        if (function->leaf && truth && function->values == std::array<unsigned, 4>{0, 1, 0, 0})
            facts[function->leaf] = true;
        if (function->leaf && truth && function->values == std::array<unsigned, 4>{1, 0, 0, 0})
            facts[function->leaf] = false;
    }
    value = readableSource(value);
    if (truth)
        if (auto compare = value.getDefiningOp<ac::BitsCompareOp>(); compare && compare.getPredicate() == "case_eq") {
            if (auto bit = readableBit(compare.getRhs())) facts[readableSource(compare.getLhs())] = *bit;
            else if (auto bit = readableBit(compare.getLhs())) facts[readableSource(compare.getRhs())] = *bit;
        }
    if (auto binary = value.getDefiningOp<ac::BitsBinaryOp>())
        if ((truth && binary.getOpcode() == "and") || (!truth && binary.getOpcode() == "or")) {
            readableAssume(binary.getLhs(), truth, facts, depth + 1);
            readableAssume(binary.getRhs(), truth, facts, depth + 1);
        }
    if (auto unary = value.getDefiningOp<ac::BitsUnaryOp>())
        if (unary.getOpcode() == "not" && readableKnownBit(unary.getOperand()))
            readableAssume(unary.getOperand(), !truth, facts, depth + 1);
}

Value readableConditionedValue(Value value, const ReadableFacts &facts, unsigned depth = 0) {
    value = readableSource(value);
    if (depth > 32 || !readablePrivateControl(value)) return value;
    auto select = value.getDefiningOp<ac::BitsSelectOp>();
    if (!select) return value;
    auto truth = readableFact(select->getOperand(0), facts);
    return truth ? readableConditionedValue(select->getOperand(*truth ? 1 : 2), facts, depth + 1) : value;
}

FailureOr<std::string> readableConditionalTerm(Value value, const ReadableFacts &facts) {
    value = readableSource(value);
    if (readablePrivateControl(value))
        if (auto compare = value.getDefiningOp<ac::BitsCompareOp>(); compare && compare.getPredicate() == "case_eq") {
            Value left = readableConditionedValue(compare.getLhs(), facts);
            Value right = readableConditionedValue(compare.getRhs(), facts);
            if (left != readableSource(compare.getLhs()) || right != readableSource(compare.getRhs())) {
                auto a = net(left), b = net(right);
                if (failed(a) || failed(b)) return failure();
                return "(" + *a + " === " + *b + ")";
            }
        }
    return net(value);
}

FailureOr<std::string> readableGuardedRequirement(Value value) {
    if (readableWidth(value) != 1 || !ac::sourceValueNames(value).empty()) return failure();
    auto *operation = value.getDefiningOp();
    Value condition, term;
    if (auto select = dyn_cast_or_null<ac::BitsSelectOp>(operation))
        if (readableControlView(select->getOperand(2)).literal == 1) {
            condition = select->getOperand(0); term = select->getOperand(1);
        }
    if (auto require = dyn_cast_or_null<ac::ValueRequireOp>(operation)) {
        condition = require->getOperand(2); term = require->getOperand(1);
    }
    if (!condition || readableControlView(condition).domain > 3 || !readablePrivateControl(term)) return failure();
    auto compare = readableSource(term).getDefiningOp<ac::BitsCompareOp>();
    if (!compare || compare.getPredicate() != "case_eq") return failure();
    ReadableFacts facts;
    readableAssume(condition, true, facts);
    Value left = readableConditionedValue(compare.getLhs(), facts);
    Value right = readableConditionedValue(compare.getRhs(), facts);
    if (left == readableSource(compare.getLhs()) && right == readableSource(compare.getRhs())) return failure();
    auto anchor = readableNameAnchor(left);
    auto name = sourceNetName(value, readableGeneratedStem((anchor ? *anchor : readablePurposeStem(value)) + "_check"));
    names.try_emplace(value, name);
    auto guard = net(condition), requirement = readableConditionalTerm(term, facts);
    if (failed(guard) || failed(requirement)) return failure();
    readableDeclaration("wire", "logic [0:0]", name);
    readableAssignment(name, *guard + " ? " + *requirement + " : 1'b1", false);
    return name;
}

LogicalResult readableMuxBody(Value value, StringRef target, ReadableFacts facts,
                              std::string &body, unsigned indent, unsigned depth = 0) {
    value = readableSource(value);
    auto select = ownershipOpaque.contains(value) ? ac::BitsSelectOp() : value.getDefiningOp<ac::BitsSelectOp>();
    if (select && depth < 32) {
        Value condition = select->getOperand(0);
        if (auto truth = readableFact(condition, facts))
            return readableMuxBody(select->getOperand(*truth ? 1 : 2), target,
                                   std::move(facts), body, indent, depth + 1);
        llvm::DenseSet<Value> visited;
        if (readableKnownBit(condition) && readableUseCount(value, visited) == 1) {
            auto rendered = net(condition);
            if (failed(rendered)) return failure();
            std::string padding(indent, ' ');
            body += padding + "if (" + *rendered + ") begin\n";
            auto yes = facts, no = facts;
            readableAssume(condition, true, yes);
            readableAssume(condition, false, no);
            if (failed(readableMuxBody(select->getOperand(1), target, std::move(yes), body, indent + 4, depth + 1)))
                return failure();
            std::string otherwise;
            if (failed(readableMuxBody(select->getOperand(2), target, std::move(no), otherwise, indent, depth + 1)))
                return failure();
            if (StringRef(otherwise).starts_with(padding + "if (")) {
                body += padding + "end else " + otherwise.substr(padding.size());
            } else {
                body += padding + "end else begin\n";
                SmallVector<StringRef> lines;
                StringRef(otherwise).split(lines, '\n', -1, false);
                for (auto line : lines) body += "    " + line.str() + "\n";
                body += padding + "end\n";
            }
            return success();
        }
    }
    auto expression = readableAssignment(value);
    if (failed(expression)) return failure();
    body += std::string(indent, ' ') + target.str() + " = " + *expression + ";\n";
    return success();
}

FailureOr<std::string> readableStructuredMux(Value value) {
    auto select = value.getDefiningOp<ac::BitsSelectOp>();
    auto width = readableWidth(value);
    llvm::DenseSet<Value> visited;
    if (!select || !width || *width < 2 || !readableKnownBit(select->getOperand(0)) ||
        readableUseCount(value, visited) != 1)
        return failure();
    std::string preferred = "next_value";
    SmallVector<Value> pending{value};
    llvm::DenseSet<Value> followed;
    while (!pending.empty() && followed.size() < 256) {
        Value current = pending.pop_back_val();
        if (!followed.insert(current).second) continue;
        for (auto &use : current.getUses()) {
            if (auto instance = dyn_cast<ac::InstanceOp>(use.getOwner())) {
                auto *callee = context.analysis.resolveCallee(instance);
                auto port = context.rtlPortName(callee, cast<StringAttr>(callee->getAttrOfType<ArrayAttr>("input_names")[use.getOperandNumber()]).getValue());
                auto owner = rtlIdentifier(instance.getInstanceName(), [&] { return instance.emitOpError(); });
                if (succeeded(port) && succeeded(owner)) preferred = rtlIdentifierStem(*owner) + "_" + rtlIdentifierStem(*port);
            } else if (auto rule = dyn_cast<ac::RuleOp>(use.getOwner())) {
                pending.push_back(rule.getBody().front().getArgument(use.getOperandNumber()));
            } else if (isa<ac::YieldOp>(use.getOwner())) {
                if (auto rule = dyn_cast<ac::RuleOp>(use.getOwner()->getParentOp()))
                    pending.push_back(rule.getResult(use.getOperandNumber()));
            }
        }
    }
    auto name = sourceNetName(value, preferred);
    std::string body;
    // Publish the destination first, while retaining recursive/shared values.
    names.try_emplace(value, name);
    if (failed(readableMuxBody(value, name, ReadableFacts{}, body, 4))) return failure();
    auto type = context.rtlType(value.getType(), value.getDefiningOp());
    if (failed(type)) return failure();
    readableDeclaration("", *type, name);
    out << "  always_comb begin\n" << body << "  end\n";
    return name;
}
