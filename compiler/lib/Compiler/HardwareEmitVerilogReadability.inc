// Physical RTL presentation. This consumes verified SSA without changing it.
Value readableSource(Value value) {
    llvm::DenseSet<Value> visited;
    while (visited.insert(value).second) {
        if (ownershipOpaque.contains(value)) break;
        if (auto alias = ownershipAliases.find(value); alias != ownershipAliases.end()) {
            value = alias->second;
            continue;
        }
        if (auto argument = dyn_cast<BlockArgument>(value)) {
            if (auto rule = dyn_cast<ac::RuleOp>(argument.getOwner()->getParentOp())) {
                value = rule.getCaptures()[argument.getArgNumber()];
                continue;
            }
        }
        if (auto rule = value.getDefiningOp<ac::RuleOp>()) {
            value = cast<ac::YieldOp>(rule.getBody().front().back())
                        .getValues()[cast<OpResult>(value).getResultNumber()];
            continue;
        }
        break;
    }
    return value;
}

std::optional<unsigned> readableWidth(Value value) {
    auto bits = dyn_cast<ac::BitsType>(value.getType());
    if (!bits || !context.isClosedStatic(bits.getWidth()))
        return std::nullopt;
    auto width = context.staticRtlValue(bits.getWidth(), definition);
    unsigned number = 0;
    if (failed(width) || StringRef(*width).getAsInteger(10, number) || !number)
        return std::nullopt;
    return number;
}

// Enum carriers are the unsigned packed encoding, including invalid/X/Z bits.
// Only the data result of from_bits is a representation alias; membership is
// an independent four-state computation and must retain its original producer.
Value readableEnumOperand(Value value) {
    if (ownershipOpaque.contains(value)) return value;
    auto *op = value.getDefiningOp();
    if (!op) return value;
    ac::EnumType type;
    Value bits, operand;
    if (auto convert = dyn_cast<ac::EnumToBitsOp>(op)) {
        operand = convert.getOperand();
        type = dyn_cast<ac::EnumType>(operand.getType());
        bits = value;
    } else if (auto convert = dyn_cast<ac::EnumFromBitsOp>(op)) {
        if (cast<OpResult>(value).getResultNumber() != 0) return value;
        type = dyn_cast<ac::EnumType>(value.getType());
        bits = operand = convert.getOperand();
    }
    if (!type) return value;
    auto enumeration = context.analysis.resolveEnum(type, op);
    auto width = readableWidth(bits);
    if (failed(enumeration) || !width || enumeration->width != *width)
        return value;
    return operand;
}

std::optional<std::string> readableLiteral(Value value) {
    value = readableSource(value);
    if (auto member = value.getDefiningOp<ac::EnumCreateOp>()) {
        auto symbol = context.rtlEnumMember(value.getType(), member.getMemberAttr(), member);
        if (succeeded(symbol)) return *symbol;
        return std::nullopt;
    }
    if (isa<ac::BitsType>(value.getType()))
        if (auto literal = context.rtlRootConstants.find(value); literal != context.rtlRootConstants.end()) return literal->second;
    if (auto pattern = value.getDefiningOp<ac::BitsConstant4Op>())
        return std::to_string(pattern.getPattern().size()) + "'b" +
               pattern.getPattern().str();
    auto constant = value.getDefiningOp<ac::BitsConstantOp>();
    auto width = readableWidth(value);
    if (!constant || !width || !context.isClosedStatic(constant.getValue()))
        return std::nullopt;
    auto literal = context.staticRtlValue(constant.getValue(), constant);
    if (failed(literal))
        return std::nullopt;
    if (StringRef(*literal).starts_with("-"))
        return "$unsigned(" + std::to_string(*width) + "'(" + *literal + "))";
    return std::to_string(*width) + "'d" + *literal;
}

std::optional<bool> readableBit(Value value, unsigned depth = 0) {
    if (ownershipOpaque.contains(value)) return std::nullopt;
    if (depth > 32 || readableWidth(value) != 1)
        return std::nullopt;
    value = readableSource(value);
    if (auto function = readableFunction(value))
        if (function->values[0] < 2 && llvm::all_of(function->values,
                [&](unsigned bit) { return bit == function->values[0]; }))
            return function->values[0] == 1;
    if (auto literal = readableLiteral(value)) {
        if (*literal == "1'd0" || *literal == "1'b0")
            return false;
        if (*literal == "1'd1" || *literal == "1'b1")
            return true;
    }
    auto *op = value.getDefiningOp();
    if (!op)
        return std::nullopt;
    if (auto compare = dyn_cast<ac::BitsCompareOp>(op)) {
        auto lhs = readableBit(op->getOperand(0), depth + 1);
        auto rhs = readableBit(op->getOperand(1), depth + 1);
        if (lhs && rhs && (compare.getPredicate() == "eq" ||
                           compare.getPredicate() == "case_eq"))
            return *lhs == *rhs;
    }
    if (auto binary = dyn_cast<ac::BitsBinaryOp>(op)) {
        auto lhs = readableBit(op->getOperand(0), depth + 1);
        auto rhs = readableBit(op->getOperand(1), depth + 1);
        if (binary.getOpcode() == "and") {
            if ((lhs && !*lhs) || (rhs && !*rhs))
                return false;
            if (lhs && rhs)
                return *lhs && *rhs;
        }
        if (binary.getOpcode() == "or") {
            if ((lhs && *lhs) || (rhs && *rhs))
                return true;
            if (lhs && rhs)
                return *lhs || *rhs;
        }
    }
    return std::nullopt;
}

Value readableFullExtract(Value value) {
    if (ownershipOpaque.contains(value)) return value;
    auto extract = value.getDefiningOp<ac::BitsExtractOp>();
    if (!extract || !context.isClosedStatic(extract.getLow()))
        return value;
    auto low = context.staticRtlValue(extract.getLow(), extract);
    auto width = readableWidth(value);
    if (succeeded(low) && *low == "0" && width &&
        width == readableWidth(extract.getOperand()))
        return extract.getOperand();
    return value;
}

bool readableInlineUses(Value value, llvm::DenseSet<Value> &visited) {
    if (!visited.insert(value).second)
        return true;
    for (OpOperand &use : value.getUses()) {
        auto *owner = use.getOwner();
        if (auto rule = dyn_cast<ac::RuleOp>(owner)) {
            if (!readableInlineUses(rule.getBody().front().getArgument(
                                        use.getOperandNumber()), visited))
                return false;
        } else if (auto yield = dyn_cast<ac::YieldOp>(owner)) {
            if (auto rule = dyn_cast<ac::RuleOp>(owner->getParentOp())) {
                if (!readableInlineUses(rule.getResult(use.getOperandNumber()), visited))
                    return false;
            } else if (!isa<ac::ModuleOp>(owner->getParentOp())) {
                return false;
            }
        } else if (auto extract = dyn_cast<ac::BitsExtractOp>(owner)) {
            if (readableFullExtract(extract.getResult()) == extract.getResult() ||
                !readableInlineUses(extract.getResult(), visited))
                return false;
        } else if (isa<ac::EnumToBitsOp, ac::EnumFromBitsOp>(owner)) {
            for (Value result : owner->getResults())
                if (!readableInlineUses(result, visited)) return false;
        } else if (!isa<ac::BitsUnaryOp, ac::BitsBinaryOp, ac::BitsCompareOp,
                        ac::BitsSelectOp, ac::BitsConcatOp, ac::BitsResizeOp,
                        ac::ValueRequireOp, ac::StructGetOp, ac::StructCreateOp,
                        ac::InstanceOp, ac::SourceExpectOp>(owner)) {
            return false;
        }
    }
    return true;
}

bool canInlineReadable(Value value, Operation *op) {
    bool projection = isa<ac::StructGetOp, ac::BitsExtractOp>(op);
    if (!ac::sourceValueNames(value).empty() || (!projection && !readableWidth(value)) ||
        !isa<ac::BitsUnaryOp, ac::BitsBinaryOp, ac::BitsCompareOp,
             ac::BitsSelectOp, ac::BitsConcatOp, ac::BitsResizeOp,
             ac::ValueRequireOp, ac::StructGetOp, ac::BitsExtractOp>(op))
        return false;
    if (auto binary = dyn_cast<ac::BitsBinaryOp>(op))
        if (binary.getOpcode() == "udiv" || binary.getOpcode() == "urem")
            return false;
    llvm::DenseSet<Value> visited;
    if (!readableInlineUses(value, visited))
        return false;
    visited.clear();
    return readableWidth(value) == 1 && readableControlUses.contains(readableSource(value))
        ? readableControlUses.lookup(readableSource(value)) == 1
        : readableUseCount(value, visited) == 1;
}

// Materialization is a typed graph decision. Spelling a source identifier or
// choosing a longer diagnostic name must never change this decision. Each
// operation/literal/wire is one display unit; a materialized input is a leaf.
static constexpr unsigned readableExpressionLimit = 12;
unsigned readableOperandCost(Value value, unsigned depth = 0) {
    if (depth > 16) return 1;
    value = readableSource(value);
    if (readableWidth(value) == 1) {
        auto view = readableControlView(value);
        if (view.literal < 4) return 1;
        value = view.value;
    }
    if (auto found = readableInlineCosts.find(value); found != readableInlineCosts.end()) return found->second;
    Value carrier = readableEnumOperand(value);
    return carrier == value ? 1 : readableOperandCost(carrier, depth + 1);
}

unsigned readableExpressionCost(Value value) {
    unsigned cost = 1;
    auto *operation = value.getDefiningOp();
    if (!operation) return cost;
    auto operands = operation->getOperands();
    if (isa<ac::ValueRequireOp>(operation)) operands = operands.drop_front();
    for (Value input : operands) {
        cost += readableOperandCost(input);
        if (cost > readableExpressionLimit) break;
    }
    return cost;
}

// Remove a sizing shell only through typed information, never by parsing RTL
// strings. Equal-width unsigned arithmetic/bitwise contexts keep precisely the
// child's original width. A different-width consumer retains the explicit cast
// so a narrow intermediate still wraps before a later widening operation.
std::string readableTypedOperand(Value input, Value output, Operation *consumer,
                                  StringRef rendered) {
    auto binary = dyn_cast<ac::BitsBinaryOp>(consumer);
    if (!context.isPhysical() || !binary)
        return rendered.str();
    bool shift = binary.getOpcode() == "shl" || binary.getOpcode() == "lshr";
    if (shift && input != binary.getLhs()) return rendered.str();
    if (!shift && !llvm::is_contained(
            ArrayRef<StringRef>{"add", "sub", "mul", "and", "or", "xor"}, binary.getOpcode()))
        return rendered.str();
    auto width = readableWidth(output);
    if (!width || readableWidth(input) != width || readableWidth(binary.getLhs()) != width ||
        (!shift && readableWidth(binary.getRhs()) != width))
        return rendered.str();
    input = readableSource(input);
    auto *producer = input.getDefiningOp();
    bool safe = isa_and_nonnull<ac::BitsSelectOp, ac::BitsUnaryOp>(producer) ||
        (*width == 1 && isa_and_nonnull<ac::BitsCompareOp>(producer));
    if (auto operation = dyn_cast_or_null<ac::BitsBinaryOp>(producer))
        safe = llvm::is_contained(ArrayRef<StringRef>{"add", "sub", "mul", "and", "or", "xor"},
                                  operation.getOpcode());
    if (!safe) return rendered.str();
    auto found = readableInlineExpressions.find(input);
    return found == readableInlineExpressions.end() ? rendered.str() : found->second;
}

// Count real consumers through source-level forwarding. Preserve SSA sharing
// instead of duplicating even a short arithmetic DAG at several use sites.
unsigned readableUseCount(Value value, llvm::DenseSet<Value> &visited) {
    if (!visited.insert(value).second)
        return 2;
    unsigned count = 0;
    for (OpOperand &use : value.getUses()) {
        auto *owner = use.getOwner();
        if (auto rule = dyn_cast<ac::RuleOp>(owner)) {
            count += readableUseCount(rule.getBody().front().getArgument(
                                          use.getOperandNumber()), visited);
        } else if (isa<ac::YieldOp>(owner) && isa<ac::RuleOp>(owner->getParentOp())) {
            auto rule = cast<ac::RuleOp>(owner->getParentOp());
            count += readableUseCount(rule.getResult(use.getOperandNumber()), visited);
        } else if (auto extract = dyn_cast<ac::BitsExtractOp>(owner);
                   extract && readableFullExtract(extract.getResult()) != extract.getResult()) {
            count += readableUseCount(extract.getResult(), visited);
        } else if (isa<ac::EnumToBitsOp, ac::EnumFromBitsOp>(owner)) {
            for (Value result : owner->getResults())
                count += readableUseCount(result, visited);
        } else {
            ++count;
        }
        if (count > 1)
            return 2;
    }
    return count;
}

bool isReadableRegister(Operation *op) {
    if (!context.isPhysical() || op->getNumResults() != 1 ||
        !isa<ac::InstanceOp, ac::CollectionOp>(op) ||
        (isa<ac::CollectionOp>(op) && !context.isSynthesis()))
        return false;
    auto *callee = isa<ac::InstanceOp>(op)
        ? context.analysis.resolveCallee(cast<ac::InstanceOp>(op))
        : context.analysis.resolveCallee(cast<ac::CollectionOp>(op));
    auto kind = context.analysis.getPrimitiveKind(callee);
    return (kind == "dff" || kind == "dffe") &&
           // Synthesis projection verifies its complete occurrence topology,
           // including unchecked explicit-domain imports absent from the
           // managed source-check commit inventory.
           (context.isSynthesis() || llvm::any_of(context.sourceChecks().commits,
                        [&](const ac::HardwareCheckCommitEndpoint &endpoint) {
                            return endpoint.allocation == op;
                        }));
}

// Controls are observed only for knownness and known-one truth by physical
// storage. These shells preserve both, including an input Z becoming X.
Value readableControl(Value value, unsigned depth = 0) {
    value = readableSource(value);
    if (ownershipOpaque.contains(value)) return value;
    if (depth > 32)
        return value;
    if (auto binary = value.getDefiningOp<ac::BitsBinaryOp>()) {
        if (binary.getOpcode() == "and") {
            if (readableBit(binary.getLhs()) == true)
                return readableControl(binary.getRhs(), depth + 1);
            if (readableBit(binary.getRhs()) == true)
                return readableControl(binary.getLhs(), depth + 1);
        }
        if (binary.getOpcode() == "or") {
            if (readableBit(binary.getLhs()) == false)
                return readableControl(binary.getRhs(), depth + 1);
            if (readableBit(binary.getRhs()) == false)
                return readableControl(binary.getLhs(), depth + 1);
        }
    }
    if (auto result = dyn_cast<OpResult>(value))
        if (auto merge = dyn_cast<ac::ValueMergeOp>(result.getOwner()))
            if (result.getResultNumber() == 1 && merge.getGuards().size() == 1)
                return readableControl(merge.getGuards().front(), depth + 1);
    if (auto select = value.getDefiningOp<ac::BitsSelectOp>())
        if (readableBit(select->getOperand(1)) == true &&
            readableBit(select->getOperand(2)) == false)
            return readableControl(select->getOperand(0), depth + 1);
    return value;
}

bool readableImplies(Value enabled, Value condition, unsigned depth = 0) {
    enabled = readableSource(enabled);
    condition = readableSource(condition);
    if (enabled == condition || readableControl(enabled) == readableControl(condition))
        return true;
    if (depth > 32)
        return false;
    if (auto binary = enabled.getDefiningOp<ac::BitsBinaryOp>())
        if (binary.getOpcode() == "and")
            return readableImplies(binary.getLhs(), condition, depth + 1) ||
                   readableImplies(binary.getRhs(), condition, depth + 1);
    return false;
}

std::string readableGeneratedStem(StringRef preferred) {
    auto raw = rtlIdentifierStem(preferred);
    std::string stem;
    for (char byte : raw) {
        bool word = isAsciiAlpha(byte) || isAsciiDigit(byte);
        if (word) stem += byte;
        else if (!stem.empty() && stem.back() != '_') stem += '_';
    }
    while (!stem.empty() && stem.back() == '_') stem.pop_back();
    if (stem.empty()) stem = "signal";
    if (isAsciiDigit(stem.front())) stem = "signal_" + stem;
    if (StringRef(stem).starts_with("pyc_")) stem = "signal_" + StringRef(stem).drop_front(4).str();
    auto token = rtlIdentifier(stem, [&] { return definition.emitOpError(); });
    if (succeeded(token) && StringRef(*token).starts_with("\\")) stem += "_signal";
    return stem;
}

std::string readableName(StringRef preferred, bool authored = false) {
    // Escaped and simple SV identifiers share a logical namespace. Allocate
    // collision suffixes on that identity, before restoring the terminator.
    bool escaped = preferred.starts_with("\\") && preferred.ends_with(" ");
    std::string generated;
    if (escaped && !authored && context.isPhysical()) {
        generated = readableGeneratedStem(preferred);
        preferred = generated;
        escaped = false;
    }
    auto stem = escaped ? preferred.drop_front().drop_back() : preferred;
    std::string name = stem.str();
    unsigned suffix = 0;
    while (readableNames.contains(name) ||
           ((!authored || suffix) && readableAuthoredNames.contains(name)))
        name = stem.str() + "_" + std::to_string(++suffix);
    readableNames.insert(name);
    return escaped ? "\\" + name + " " : name;
}

FailureOr<std::string> readableInstanceName(Operation *operation) {
    if (auto found = readableInstanceNames.find(operation); found != readableInstanceNames.end())
        return found->second;
    auto raw = operation->getAttrOfType<StringAttr>("instance_name").getValue();
    std::string preferred = raw.str();
    auto *callee = isa<ac::InstanceOp>(operation)
        ? context.analysis.resolveCallee(cast<ac::InstanceOp>(operation))
        : context.analysis.resolveCallee(cast<ac::CollectionOp>(operation));
    if (auto module = dyn_cast_or_null<ac::ModuleOp>(callee)) {
        // These names are reserved compiler call-site IDs, not authored names.
        // Keep the original occurrence/identity; only its RTL spelling changes.
        uint64_t ordinal = 0;
        if (raw.starts_with("__pyc_call_") &&
            !raw.drop_front(StringRef("__pyc_call_").size()).getAsInteger(10, ordinal))
            preferred = rtlIdentifierStem(context.names(module).rtl) + "_inst_" + std::to_string(ordinal);
    }
    auto id = rtlIdentifier(preferred, [&] { return operation->emitOpError(); });
    if (failed(id)) return failure();
    auto name = readableName(*id, !raw.starts_with("__pyc_call_"));
    readableInstanceNames.try_emplace(operation, name);
    return name;
}

// Derive a diagnostic name from the actual typed enum comparison. This is
// naming only; equality, width, invalid carriers and X/Z remain unchanged.
std::optional<std::string> readableEnumCompareName(Value value) {
    auto compare = value.getDefiningOp<ac::BitsCompareOp>();
    if (!compare || (compare.getPredicate() != "eq" && compare.getPredicate() != "ne"))
        return std::nullopt;
    Value carriers[2];
    for (unsigned i = 0; i != 2; ++i) {
        Value input = readableSource(compare->getOperand(i));
        auto bits = input.getDefiningOp<ac::EnumToBitsOp>();
        if (!bits || readableEnumOperand(input) == input) return std::nullopt;
        carriers[i] = readableSource(bits.getOperand());
    }
    if (carriers[0].getType() != carriers[1].getType()) return std::nullopt;
    for (unsigned i = 0; i != 2; ++i) {
        auto member = carriers[i].getDefiningOp<ac::EnumCreateOp>();
        if (!member) continue;
        auto carrier = readableNameAnchor(carriers[1 - i]);
        if (!carrier) return std::nullopt;
        auto stem = *carrier;
        if (stem.empty() || !llvm::all_of(stem, [](char c) { return llvm::isAlnum(c) || c == '_'; }))
            return std::nullopt;
        return stem + (compare.getPredicate() == "eq" ? "_is_" : "_is_not_") +
            member.getMemberAttr().getValue().str();
    }
    return std::nullopt;
}

// One optimized value gets one wire, even when several source bindings name
// it. The remaining aliases are kept in the actual RTL for source navigation.
std::string sourceNetName(Value value, StringRef fallback = {}) {
    auto bindings = ac::sourceValueNames(value);
    if (!bindings.empty()) {
        std::string spelling = context.isPhysical() ? readableBindingName(value, bindings) : bindings.front().name.getValue().str();
        StringRef raw(spelling);
        auto id = rtlIdentifier(raw,
                                     [&] { return definition.emitOpError(); });
        if (succeeded(id)) {
            bool asciiIdentifier = !raw.empty() &&
                (isAsciiAlpha(raw.front()) || raw.front() == '_');
            for (char byte : raw)
                asciiIdentifier &= isAsciiAlpha(byte) || isAsciiDigit(byte) || byte == '_';
            // C++ reserved names need not become hex in RTL. The standard SV
            // escape retains an ASCII source binding, including keyword names.
            if (asciiIdentifier && *id != raw)
                return readableName("\\" + raw.str() + " ", true);
            auto name = readableName(*id, true);
            return name;
        }
    }
    // Keep the existing symbolic Enum/member spelling ahead of generic
    // source-branch roles; the method provenance is still recorded separately.
    if (context.isPhysical())
        if (auto name = readableEnumCompareName(value)) {
            auto id = rtlIdentifier(*name, [&] { return definition.emitOpError(); });
            if (succeeded(id)) return readableName(*id);
        }
    if (context.isPhysical()) {
        auto hint = readableRoleHints.find(value);
        if (hint == readableRoleHints.end())
            if (auto auxiliary = readableAuxiliaryStem(value)) return readableDerivedName(*auxiliary);
        auto role = hint != readableRoleHints.end() ? std::optional<std::string>(hint->second) : readableRoleStem(value);
        if (role) {
            auto id = rtlIdentifier(*role, [&] { return definition.emitOpError(); });
            if (succeeded(id)) return readableName(*id);
        }
    }
    if (!fallback.empty())
        return readableName(fallback);
    if (context.isPhysical())
        if (auto construction = readableConstructionStem(value)) return readableDerivedName(*construction);
    if (context.isPhysical())
        if (auto pin = readablePrimitiveResultStem(value)) return readableDerivedName(*pin);
    if (context.isPhysical())
        if (auto guarded = readableGuardedControlStem(value)) return readableDerivedName(*guarded);
    if (context.isPhysical())
        if (auto control = readableControlRelationStem(value)) return readableDerivedName(*control);
    if (context.isPhysical())
        if (auto operation = readableOperationStem(value)) return readableDerivedName(*operation);
    if (context.isPhysical()) return readableDerivedName(readablePurposeStem(value));
    std::string role = "value";
    auto *operation = value.getDefiningOp();
    if (auto binary = dyn_cast_or_null<ac::BitsBinaryOp>(operation))
        role = binary.getOpcode().str();
    else if (auto compare = dyn_cast_or_null<ac::BitsCompareOp>(operation))
        role = "compare_" + compare.getPredicate().str();
    else if (auto get = dyn_cast_or_null<ac::StructGetOp>(operation))
        role = get.getField().str();
    else if (operation && isa<ac::InstanceOp, ac::CollectionOp>(operation))
        role = operation->getAttrOfType<StringAttr>("instance_name").getValue().str() +
               "_result_" + std::to_string(cast<OpResult>(value).getResultNumber());
    else if (operation) {
        role = operation->getName().getStringRef().rsplit('.').second.str();
        for (char &character : role) if (character == '.') character = '_';
    }
    // Add the generated suffix first: "and_7" is a legal identifier even
    // though the unsuffixed operation word is a Verilog keyword.
    role += "_" + std::to_string(next++);
    auto id = rtlIdentifier(role, [&] { return definition.emitOpError(); });
    return readableName(succeeded(id) ? *id : "value");
}

LogicalResult emitReadableRegister(ac::InstanceOp instance) {
    auto kind = context.analysis.getPrimitiveKind(context.analysis.resolveCallee(instance));
    bool enabled = kind == "dffe";
    auto clock = net(instance.getOperand(0));
    auto reset = net(instance.getOperand(1));
    auto q = net(instance.getResult(0));
    auto initial = physicalInitializer(instance.getOperand(enabled ? 4 : 3));
    if (failed(clock) || failed(reset) || failed(q) || failed(initial))
        return failure();
    *reset = context.rtlReset(*reset);
    Value data = readableSource(instance.getOperand(enabled ? 3 : 2));
    Value control = enabled ? instance.getOperand(2) : Value();
    llvm::DenseSet<Value> visitedData;
    while (enabled && visitedData.insert(data).second) {
        if (auto merge = data.getDefiningOp<ac::ValueMergeOp>())
            if (data == merge.getResult(0) && merge.getGuards().size() == 1 &&
                cast<ArrayAttr>(merge.getPaths()[0]).empty() &&
                readableSource(merge.getBase()) == instance.getResult(0) &&
                readableImplies(control, merge.getGuards().front())) {
                data = readableSource(merge.getValues().front());
                continue;
            }
        if (auto select = data.getDefiningOp<ac::BitsSelectOp>())
            if (readableSource(select->getOperand(2)) == instance.getResult(0) &&
                readableImplies(control, select->getOperand(0))) {
                data = readableSource(select->getOperand(1));
                continue;
            }
        break;
    }
    auto d = readableAssignment(data);
    auto en = enabled ? net(readableControl(control))
                      : FailureOr<std::string>(std::string("1'b1"));
    if (failed(d) || failed(en))
        return failure();
    if (isa<ac::EnumType>(instance.getResult(0).getType())) {
        // Keep the original D and E as separate named connections. These are
        // wire aliases, not a reconstructed transition/enable or new storage.
        auto type = context.rtlType(instance.getResult(0).getType(), instance);
        if (failed(type)) return failure();
        auto nextState = readableName(rtlIdentifierStem(*q) + "_next");
        readableDeclaration("wire", *type, nextState);
        readableAssignment(nextState, *d, false);
        *d = nextState;
        if (enabled && readableBit(control) != true) {
            auto update = readableName(rtlIdentifierStem(*q) + "_enable");
            readableDeclaration("wire", "logic [0:0]", update);
            readableAssignment(update, *en, false);
            *en = update;
        }
    }
    if (context.isSynthesis()) {
        out << "  always_ff @(posedge " << *clock << ") begin\n"
            << "    if (" << *reset << ")\n"
            << "      " << *q << " <= " << *initial << ";\n"
            << (!enabled || readableBit(control) == true ? "    else\n" : "    else if (" + *en + ")\n")
            << "      " << *q << " <= " << *d << ";\n"
            << "  end\n";
        return success();
    }
    std::string error = readableName("storage_error_" + rtlIdentifierStem(*q));
    readableErrors.emplace_back(error, "$isunknown(" + *reset + ") || (!" + *reset + " && $isunknown(" + *en + "))");
    readableClock = *clock;
    out << "  initial " << *q << " = " << *initial << ";\n"
        << "  always_ff @(posedge " << *clock << ") begin\n"
        << "    if (__checks.allow_update(" << *clock << ")) begin\n"
        << "      if (" << *reset << ")\n"
        << "        " << *q << " <= " << *initial << ";\n"
        << "      else if (" << *en << ")\n"
        << "        " << *q << " <= " << *d << ";\n"
        << "    end\n  end\n";
    localErrors.push_back("__checks." + error);
    return success();
}

// A Collection retains the existing packed lane order and one update process
// per authenticated endpoint. Payloads may be nominal records or enums; the
// same payloadWidth/layout contract used by the original primitive is used.
LogicalResult emitReadableCollection(ac::CollectionOp collection) {
    auto kind = context.analysis.getPrimitiveKind(context.analysis.resolveCallee(collection));
    bool enabled = kind == "dffe";
    SmallVector<Value> roots{collection.getOperand(enabled ? 3 : 2)};
    if (enabled) roots.push_back(collection.getOperand(2));
    if (auto plan = prepareReadableTableLanes(roots, false, collection))
        return emitReadableCollectionLanes(collection, *plan);
    auto count = context.shapeSize(collection.getShape(), collection, true);
    auto table = dyn_cast<ac::TableType>(collection.getResult(0).getType());
    if (!table) return collection.emitOpError() << "storage collection requires Table result";
    auto width = context.payloadWidth(table.getElementType(), collection, true);
    auto q = net(collection.getResult(0));
    auto initial = physicalInitializer(collection.getOperand(enabled ? 4 : 3));
    SmallVector<std::string> pins;
    for (Value input : collection->getOperands()) {
        auto rendered = net(input);
        if (failed(rendered)) return failure();
        pins.push_back(*rendered);
    }
    if (failed(count) || failed(width) || failed(q) || failed(initial)) return failure();
    auto lane = readableName(rtlIdentifierStem(*q) + "_lane");
    auto block = readableName(rtlIdentifierStem(*q) + "_update");
    auto pin = [&](unsigned index) {
        return readablePackedElement(pins[index], lane,
            cast<ac::TableType>(collection.getOperand(index).getType()), collection);
    };
    auto clock = pin(0), reset = pin(1), data = pin(enabled ? 3 : 2);
    auto old = readablePackedElement(*q, lane, table, collection);
    auto resetValue = readablePackedElement(*initial, lane, table, collection);
    auto enable = enabled ? pin(2) : FailureOr<std::string>(std::string("1'b1"));
    if (failed(clock) || failed(reset) || failed(data) || failed(old) ||
        failed(resetValue) || failed(enable)) return failure();
    out << "  for (genvar " << lane << " = 0; " << lane << " < (" << *count
        << "); ++" << lane << ") begin : " << block << "\n"
        << "    always_ff @(posedge " << *clock << ") begin\n"
        << "      if (" << context.rtlReset(*reset) << ")\n"
        << "        " << *old << " <= " << *resetValue << ";\n";
    if (enabled)
        out << "      else if (" << *enable << ")\n";
    else
        out << "      else\n";
    out << "        " << *old << " <= " << *data << ";\n"
        << "    end\n  end\n";
    return success();
}
#include "HardwareEmitVerilogControlView.inc"
#include "HardwareEmitVerilogStructured.inc"
