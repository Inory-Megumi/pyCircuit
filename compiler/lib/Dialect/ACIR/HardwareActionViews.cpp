#include "HardwareActionViews.h"
#include "HardwareSourceCheckPreflight.h"
#include "HardwareSampledAdmission.h"
#include "HardwareGrantProof.h"
#include "mlir/IR/Matchers.h"
#include "llvm/ADT/APSInt.h"
#include <functional>

using namespace mlir;
namespace acir::ac::detail {
namespace {
bool exactActionFields(DictionaryAttr row, std::initializer_list<StringRef> fields) {
    if (!row || row.size() != fields.size()) return false;
    return llvm::all_of(fields, [&](StringRef field) { return bool(row.get(field)); });
}
std::optional<uint64_t> actionIndex(DictionaryAttr row, StringRef field) {
    auto value = row ? row.getAs<IntegerAttr>(field) : IntegerAttr();
    if (!value || !value.getType().isSignlessInteger(64) || value.getInt() < 0) return {};
    return value.getInt();
}

class ActionGrantProof {
    using Core = HardwareGrantProof;
    using Node = Core::Node;
    struct Entry { std::optional<HardwareIdentityEndpoint> endpoint; Core::NodeView synthetic; };
    ModuleOp module;
    const HardwareAnalysis &analysis;
    SourceCheckBudget &budget;
    SmallVector<Entry, 0> nodes;
    DenseMap<std::pair<std::pair<Value, ArrayAttr>, Type>, Node> ids;
    DenseMap<Node, Core::NodeView> views;
    Core core;

    FailureOr<Node> bind(Value value, const HardwareIdentityScope &scope) {
        auto endpoint = makeIdentityEndpoint(value, scope, analysis, budget);
        if (failed(endpoint)) return failure();
        auto normalized = normalizeIdentityEndpoint(*endpoint,
            {HardwareIdentityTraversal::OrdinaryInstances, {}}, analysis, budget);
        if (failed(normalized) || failed(budget.debit(64 + normalized->scope.path.size() * 8, module)))
            return failure();
        SmallVector<Attribute> path;
        for (auto instance : normalized->scope.path) path.push_back(instance.getOccurrence());
        auto key = std::make_pair(std::make_pair(normalized->value,
            ArrayAttr::get(module.getContext(), path)), normalized->resolvedType);
        auto found = ids.find(key);
        if (found != ids.end()) return found->second;
        Node id = nodes.size(); nodes.push_back({std::move(*normalized), {}}); ids.try_emplace(key, id);
        return id;
    }
    FailureOr<Node> canonical(Node id, unsigned depth) {
        if (id >= nodes.size() || depth > 128 || failed(budget.debit(1, module))) return failure();
        if (!nodes[id].endpoint) return id;
        auto endpoint = *nodes[id].endpoint;
        if (auto result = dyn_cast<OpResult>(endpoint.value))
            if (auto rule = dyn_cast<RuleOp>(result.getOwner())) {
                auto yield = cast<YieldOp>(rule.getBody().front().getTerminator());
                auto child = bind(yield.getValues()[result.getResultNumber()], endpoint.scope);
                if (failed(child)) return failure();
                return canonical(*child, depth + 1);
            }
        return id;
    }
    FailureOr<Core::NodeView> inspect(Node id) {
        if (id >= nodes.size() || failed(budget.debit(4, module))) return failure();
        if (!nodes[id].endpoint) return nodes[id].synthetic;
        if (auto found = views.find(id); found != views.end()) return found->second;
        auto endpoint = *nodes[id].endpoint;
        auto bindings = getIdentityScopeBindings(endpoint.scope, analysis, budget, module);
        if (failed(bindings)) return failure();
        Core::NodeView view;
        if (!isa<BitsType>(endpoint.resolvedType)) return view;
        auto width = analysis.getPackedWidth(endpoint.resolvedType, *bindings, module);
        if (failed(width)) return failure();
        view.width = *width;
        auto operation = endpoint.value.getDefiningOp();
        if (auto literal = dyn_cast_or_null<BitsConstantOp>(operation)) {
            auto value = analysis.evaluateStatic(literal.getValue(), *bindings, literal);
            if (failed(value)) return failure();
            if (auto number = dyn_cast<MathIntAttr>(*value)) {
                if (failed(budget.debit(number.getCanonicalValue().size() + *width / 64 + 1, module)))
                    return failure();
                llvm::APSInt integer(number.getCanonicalValue());
                if (!integer.isNegative() && integer.getActiveBits() <= *width)
                    view.fullyKnown = Core::Constant{number, *width};
            }
        } else if (auto unary = dyn_cast_or_null<BitsUnaryOp>(operation)) {
            if (unary.getOpcode() == "not") view.kind = Core::NodeView::Not;
        } else if (auto binary = dyn_cast_or_null<BitsBinaryOp>(operation)) {
            if (binary.getOpcode() == "and") view.kind = Core::NodeView::And;
            if (binary.getOpcode() == "or") view.kind = Core::NodeView::Or;
        } else if (isa_and_nonnull<BitsSelectOp>(operation)) view.kind = Core::NodeView::Select;
        else if (auto compare = dyn_cast_or_null<BitsCompareOp>(operation)) {
            if (compare.getPredicate() == "eq") view.kind = Core::NodeView::Eq;
            if (compare.getPredicate() == "ne") view.kind = Core::NodeView::Ne;
            if (compare.getPredicate() == "case_eq") {
                auto right = compare.getRhs().getDefiningOp<BitsConstantOp>();
                auto leftWidth = analysis.getPackedWidth(compare.getLhs().getType(), *bindings, compare);
                auto value = right ? analysis.evaluateStatic(right.getValue(), *bindings, right)
                                   : FailureOr<Attribute>(Attribute());
                auto number = succeeded(value) ? dyn_cast_or_null<MathIntAttr>(*value) : MathIntAttr();
                if (failed(leftWidth) || failed(value)) return failure();
                if (*leftWidth == 1 && number &&
                    (number.getCanonicalValue() == "0" || number.getCanonicalValue() == "1")) {
                    auto child = bind(compare.getLhs(), endpoint.scope);
                    if (failed(child)) return failure();
                    Node condition = *child;
                    if (number.getCanonicalValue() == "0") {
                        if (failed(budget.debit(64, module))) return failure();
                        Core::NodeView negation; negation.kind = Core::NodeView::Not;
                        negation.width = 1; negation.operands.push_back(condition);
                        condition = nodes.size(); nodes.push_back({{}, std::move(negation)});
                    }
                    view.kind = Core::NodeView::IsTrue; view.operands.push_back(condition);
                }
            }
        }
        if (view.kind != Core::NodeView::Raw && view.operands.empty())
            for (Value operand : operation->getOperands()) {
                auto child = bind(operand, endpoint.scope);
                if (failed(child)) return failure();
                view.operands.push_back(*child);
            }
        if (view.kind != Core::NodeView::Raw &&
            failed(analysis.verifyResolvedOperation(operation, *bindings))) return failure();
        if (failed(budget.debit(16, module))) return failure();
        views.try_emplace(id, view);
        return view;
    }
public:
    ActionGrantProof(ModuleOp module, const HardwareAnalysis &analysis, SourceCheckBudget &budget)
        : module(module), analysis(analysis), budget(budget),
          core([this](Node id, unsigned depth) { return canonical(id, depth); },
               [this](Node id) { return inspect(id); },
               [this](uint64_t work) { return succeeded(this->budget.debit(work, this->module)); }) {}
    FailureOr<bool> disjoint(Value left, Value right) {
        HardwareBindings bindings; bindings.owner = module;
        HardwareIdentityScope scope{module, bindings, {}};
        auto a = bind(left, scope), b = bind(right, scope);
        if (failed(a) || failed(b)) return failure();
        return core.disjoint(*a, *b);
    }
};
}

LogicalResult verifyActionDomains(RuleOp producer, RuleOp observer,
    const HardwareAnalysis &analysis, SourceCheckBudget &budget) {
    auto module = producer->getParentOfType<ModuleOp>();
    if (!module || observer->getParentOp() != module.operator->()) return failure();
    HardwareBindings bindings; bindings.owner = module;
    HardwareIdentityScope scope{module, bindings, {}};
    for (StringRef name : {"clock_capture", "reset_capture"}) {
        auto a = actionIndex(producer->getAttrOfType<DictionaryAttr>("ac.sampled_admission"), name);
        auto b = actionIndex(observer->getAttrOfType<DictionaryAttr>("ac.sampled_admission"), name);
        if (!a || !b || *a >= producer->getNumOperands() || *b >= observer->getNumOperands()) return failure();
        auto left = makeIdentityEndpoint(producer->getOperand(*a), scope, analysis, budget);
        auto right = makeIdentityEndpoint(observer->getOperand(*b), scope, analysis, budget);
        if (failed(left) || failed(right)) return failure();
        left = normalizeIdentityEndpoint(*left, {HardwareIdentityTraversal::OrdinaryInstances, {}}, analysis, budget);
        right = normalizeIdentityEndpoint(*right, {HardwareIdentityTraversal::OrdinaryInstances, {}}, analysis, budget);
        if (failed(left) || failed(right)) return failure();
        if (left->value == right->value && left->scope.root == right->scope.root &&
            left->scope.path == right->scope.path) continue;
        auto literal = [&](const HardwareIdentityEndpoint &endpoint) -> FailureOr<MathIntAttr> {
            auto constant = endpoint.value.getDefiningOp<BitsConstantOp>();
            if (!constant) return MathIntAttr();
            auto bound = getIdentityScopeBindings(endpoint.scope, analysis, budget, observer);
            if (failed(bound)) return failure();
            auto value = analysis.evaluateStatic(constant.getValue(), *bound, constant);
            if (failed(value)) return failure();
            return dyn_cast<MathIntAttr>(*value);
        };
        auto aValue = literal(*left), bValue = literal(*right);
        if (failed(aValue) || failed(bValue)) return failure();
        if (!*aValue || !*bValue || *aValue != *bValue)
            return observer.emitOpError() << "action observation crosses physical clock/reset domains";
    }
    return success();
}

LogicalResult verifyForwardOldQ(Value value, DictionaryAttr state, RuleOp reader,
    const HardwareAnalysis &analysis, SourceCheckBudget &budget) {
    auto module = reader->getParentOfType<ModuleOp>();
    HardwareBindings bindings; bindings.owner = module;
    HardwareIdentityScope scope{module, bindings, {}};
    auto owner = resolveTransactionState(module, state, analysis, bindings, budget);
    if (failed(owner)) return failure();
    auto same = [&](Value left, const HardwareIdentityScope &leftScope,
                    Value right, const HardwareIdentityScope &rightScope) -> FailureOr<bool> {
        auto a = makeIdentityEndpoint(left, leftScope, analysis, budget);
        auto b = makeIdentityEndpoint(right, rightScope, analysis, budget);
        if (failed(a) || failed(b)) return failure();
        a = normalizeIdentityEndpoint(*a, {HardwareIdentityTraversal::OrdinaryInstances, {}}, analysis, budget);
        b = normalizeIdentityEndpoint(*b, {HardwareIdentityTraversal::OrdinaryInstances, {}}, analysis, budget);
        if (failed(a) || failed(b)) return failure();
        if (a->value == b->value && a->scope.root == b->scope.root && a->scope.path == b->scope.path) return true;
        auto literal = [&](const HardwareIdentityEndpoint &at) -> FailureOr<Attribute> {
            auto constant = at.value.getDefiningOp<BitsConstantOp>();
            if (!constant) return Attribute();
            auto bound = getIdentityScopeBindings(at.scope, analysis, budget, reader);
            if (failed(bound)) return failure();
            return analysis.evaluateStatic(constant.getValue(), *bound, constant);
        };
        auto av = literal(*a), bv = literal(*b);
        if (failed(av) || failed(bv)) return failure();
        return *av && *bv && *av == *bv;
    };
    // Q identity cannot be replaced by an equal constant or another candidate.
    auto a = makeIdentityEndpoint(value, scope, analysis, budget);
    auto b = makeIdentityEndpoint(owner->q, owner->ownerScope, analysis, budget);
    if (failed(a) || failed(b)) return failure();
    a = normalizeIdentityEndpoint(*a, {HardwareIdentityTraversal::OrdinaryInstances, {}}, analysis, budget);
    b = normalizeIdentityEndpoint(*b, {HardwareIdentityTraversal::OrdinaryInstances, {}}, analysis, budget);
    if (failed(a) || failed(b) || a->value != b->value || a->scope.root != b->scope.root ||
        a->scope.path != b->scope.path) return reader.emitOpError() << "forward fallback is not the actual committed owner Q";
    auto metadata = reader->getAttrOfType<DictionaryAttr>("ac.sampled_admission");
    for (auto [name, endpoint] : {std::pair<StringRef, Value>{"clock_capture", owner->clock},
                                 {"reset_capture", owner->reset}}) {
        auto index = actionIndex(metadata, name);
        if (!index || *index >= reader->getNumOperands()) return failure();
        auto equal = same(reader->getOperand(*index), scope, endpoint, owner->ownerScope);
        if (failed(equal) || !*equal) return reader.emitOpError() << "forward Q crosses physical clock/reset domains";
    }
    return success();
}

FailureOr<ActionViewProof> verifyActionView(RuleOp rule,
    const HardwareAnalysis &analysis, SourceCheckBudget &budget) {
    auto reject = [&]() -> FailureOr<ActionViewProof> {
        return rule.emitOpError() << "action view does not match its authenticated event/argument transport";
    };
    if (failed(budget.debit(32, rule))) return failure();
    auto view = rule->getAttrOfType<DictionaryAttr>("ac.action_view");
    NamedAttrList core(view ? view : DictionaryAttr::get(rule.getContext()));
    core.erase("state"); core.erase("fields");
    if (!exactActionFields(core.getDictionary(rule.getContext()), {"capture", "action", "member", "argument",
            "occurrence", "registration", "sources"}) || rule->getNumResults() != 1 ||
        !rule.getBody().hasOneBlock()) return reject();
    auto member = view.getAs<StringAttr>("member");
    auto argument = view.getAs<StringAttr>("argument");
    auto sources = view.getAs<ArrayAttr>("sources");
    auto action = view.getAs<DictionaryAttr>("action");
    auto capture = actionIndex(view, "capture");
    if (!member || !argument || !sources || !capture ||
        !(exactActionFields(action, {"callee", "declaration", "owner"}) ||
          exactActionFields(action, {"callee", "declaration", "owner", "registration"})) ||
        !action.getAs<SymbolRefAttr>("callee") || !action.getAs<DictionaryAttr>("declaration") ||
        !action.getAs<ArrayAttr>("owner")) return reject();
    bool active = member.getValue() == "active";
    bool forward = member.getValue() == "forward";
    if ((!active && !forward && member.getValue() != "argument") ||
        (active && !argument.getValue().empty()) ||
        rule->getNumOperands() != sources.size() * (active ? 1 : 2) + unsigned(forward) ||
        (forward ? (!view.getAs<DictionaryAttr>("state") || !view.getAs<ArrayAttr>("fields") || !argument.getValue().empty())
                 : bool(view.get("state")) || bool(view.get("fields")))) return reject();
    ActionViewProof proof;
    auto &body = rule.getBody().front();
    auto yield = dyn_cast_or_null<YieldOp>(body.getTerminator());
    if (!yield || yield.getValues().size() != 1 ||
        body.getNumArguments() != rule->getNumOperands()) return reject();
    proof.operations.insert(rule); proof.operations.insert(yield);
    RuleOp observer;
    for (OpOperand &use : rule->getResult(0).getUses()) {
        auto target = dyn_cast<RuleOp>(use.getOwner());
        auto metadata = target ? target->getAttrOfType<DictionaryAttr>("ac.sampled_admission") : DictionaryAttr();
        auto inputs = metadata ? metadata.getAs<ArrayAttr>("action_inputs") : ArrayAttr();
        if (!target || target->getParentOp() != rule->getParentOp() ||
            target->getAttr("occurrence") != view.get("registration") ||
            use.getOperandNumber() != *capture || !inputs || observer) return reject();
        NamedAttrList expected(view);
        expected.erase("sources"); expected.erase("registration");
        if (llvm::count(inputs, Attribute(expected.getDictionary(rule.getContext()))) != 1)
            return reject();
        observer = target;
        proof.uses.insert(&use);
    }
    if (!observer) return reject();
    auto observerMetadata = observer->getAttrOfType<DictionaryAttr>("ac.sampled_admission");
    auto observerClock = actionIndex(observerMetadata, "clock_capture");
    auto observerReset = actionIndex(observerMetadata, "reset_capture");
    if (!observerClock || !observerReset || *observerClock >= observer->getNumOperands() ||
        *observerReset >= observer->getNumOperands()) return reject();
    DenseSet<std::pair<Operation *, uint64_t>> expectedSources, actualSources;
    SmallVector<Value, 0> events;
    auto module = rule->getParentOfType<ModuleOp>();
    for (auto producer : module.getBody().front().getOps<RuleOp>()) {
        if (failed(budget.debit(1, rule))) return failure();
        auto metadata = producer->getAttrOfType<DictionaryAttr>("ac.sampled_admission");
        auto exports = metadata ? metadata.getAs<ArrayAttr>("actions") : ArrayAttr();
        if (!exports) continue;
        for (Attribute rawExport : exports) {
            if (failed(budget.debit(16, rule))) return failure();
            auto output = dyn_cast<DictionaryAttr>(rawExport);
            if (!output || output.get("action") != action) continue;
            auto result = actionIndex(output, "active");
            if (!result || *result >= producer->getNumResults() ||
                !expectedSources.insert({producer, *result}).second) return reject();
            events.push_back(producer->getResult(*result));
        }
    }
    unsigned cursor = forward ? 1 : 0;
    if (forward) {
        if (failed(verifyForwardOldQ(rule->getOperand(0), view.getAs<DictionaryAttr>("state"), observer, analysis, budget))) return failure();
        proof.uses.insert(&rule->getOpOperand(0));
    }
    for (Attribute raw : sources) {
        if (failed(budget.debit(48, rule))) return failure();
        auto source = dyn_cast<DictionaryAttr>(raw);
        if (!exactActionFields(source, active ? std::initializer_list<StringRef>{"registration", "active"}
                    : forward ? std::initializer_list<StringRef>{"registration", "active", "forward"}
                              : std::initializer_list<StringRef>{"registration", "active", "argument"})) return reject();
        auto endpoint = dyn_cast<OpResult>(rule->getOperand(cursor));
        auto producer = endpoint ? dyn_cast<RuleOp>(endpoint.getOwner()) : RuleOp();
        auto metadata = producer ? producer->getAttrOfType<DictionaryAttr>("ac.sampled_admission") : DictionaryAttr();
        auto exports = metadata ? metadata.getAs<ArrayAttr>("actions") : ArrayAttr();
        auto result = actionIndex(source, "active");
        auto clock = actionIndex(metadata, "clock_capture");
        auto reset = actionIndex(metadata, "reset_capture");
        if (!producer || producer == observer || producer->getParentOp() != rule->getParentOp() ||
            !exports || !result || !clock || !reset || *clock >= producer->getNumOperands() ||
            *reset >= producer->getNumOperands() || endpoint.getResultNumber() != *result ||
            producer->getAttr("occurrence") != source.get("registration") ||
            failed(verifyActionDomains(producer, observer, analysis, budget))) return reject();
        DictionaryAttr matching;
        for (Attribute rawExport : exports) {
            if (failed(budget.debit(1, rule))) return failure();
            auto output = dyn_cast<DictionaryAttr>(rawExport);
            auto index = actionIndex(output, "active");
            if (index && *index == *result && output.get("action") == action) {
                if (matching) return reject();
                matching = output;
            }
        }
        if (!matching) return reject();
        if (!actualSources.insert({producer, *result}).second) return reject();
        proof.uses.insert(&rule->getOpOperand(cursor++));
        if (!active) {
            auto index = actionIndex(source, forward ? "forward" : "argument");
            if (!index || *index >= producer->getNumResults() ||
                rule->getOperand(cursor) != producer->getResult(*index)) return reject();
            auto arguments = matching.getAs<ArrayAttr>(forward ? "forwards" : "arguments");
            if (!arguments) return reject();
            bool found = false;
            for (Attribute rawArgument : arguments) {
                if (failed(budget.debit(1, rule))) return failure();
                auto field = dyn_cast<DictionaryAttr>(rawArgument);
                auto number = actionIndex(field, "result");
                found |= number && *number == *index && (forward ?
                    (field.get("state") == view.get("state") && field.get("fields") == view.get("fields")) :
                    field.getAs<StringAttr>("name") == argument);
            }
            if (!found) return reject();
            proof.uses.insert(&rule->getOpOperand(cursor++));
        }
    }
    if (actualSources.size() != expectedSources.size()) return reject();
    if (action.get("registration") && expectedSources.size() != 1) return reject();
    for (const auto &source : expectedSources)
        if (!actualSources.contains(source)) return reject();
    if (events.size() > 1) {
        ActionGrantProof grants(module, analysis, budget);
        for (uint64_t i = 0; i < events.size(); ++i)
            for (uint64_t j = 0; j < i; ++j) {
                auto disjoint = grants.disjoint(events[i], events[j]);
                if (failed(disjoint)) return failure();
                if (!*disjoint) return rule.emitOpError()
                    << "action view requires mutually exclusive actual source events";
            }
    }
    Value value = yield.getValues().front();
    for (uint64_t i = sources.size(); i-- > 0;) {
        if (failed(budget.debit(8, rule))) return failure();
        auto operation = value.getDefiningOp();
        if (!operation || operation->getBlock() != &body) return reject();
        Value condition = body.getArgument(unsigned(forward) + i * (active ? 1 : 2));
        if (active) {
            auto join = dyn_cast<BitsBinaryOp>(operation);
            if (!join || join.getOpcode() != "or" || join.getRhs() != condition) return reject();
            value = join.getLhs();
        } else {
            Value payload = body.getArgument(unsigned(forward) + 2 * i + 1);
            if (auto select = dyn_cast<BitsSelectOp>(operation)) {
                if (select->getOperand(0) != condition || select->getOperand(1) != payload) return reject();
                value = select->getOperand(2);
            } else if (auto merge = dyn_cast<ValueMergeOp>(operation)) {
                auto paths = merge.getPaths();
                auto path = paths.size() == 1 ? dyn_cast<ArrayAttr>(paths[0]) : ArrayAttr();
                if (merge->getNumOperands() != 3 || merge->getOperand(1) != condition ||
                    merge->getOperand(2) != payload || !path ||
                    !path.empty() || !merge->getResult(1).use_empty()) return reject();
                value = merge->getOperand(0);
            } else return reject();
        }
        proof.operations.insert(operation);
    }
    std::function<LogicalResult(Value, unsigned)> zero = [&](Value value, unsigned depth) {
        if (depth > 128 || failed(budget.debit(4, rule))) return failure();
        auto operation = value.getDefiningOp();
        if (!operation || operation->getBlock() != &body) return failure();
        proof.operations.insert(operation);
        if (auto literal = dyn_cast<BitsConstantOp>(operation)) {
            auto evaluated = analysis.evaluateStatic(literal.getValue(), {}, literal);
            auto integer = succeeded(evaluated) ? dyn_cast<MathIntAttr>(*evaluated) : MathIntAttr();
            return success(integer && integer.getCanonicalValue() == "0");
        }
        if (!isa<StructCreateOp>(operation)) return failure();
        for (Value field : operation->getOperands())
            if (failed(zero(field, depth + 1))) return failure();
        return success();
    };
    if (forward) {
        auto fields = view.getAs<ArrayAttr>("fields");
        for (Attribute field : llvm::reverse(fields)) {
            if (failed(budget.debit(16, rule))) return failure();
            auto get = value.getDefiningOp<StructGetOp>();
            if (!get || get->getBlock() != &body || get.getFieldAttr() != field) return reject();
            proof.operations.insert(get); value = get.getValue();
        }
        if (value != body.getArgument(0)) return reject();
    } else if (failed(zero(value, 0))) return reject();
    for (Operation &operation : body)
        if (!proof.operations.contains(&operation)) return reject();
    return proof;
}
}
