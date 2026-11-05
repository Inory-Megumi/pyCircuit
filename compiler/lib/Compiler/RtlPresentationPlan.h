// Read-only presentation planning, adapted from the archlab 2026-11-03 design.
// Identity, dependencies and sharing come from verified IR, never RTL text.
#ifndef PYCIRCUIT_RTL_PRESENTATION_PLAN_H
#define PYCIRCUIT_RTL_PRESENTATION_PLAN_H

#include "FinalCppNames.h"
#include "HardwareEmitCommon.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/JSON.h"
#include <map>

namespace acir::compiler {
class RtlPresentationPlan {
public:
    struct Node {
        mlir::Value value;
        llvm::SmallVector<unsigned> inputs, consumers;
        std::string name, hint, rendering, disposition;
        ac::RuleOp rule;
        unsigned uses = 0, cost = 1;
        unsigned domain = 15, constant = 4;
        mlir::Value replacement;
        bool live = false, root = false, terminal = false, local = false;
        bool oneBit = false;
        bool authored = false, indexed = false, literal = false, inlineValue = false;
        unsigned representative = 0;
    };
    struct Check {
        mlir::Value condition, path;
        bool pathUnknown = true, conditionUnknown = true, pathAlwaysOne = false;
        bool needed() const { return pathUnknown || conditionUnknown; }
    };

    RtlPresentationPlan(HardwareEmitContext &context, ac::ModuleOp module)
        : context(context), module(module) {}

    void recordStorage(llvm::json::Object row) {
        storage.push_back(std::move(row));
    }

    mlir::Value canonical(mlir::Value value) {
        llvm::SmallVector<mlir::Value> path;
        while (true) {
            if (auto found = aliases.find(value); found != aliases.end()) {
                value = found->second;
                break;
            }
            path.push_back(value);
            if (auto argument = mlir::dyn_cast<mlir::BlockArgument>(value)) {
                if (auto rule = mlir::dyn_cast<ac::RuleOp>(argument.getOwner()->getParentOp())) {
                    value = rule.getCaptures()[argument.getArgNumber()];
                    continue;
                }
            } else if (auto rule = value.getDefiningOp<ac::RuleOp>()) {
                value = mlir::cast<ac::YieldOp>(rule.getBody().front().back())
                            .getValues()[mlir::cast<mlir::OpResult>(value).getResultNumber()];
                continue;
            }
            if (auto extract = value.getDefiningOp<ac::BitsExtractOp>()) {
                auto low = context.staticRtlValue(extract.getLow(), extract);
                if (mlir::succeeded(low) && *low == "0" && sameWidth(extract.getInput(), value)) {
                    value = extract.getInput();
                    continue;
                }
            }
            if (auto resize = value.getDefiningOp<ac::BitsResizeOp>()) {
                if (sameWidth(resize.getInput(), value)) {
                    value = resize.getInput();
                    continue;
                }
            }
            break;
        }
        for (auto alias : path) aliases.try_emplace(alias, value);
        if (normalized) {
            auto found = ids.find(value);
            if (found != ids.end()) value = nodes[nodes[found->second].representative].value;
        }
        return value;
    }

    mlir::LogicalResult prepare() {
        for (auto argument : module.getBody().front().getArguments()) add(argument);
        module.walk([&](mlir::Operation *op) {
            if (auto rule = mlir::dyn_cast<ac::RuleOp>(op)) rules.push_back(rule);
            for (auto value : op->getResults()) add(value);
        });
        for (unsigned id = 0; id < nodes.size(); ++id) {
            auto value = nodes[id].value;
            auto *op = value.getDefiningOp();
            if (!op) continue;
            if (mlir::isa<ac::InstanceOp, ac::CollectionOp>(op)) {
                nodes[id].terminal = true;
                continue;
            }
            auto operands = op->getOperands();
            if (mlir::isa<ac::DWireOp>(op)) operands = operands.drop_front(2);
            if (mlir::isa<ac::ValueRequireOp>(op)) operands = operands.drop_front();
            for (auto operand : operands) {
                auto input = add(operand);
                nodes[id].inputs.push_back(input);
                // Indexed/field syntax needs a signal, not an arbitrary expression.
                if ((!scalar(op) && !mlir::isa<ac::DWireOp, ac::ValueRequireOp>(op)) ||
                    mlir::isa<ac::BitsExtractOp>(op)) nodes[input].indexed = true;
            }
            for (auto &region : op->getRegions())
                for (auto &block : region)
                    if (auto yield = mlir::dyn_cast<ac::YieldOp>(block.getTerminator()))
                        for (auto value : yield.getValues()) {
                            auto input = add(value);
                            nodes[id].inputs.push_back(input);
                        }
        }
        auto root = [&](mlir::Value value) {
            auto id = add(value);
            nodes[id].root = true;
            roots.push_back(id);
        };
        for (auto value : mlir::cast<ac::YieldOp>(module.getBody().front().back()).getValues()) root(value);
        for (const auto &binding : context.sourceChecks().bindings) {
            if (binding.definition != module) continue;
            root(binding.condition);
            root(binding.path);
        }
        module.walk([&](mlir::Operation *op) {
            if (!mlir::isa<ac::InstanceOp, ac::CollectionOp>(op)) return;
            for (auto value : op->getOperands()) {
                root(value);
                if (mlir::isa<ac::CollectionOp>(op)) nodes[add(value)].indexed = true;
            }
            for (auto value : op->getResults()) root(value);
        });
        llvm::SmallVector<unsigned> pending(roots);
        while (!pending.empty()) {
            auto id = pending.pop_back_val();
            if (nodes[id].live) continue;
            nodes[id].live = true;
            llvm::append_range(pending, nodes[id].inputs);
            // Structured emitters materialize all sibling results together.
            if (auto *op = nodes[id].value.getDefiningOp())
                if (!scalar(op))
                    for (auto sibling : op->getResults()) pending.push_back(add(sibling));
        }
        for (auto id : roots) ++nodes[id].uses;
        for (unsigned id = 0; id < nodes.size(); ++id) {
            if (!nodes[id].live) continue;
            for (auto input : nodes[id].inputs) {
                ++nodes[input].uses;
                nodes[input].consumers.push_back(id);
            }
        }
        // Prefer actual state/wire identities before derived use-role names.
        module.walk([&](mlir::Operation *op) {
            if (auto wire = mlir::dyn_cast<ac::DWireOp>(op)) {
                hint(wire.getQ(), wire.getInstanceName(), true);
                nodes[add(wire.getQ())].rule = ruleOf(wire.getEnable());
                hint(wire.getData(), wire.getInstanceName().str() + "_value");
                hint(wire.getEnable(), wire.getInstanceName().str() + "_write");
            }
            if (!mlir::isa<ac::InstanceOp, ac::CollectionOp>(op)) return;
            auto *callee = mlir::isa<ac::InstanceOp>(op)
                ? context.analysis.resolveCallee(mlir::cast<ac::InstanceOp>(op))
                : context.analysis.resolveCallee(mlir::cast<ac::CollectionOp>(op));
            auto kind = context.analysis.getPrimitiveKind(callee);
            auto owner = op->getAttrOfType<mlir::StringAttr>("instance_name").getValue();
            auto outputs = callee->getAttrOfType<mlir::ArrayAttr>("output_names");
            for (auto [i, value] : llvm::enumerate(op->getResults()))
                hint(value, kind == "dff" || kind == "dffe" ? owner.str()
                    : owner.str() + "_" + mlir::cast<mlir::StringAttr>(outputs[i]).getValue().str(), true);
            if (kind == "dff" || kind == "dffe") {
                hint(op->getOperand(kind == "dff" ? 2 : 3), owner.str() + "_next");
                if (kind == "dffe") hint(op->getOperand(2), owner.str() + "_write");
            }
        });
        // A bottom-up worklist bounds expression expansion. Coupled field DAGs
        // may contain whole-value cycles; leave those nodes materialized.
        llvm::SmallVector<unsigned> remaining(nodes.size()), ready;
        for (unsigned id = 0; id < nodes.size(); ++id) {
            remaining[id] = nodes[id].inputs.size();
            if (nodes[id].live && !remaining[id]) ready.push_back(id);
        }
        for (unsigned cursor = 0; cursor < ready.size(); ++cursor) {
            auto id = ready[cursor];
            auto &node = nodes[id];
            auto *op = node.value.getDefiningOp();
            node.literal = op && mlir::isa<ac::BitsConstantOp, ac::BitsConstant4Op>(op);
            facts(id);
            node.literal |= node.constant < 4;
            for (auto consumer : node.consumers)
                if (--remaining[consumer] == 0) ready.push_back(consumer);
        }
        normalize();
        for (bool authored : {true, false}) {
            for (auto [id, node] : llvm::enumerate(nodes)) {
                if (!node.live || node.representative != id || node.authored != authored) continue;
                if (auto argument = mlir::dyn_cast<mlir::BlockArgument>(node.value);
                    argument && argument.getOwner()->getParentOp() == module) {
                    auto name = context.rtlPortName(module, false, argument.getArgNumber());
                    if (mlir::failed(name)) return mlir::failure();
                    node.name = *name;
                    continue;
                }
                std::string label = node.hint;
                if (label.empty()) {
                    auto *op = node.value.getDefiningOp();
                    label = op ? operationName(op) : "element_argument";
                    if (node.rule) label = node.rule.getName().str() + "_" + label;
                }
                auto name = context.rtlIdentifier(label, module);
                if (mlir::failed(name)) return mlir::failure();
                node.name = context.rtlGeneratedName(module, "value:" + std::to_string(id), *name);
            }
        }
        return mlir::success();
    }

    Node &get(mlir::Value value) { return nodes[ids.lookup(canonical(value))]; }
    const Check &check(unsigned ordinal) const { return checks.find(ordinal)->second; }
    void recordInitializer(mlir::Value source, llvm::StringRef name) {
        initializerNames[source] = name.str();
    }
    void record(mlir::Value value, llvm::StringRef rendering, llvm::StringRef disposition) {
        auto &node = get(value);
        node.rendering = rendering.str();
        node.disposition = disposition.str();
    }
    void declare(llvm::StringRef text) { declarations += text; }
    void statement(mlir::Value value, llvm::StringRef text) {
        auto rule = get(value).rule;
        statements[rule ? rule.getOperation() : nullptr] += text;
    }
    void emit(llvm::raw_ostream &out) {
        out << "\n  // Signals (source names and derived use roles)\n" << declarations;
        if (auto found = statements.find(nullptr); found != statements.end())
            out << "\n  // Shared combinational logic\n" << found->second;
        for (auto rule : rules) {
            auto found = statements.find(rule);
            if (found == statements.end()) continue;
            out << "\n  // Rule " << comment(rule.getName()) << " -- " << comment(location(rule.getLoc())) << "\n";
            out << found->second;
        }
    }
    llvm::json::Object mapping() {
        llvm::json::Array values;
        for (auto [id, node] : llvm::enumerate(nodes)) {
            if (node.representative != id) {
                const auto &target = nodes[node.representative];
                node.name = target.name;
                node.rendering = target.rendering;
                node.disposition = "alias";
            }
            llvm::json::Array consumers;
            for (auto consumer : node.consumers) consumers.push_back(consumer);
            llvm::json::Object row{{"id", id}, {"name", node.name},
                {"rendering", node.rendering}, {"disposition", node.disposition.empty() ? "elided" : node.disposition},
                {"source", location(node.value.getLoc())}, {"uses", node.uses},
                {"source_locations", sourceLocations(node.value.getLoc())},
                {"consumers", std::move(consumers)}, {"expression_cost", node.cost}};
            row["representative"] = node.representative;
            if (!node.hint.empty()) row["role"] = node.hint;
            if (auto *op = node.value.getDefiningOp()) row["operation"] = op->getName().getStringRef().str();
            if (node.rule) {
                row["rule"] = node.rule.getName().str();
                std::string identity;
                llvm::raw_string_ostream stream(identity);
                node.rule.getOccurrence().print(stream);
                row["rule_occurrence"] = identity;
            }
            values.push_back(std::move(row));
        }
        llvm::json::Array origins, checkRows, initializers;
        for (auto [id, source] : llvm::enumerate(sourceValues)) {
            auto target = ids.lookup(canonical(source));
            llvm::json::Object origin{{"id", id}, {"value", target},
                {"source", location(source.getLoc())}, {"source_locations", sourceLocations(source.getLoc())}};
            if (auto *op = source.getDefiningOp()) origin["operation"] = op->getName().getStringRef().str();
            origins.push_back(std::move(origin));
            if (auto found = initializerNames.find(source); found != initializerNames.end())
                initializers.push_back(llvm::json::Object{{"source_value", id}, {"name", found->second}});
        }
        for (auto [ordinal, binding] : llvm::enumerate(context.sourceChecks().bindings)) {
            if (binding.definition != module) continue;
            const auto &plan = check(ordinal);
            checkRows.push_back(llvm::json::Object{{"ordinal", ordinal},
                {"condition", ids.lookup(canonical(plan.condition))},
                {"path", ids.lookup(canonical(plan.path))},
                {"disposition", plan.needed() ? "runtime" : "proven-zero"}});
        }
        return llvm::json::Object{{"definition", module.getSymName().str()},
            {"rtl_module", context.names(module).rtl}, {"rtl_file", context.names(module).verilog},
            {"values", std::move(values)}, {"source_values", std::move(origins)},
            {"checks", std::move(checkRows)}, {"initializers", std::move(initializers)},
            {"storage", std::move(storage)}};
    }

private:
    HardwareEmitContext &context;
    ac::ModuleOp module;
    llvm::DenseMap<mlir::Value, mlir::Value> aliases;
    llvm::DenseMap<mlir::Value, unsigned> ids;
    llvm::SmallVector<Node, 0> nodes;
    llvm::SmallVector<unsigned> roots;
    llvm::SmallVector<ac::RuleOp> rules;
    llvm::DenseSet<mlir::Value> seenSources;
    llvm::SmallVector<mlir::Value> sourceValues;
    llvm::DenseMap<unsigned, Check> checks;
    llvm::DenseMap<mlir::Value, std::string> initializerNames;
    llvm::json::Array storage;
    bool normalized = false;
    std::string declarations;
    std::map<mlir::Operation *, std::string> statements;

    void normalize() {
        // Proof identities stay in nodes/sourceValues; only the presentation
        // graph is quotiented. Replacement edges are proven input identities
        // in the acyclic part of the graph, so they cannot introduce cycles.
        for (auto &node : nodes)
            if (node.replacement && node.constant >= 4)
                node.representative = ids.lookup(canonical(node.replacement));
        auto representative = [&](unsigned id) {
            unsigned result = id;
            while (nodes[result].representative != result) result = nodes[result].representative;
            while (nodes[id].representative != id) {
                unsigned next = nodes[id].representative;
                nodes[id].representative = result;
                id = next;
            }
            return result;
        };
        for (unsigned id = 0; id < nodes.size(); ++id) {
            auto target = representative(id);
            auto &node = nodes[id], &result = nodes[target];
            if (target != id && !node.hint.empty() &&
                (result.hint.empty() || (node.authored && !result.authored))) {
                result.hint = node.hint;
                result.authored = node.authored;
            }
        }
        normalized = true;
        auto idOf = [&](mlir::Value value) { return ids.lookup(canonical(value)); };
        for (auto [id, node] : llvm::enumerate(nodes)) {
            node.live = node.root = node.indexed = node.inlineValue = false;
            node.uses = 0;
            node.cost = 1;
            node.consumers.clear();
            if (node.representative != id || node.literal) node.inputs.clear();
            else for (auto &input : node.inputs) input = nodes[input].representative;
        }
        roots.clear();
        auto root = [&](mlir::Value value) {
            auto id = idOf(value);
            nodes[id].root = true;
            roots.push_back(id);
        };
        for (auto value : mlir::cast<ac::YieldOp>(module.getBody().front().back()).getValues()) root(value);
        for (auto [ordinal, binding] : llvm::enumerate(context.sourceChecks().bindings)) {
            if (binding.definition != module) continue;
            auto &condition = nodes[idOf(binding.condition)], &path = nodes[idOf(binding.path)];
            Check plan{binding.condition, binding.path,
                !path.oneBit || bool(path.domain & 12),
                (!condition.oneBit || bool(condition.domain & 12)) && (!path.oneBit || bool(path.domain & 2)),
                path.oneBit && path.domain == 2};
            checks.try_emplace(ordinal, plan);
            if (plan.pathUnknown || (plan.conditionUnknown && !plan.pathAlwaysOne)) root(plan.path);
            if (plan.conditionUnknown) root(plan.condition);
        }
        module.walk([&](mlir::Operation *op) {
            if (!mlir::isa<ac::InstanceOp, ac::CollectionOp>(op)) return;
            for (auto value : op->getOperands()) {
                root(value);
                if (mlir::isa<ac::CollectionOp>(op)) nodes[idOf(value)].indexed = true;
            }
            for (auto value : op->getResults()) root(value);
        });
        llvm::SmallVector<unsigned> pending(roots);
        while (!pending.empty()) {
            auto id = pending.pop_back_val();
            auto &node = nodes[id];
            if (node.live) continue;
            node.live = true;
            llvm::append_range(pending, node.inputs);
            auto *op = node.value.getDefiningOp();
            if (!op || node.literal || mlir::isa<ac::InstanceOp, ac::CollectionOp>(op)) continue;
            if ((!scalar(op) && !mlir::isa<ac::DWireOp, ac::ValueRequireOp>(op)) || mlir::isa<ac::BitsExtractOp>(op))
                for (auto operand : op->getOperands()) nodes[idOf(operand)].indexed = true;
            if (!scalar(op))
                for (auto sibling : op->getResults()) pending.push_back(idOf(sibling));
        }
        for (auto id : roots) ++nodes[id].uses;
        for (auto [id, node] : llvm::enumerate(nodes)) {
            if (!node.live) continue;
            for (auto input : node.inputs) {
                ++nodes[input].uses;
                nodes[input].consumers.push_back(id);
            }
        }
        llvm::SmallVector<unsigned> remaining(nodes.size()), ready;
        for (auto [id, node] : llvm::enumerate(nodes)) {
            remaining[id] = node.inputs.size();
            if (node.live && !remaining[id]) ready.push_back(id);
        }
        for (unsigned cursor = 0; cursor < ready.size(); ++cursor) {
            auto id = ready[cursor];
            auto &node = nodes[id];
            auto *op = node.value.getDefiningOp();
            for (auto input : node.inputs)
                node.cost = std::min(13u, node.cost + (nodes[input].inlineValue ? nodes[input].cost : 1));
            node.inlineValue = op && scalar(op) && !node.indexed && !node.terminal &&
                mlir::isa<ac::BitsType>(node.value.getType()) &&
                (node.literal || (node.hint.empty() && !node.root && !mlir::isa<ac::BitsSelectOp>(op) && node.uses == 1 && node.cost <= 12 &&
                    llvm::all_of(node.consumers, [&](unsigned consumer) { return nodes[consumer].rule == node.rule; })));
            for (auto consumer : node.consumers)
                if (--remaining[consumer] == 0) ready.push_back(consumer);
        }
    }

    unsigned add(mlir::Value raw) {
        if (seenSources.insert(raw).second) sourceValues.push_back(raw);
        auto value = canonical(raw);
        auto [found, inserted] = ids.try_emplace(value, nodes.size());
        if (inserted) {
            Node node;
            node.representative = found->second;
            node.value = value;
            node.terminal = mlir::isa<mlir::BlockArgument>(value);
            auto *owner = value.getParentRegion()->getParentOp();
            node.local = !mlir::isa<ac::ModuleOp, ac::RuleOp>(owner);
            node.rule = ruleOf(value);
            if (mlir::isa<ac::BitsType>(value.getType())) {
                auto width = context.payloadWidth(value.getType(), module, true);
                node.oneBit = mlir::succeeded(width) && *width == "1";
            }
            nodes.push_back(std::move(node));
        }
        return found->second;
    }
    ac::RuleOp ruleOf(mlir::Value value) {
        if (auto *op = canonical(value).getDefiningOp()) return op->getParentOfType<ac::RuleOp>();
        return {};
    }
    void hint(mlir::Value value, llvm::StringRef label, bool authored = false) {
        auto &node = nodes[add(value)];
        if (node.hint.empty() || (authored && !node.authored)) node.hint = label.str();
        node.authored |= authored;
    }
    bool sameWidth(mlir::Value input, mlir::Value output) {
        auto a = mlir::dyn_cast<ac::BitsType>(input.getType());
        auto b = mlir::dyn_cast<ac::BitsType>(output.getType());
        if (!a || !b || !context.isClosedStatic(a.getWidth()) || !context.isClosedStatic(b.getWidth())) return false;
        auto x = context.payloadWidth(a, module, true), y = context.payloadWidth(b, module, true);
        return mlir::succeeded(x) && mlir::succeeded(y) && *x == *y;
    }
    // Finite four-state facts; no assumptions about valid clocks or guards.
    // Z is distinct from X for wires, case equality and conditional merging.
    static unsigned evaluate(llvm::StringRef op, unsigned a, unsigned b, unsigned c) {
        if (op == "not") return a < 2 ? 1 - a : 2;
        if (op == "and") return a == 0 || b == 0 ? 0 : a == 1 && b == 1 ? 1 : 2;
        if (op == "or") return a == 1 || b == 1 ? 1 : a == 0 && b == 0 ? 0 : 2;
        if (op == "xor") return a < 2 && b < 2 ? a ^ b : 2;
        if (op == "case_eq") return a == b;
        if (op == "eq" || op == "ne") return a < 2 && b < 2 ? unsigned((a == b) == (op == "eq")) : 2;
        return a == 1 ? b : a == 0 ? c : b == c ? b : 2;
    }
    void facts(unsigned id) {
        auto &node = nodes[id];
        if (!node.oneBit) return;
        auto *op = node.value.getDefiningOp();
        if (!op) return;
        if (auto constant = mlir::dyn_cast<ac::BitsConstantOp>(op)) {
            if (context.isClosedStatic(constant.getValue())) {
                auto value = context.staticRtlValue(constant.getValue(), op);
                if (mlir::succeeded(value) && (*value == "0" || *value == "1")) node.constant = *value == "1";
            }
        } else if (auto pattern = mlir::dyn_cast<ac::BitsConstant4Op>(op)) {
            auto bit = pattern.getPattern().front();
            node.constant = bit == '0' ? 0 : bit == '1' ? 1 : bit == 'z' ? 3 : 2;
        }
        if (node.constant < 4) {
            node.domain = 1u << node.constant;
            return;
        }
        std::string operation;
        if (auto binary = mlir::dyn_cast<ac::BitsBinaryOp>(op)) operation = binary.getOpcode().str();
        if (auto unary = mlir::dyn_cast<ac::BitsUnaryOp>(op)) operation = unary.getOpcode().str();
        if (auto compare = mlir::dyn_cast<ac::BitsCompareOp>(op)) {
            operation = compare.getPredicate().str();
            node.domain = operation == "case_eq" ? 3 : 7;
        }
        if (mlir::isa<ac::BitsSelectOp>(op)) operation = "select";
        if (operation != "not" && operation != "and" && operation != "or" && operation != "xor" &&
            operation != "case_eq" && operation != "eq" && operation != "ne" && operation != "select") return;
        if (node.inputs.empty() || node.inputs.size() > 3 ||
            !llvm::all_of(node.inputs, [&](unsigned input) { return nodes[input].oneBit; })) return;
        unsigned domains[3] = {1, 1, 1};
        for (auto [slot, input] : llvm::enumerate(node.inputs)) domains[slot] = nodes[input].domain;
        node.domain = 0;
        unsigned aliases = (1u << node.inputs.size()) - 1;
        for (unsigned a = 0; a < 4; ++a) for (unsigned b = 0; b < 4; ++b) for (unsigned c = 0; c < 4; ++c) {
            if (!(domains[0] & (1u << a)) || !(domains[1] & (1u << b)) || !(domains[2] & (1u << c))) continue;
            unsigned values[3] = {a, b, c};
            bool possible = true;
            for (unsigned i = 0; i < node.inputs.size(); ++i)
                for (unsigned j = 0; j < i; ++j)
                    if (node.inputs[i] == node.inputs[j] && values[i] != values[j]) possible = false;
            if (!possible) continue;
            auto result = evaluate(operation, a, b, c);
            node.domain |= 1u << result;
            for (unsigned i = 0; i < node.inputs.size(); ++i)
                if (result != values[i]) aliases &= ~(1u << i);
        }
        for (unsigned bit = 0; bit < 4; ++bit) if (node.domain == (1u << bit)) node.constant = bit;
        for (unsigned i = 0; i < node.inputs.size(); ++i)
            if (aliases & (1u << i)) { node.replacement = nodes[node.inputs[i]].value; break; }
    }
    static bool scalar(mlir::Operation *op) {
        if (auto binary = mlir::dyn_cast<ac::BitsBinaryOp>(op))
            return binary.getOpcode() != "udiv" && binary.getOpcode() != "urem";
        return mlir::isa<ac::BitsConstantOp, ac::BitsConstant4Op, ac::BitsUnaryOp,
            ac::BitsCompareOp, ac::BitsSelectOp, ac::BitsExtractOp, ac::BitsResizeOp,
            ac::BitsConcatOp>(op);
    }
    static std::string operationName(mlir::Operation *op) {
        if (auto binary = mlir::dyn_cast<ac::BitsBinaryOp>(op)) return binary.getOpcode().str();
        if (auto compare = mlir::dyn_cast<ac::BitsCompareOp>(op)) return compare.getPredicate().str();
        std::string name = op->getName().getStringRef().str();
        if (llvm::StringRef(name).starts_with("ac.bits.")) name.erase(0, 8);
        else if (llvm::StringRef(name).starts_with("ac.")) name.erase(0, 3);
        std::replace(name.begin(), name.end(), '.', '_');
        return name;
    }
    static std::string comment(llvm::StringRef text) {
        std::string result;
        for (unsigned char c : text) result += c >= 32 && c < 127 && c != '\\' ? char(c) : '_';
        return result;
    }
    static std::string location(mlir::Location loc) {
        std::string result;
        llvm::raw_string_ostream out(result);
        loc.print(out);
        return result;
    }
    static llvm::json::Array sourceLocations(mlir::Location loc) {
        llvm::json::Array result;
        llvm::SmallVector<mlir::Location> pending{loc};
        llvm::DenseSet<mlir::Location> seen;
        while (!pending.empty()) {
            auto current = pending.pop_back_val();
            if (!seen.insert(current).second) continue;
            if (auto file = mlir::dyn_cast<mlir::FileLineColLoc>(current))
                result.push_back(llvm::json::Object{{"file", file.getFilename().str()},
                    {"line", file.getLine()}, {"column", file.getColumn()}});
            else if (auto fused = mlir::dyn_cast<mlir::FusedLoc>(current))
                llvm::append_range(pending, fused.getLocations());
            else if (auto name = mlir::dyn_cast<mlir::NameLoc>(current)) pending.push_back(name.getChildLoc());
            else if (auto call = mlir::dyn_cast<mlir::CallSiteLoc>(current)) {
                pending.push_back(call.getCaller());
                pending.push_back(call.getCallee());
            }
        }
        return result;
    }
};
} // namespace acir::compiler
#endif
