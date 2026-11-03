// A read-only, typed presentation graph. No decision depends on rendered text.
#ifndef PYCIRCUIT_RTL_PRESENTATION_PLAN_H
#define PYCIRCUIT_RTL_PRESENTATION_PLAN_H

#include "mlir/IR/Value.h"
#include "mlir/Support/LogicalResult.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/JSON.h"
#include <algorithm>
#include <functional>
#include <limits>
#include <map>
#include <optional>
#include <string>

namespace acir::compiler {

class RtlPresentationPlan {
public:
    struct Hooks {
        std::function<mlir::Value(mlir::Value)> canonical;
        std::function<llvm::SmallVector<mlir::Value>(mlir::Value)> inputs;
        std::function<llvm::SmallVector<mlir::Value>(mlir::Value)> companions;
        std::function<bool(mlir::Value)> terminal, oneBit, inlineable, authored;
        std::function<unsigned(mlir::Value)> literal;
        std::function<std::string(mlir::Value)> operation, kind;
        std::function<std::string(mlir::Value, unsigned)> inputRole;
    };
    struct View {
        mlir::Value value;
        unsigned domain = 15, literal = 4;
    };
    struct Root {
        mlir::Value value;
        std::string label, scope;
    };
    struct Description {
        std::string anchor, scope;
        mlir::Attribute owner;
        std::string rootScope;
        unsigned rank = 0;
        bool sharedOwner = false;
    };
    struct Node {
        mlir::Value value;
        llvm::SmallVector<unsigned> inputs, consumers;
        llvm::SmallVector<std::string> inputRoles;
        View view;
        std::string operation, kind, anchor, scope, label;
        mlir::Attribute owner;
        std::string rootScope;
        unsigned anchorRank = 0;
        unsigned uses = 0, cost = 1, rhsCost = 1, context = 0;
        bool terminal = false, oneBit = false, live = false, inlineable = false;
        bool inlineExpression = false, sharedContext = false, emitted = false;
        bool explicitOwner = false, sharedOwner = false, coupledFields = false;
        bool sharedScope = false;
    };

private:
    Hooks hooks;
    llvm::DenseMap<mlir::Value, unsigned> ids;
    llvm::SmallVector<Node, 0> nodes;
    llvm::SmallVector<unsigned> order;
    llvm::SmallVector<Root> runtimeRoots;
    llvm::DenseSet<mlir::Value> unknownEmissions;
    bool prepared = false, censused = false, planned = false;
    static constexpr unsigned shared = std::numeric_limits<unsigned>::max();

    unsigned add(mlir::Value raw) {
        auto value = hooks.canonical(raw);
        auto [found, inserted] = ids.try_emplace(value, nodes.size());
        if (!inserted) return found->second;
        Node node;
        node.value = value;
        node.view.value = value;
        node.terminal = hooks.terminal(value);
        node.oneBit = hooks.oneBit(value);
        node.inlineable = hooks.inlineable(value);
        node.operation = hooks.operation(value);
        node.kind = hooks.kind(value);
        nodes.push_back(std::move(node));
        return found->second;
    }

    static unsigned evaluate(llvm::StringRef op, llvm::ArrayRef<unsigned> bits) {
        unsigned a = bits[0], b = bits.size() > 1 ? bits[1] : 0;
        if (op == "not") return a < 2 ? 1 - a : 2;
        if (op == "and") return a == 0 || b == 0 ? 0 : a == 1 && b == 1 ? 1 : 2;
        if (op == "or") return a == 1 || b == 1 ? 1 : a == 0 && b == 0 ? 0 : 2;
        if (op == "xor") return a < 2 && b < 2 ? a ^ b : 2;
        if (op == "case_eq") return a == b;
        if (op == "eq" || op == "ne")
            return a < 2 && b < 2 ? unsigned((a == b) == (op == "eq")) : 2;
        if (op == "require") return b == 1 ? a : b == 0 ? 1 : a == 1 ? 1 : 2;
        unsigned c = bits[2];
        return a == 1 ? b : a == 0 ? c : b == c ? b : 2;
    }

    void facts(unsigned id) {
        auto &node = nodes[id];
        if (!node.oneBit) return;
        unsigned literal = hooks.literal(node.value);
        if (literal < 4) {
            node.view.domain = 1u << literal;
            node.view.literal = literal;
            return;
        }
        if (node.operation == "case_eq") node.view.domain = 3;
        if (node.operation == "eq" || node.operation == "ne") node.view.domain = 7;
        if (node.terminal || node.operation.empty() || node.inputs.empty() || node.inputs.size() > 3 ||
            !llvm::all_of(node.inputs, [&](unsigned input) { return nodes[input].oneBit; })) return;
        unsigned domain = 0, projections = (1u << node.inputs.size()) - 1;
        for (unsigned tuple = 0; tuple < (1u << (2 * node.inputs.size())); ++tuple) {
            llvm::SmallVector<unsigned, 3> bits;
            bool possible = true;
            for (auto [index, input] : llvm::enumerate(node.inputs)) {
                const auto &view = nodes[input].view;
                unsigned bit = (tuple >> (2 * index)) & 3;
                bits.push_back(bit);
                possible &= bool(view.domain & (1u << bit));
                for (unsigned earlier = 0; earlier < index; ++earlier) {
                    const auto &other = nodes[node.inputs[earlier]].view;
                    if (view.literal == 4 && other.literal == 4 && view.value == other.value)
                        possible &= bit == bits[earlier];
                }
            }
            if (!possible) continue;
            unsigned bit = evaluate(node.operation, bits);
            domain |= 1u << bit;
            for (unsigned index = 0; index < node.inputs.size(); ++index)
                if (bit != bits[index]) projections &= ~(1u << index);
        }
        node.view.domain = domain;
        if (hooks.authored(node.value)) return;
        if (domain && !(domain & (domain - 1))) {
            for (unsigned bit = 0; bit < 4; ++bit)
                if (domain == (1u << bit)) node.view.literal = bit;
        } else {
            for (unsigned index = 0; index < node.inputs.size(); ++index)
                if (projections & (1u << index)) { node.view = nodes[node.inputs[index]].view; break; }
        }
    }

    unsigned normalized(unsigned id) const {
        auto found = ids.find(nodes[id].view.value);
        return found == ids.end() ? id : found->second;
    }

    bool join(unsigned id, unsigned incoming) {
        auto &node = nodes[id];
        if (!node.anchor.empty()) incoming = id + 1;
        if (!incoming || node.context == shared || node.context == incoming) return false;
        node.context = !node.context ? incoming : shared;
        return true;
    }

    bool joinOwner(unsigned id, mlir::Attribute owner, llvm::StringRef scope, bool multiple) {
        auto &node = nodes[id];
        if (node.terminal || node.explicitOwner || node.sharedOwner || (!owner && !multiple)) return false;
        if (multiple || (node.owner && node.owner != owner)) {
            node.owner = {}; node.rootScope.clear(); node.sharedOwner = true; return true;
        }
        if (node.owner) return false;
        node.owner = owner; node.rootScope = scope.str(); return true;
    }

public:
    // All walks use explicit stacks. Graph size, rather than recursion depth or
    // a pattern-search budget, determines complete coverage of accepted IR.
    mlir::LogicalResult analyze(llvm::ArrayRef<mlir::Value> values, Hooks queries) {
        hooks = std::move(queries);
        for (auto raw : values) add(raw);
        for (unsigned id = 0; id < nodes.size(); ++id) {
            if (nodes[id].terminal) continue;
            auto inputs = hooks.inputs(nodes[id].value);
            llvm::SmallVector<unsigned> indices;
            for (auto input : inputs) indices.push_back(add(input));
            nodes[id].inputs = std::move(indices);
            for (unsigned slot = 0; slot < inputs.size(); ++slot)
                nodes[id].inputRoles.push_back(hooks.inputRole(nodes[id].value, slot));
        }
        // Common verification is field-sensitive. A legal record can read a
        // different field of itself, so whole-value SCCs are layout clusters,
        // not evidence of a hardware cycle. Condense them without changing IR.
        struct Frame { unsigned id, next = 0; };
        llvm::SmallVector<bool, 0> visited(nodes.size(), false);
        llvm::SmallVector<unsigned> finished;
        llvm::SmallVector<llvm::SmallVector<unsigned, 2>, 0> reverse(nodes.size());
        for (unsigned id = 0; id < nodes.size(); ++id)
            for (unsigned input : nodes[id].inputs) reverse[input].push_back(id);
        for (unsigned root = 0; root < nodes.size(); ++root) {
            if (visited[root]) continue;
            visited[root] = true;
            llvm::SmallVector<Frame> stack{{root}};
            while (!stack.empty()) {
                unsigned id = stack.back().id;
                if (stack.back().next < nodes[id].inputs.size()) {
                    unsigned input = nodes[id].inputs[stack.back().next++];
                    if (!visited[input]) { visited[input] = true; stack.push_back({input}); }
                } else { finished.push_back(id); stack.pop_back(); }
            }
        }
        llvm::SmallVector<unsigned> component(nodes.size(), shared);
        llvm::SmallVector<llvm::SmallVector<unsigned, 2>, 0> groups;
        for (unsigned root : llvm::reverse(finished)) {
            if (component[root] != shared) continue;
            unsigned group = groups.size();
            groups.emplace_back();
            llvm::SmallVector<unsigned> pending{root};
            component[root] = group;
            while (!pending.empty()) {
                unsigned id = pending.pop_back_val();
                groups.back().push_back(id);
                for (unsigned next : reverse[id])
                    if (component[next] == shared) { component[next] = group; pending.push_back(next); }
            }
            llvm::sort(groups.back());
        }
        for (const auto &group : llvm::reverse(groups)) {
            bool coupled = group.size() > 1 || llvm::is_contained(nodes[group.front()].inputs, group.front());
            for (unsigned id : group) {
                order.push_back(id);
                nodes[id].coupledFields = coupled;
                if (!coupled) facts(id);
                else {
                    nodes[id].inlineable = false;
                    if (nodes[id].operation == "case_eq") nodes[id].view.domain = 3;
                    if (nodes[id].operation == "eq" || nodes[id].operation == "ne") nodes[id].view.domain = 7;
                }
            }
        }
        prepared = true;
        return mlir::success();
    }

    View view(mlir::Value raw) const {
        auto value = hooks.canonical(raw);
        auto found = ids.find(value);
        return found == ids.end() ? View{value} : nodes[found->second].view;
    }

    mlir::LogicalResult census(llvm::ArrayRef<Root> roots) {
        if (!prepared) return mlir::failure();
        if (censused) return mlir::success();
        llvm::SmallVector<unsigned> pending;
        for (const auto &root : roots) {
            auto found = ids.find(hooks.canonical(root.value));
            if (found == ids.end()) return mlir::failure();
            unsigned id = normalized(found->second);
            ++nodes[id].uses;
            pending.push_back(id);
            runtimeRoots.push_back({nodes[id].value, root.label, root.scope});
        }
        while (!pending.empty()) {
            unsigned id = pending.pop_back_val();
            auto &node = nodes[id];
            if (node.live) continue;
            node.live = true;
            // Some original multi-result operations print their complete typed
            // result bundle. Retaining that bundle creates no semantic use.
            for (auto sibling : hooks.companions(node.value)) {
                auto found = ids.find(hooks.canonical(sibling));
                if (found == ids.end()) return mlir::failure();
                pending.push_back(normalized(found->second));
            }
            if (node.view.literal < 4) continue;
            for (unsigned input : node.inputs) {
                input = normalized(input);
                ++nodes[input].uses;
                nodes[input].consumers.push_back(id);
                pending.push_back(input);
            }
        }
        censused = true;
        return mlir::success();
    }

    mlir::LogicalResult plan(const std::function<Description(mlir::Value)> &describe,
                            unsigned expressionLimit) {
        if (!censused) return mlir::failure();
        for (unsigned id : order) {
            auto description = describe(nodes[id].value);
            auto &node = nodes[normalized(id)];
            if (!description.anchor.empty() && (node.anchor.empty() || description.rank > node.anchorRank ||
                (description.rank == node.anchorRank && description.anchor < node.anchor))) {
                node.anchor = std::move(description.anchor);
                node.anchorRank = description.rank;
            }
            if (!description.scope.empty() && !node.sharedScope) {
                if (node.scope.empty()) node.scope = description.scope;
                else if (node.scope != description.scope) {
                    node.scope.clear(); node.sharedScope = true;
                }
            }
            if (description.owner || description.sharedOwner) {
                bool multiple = description.sharedOwner || node.sharedOwner || (node.owner && node.owner != description.owner);
                node.owner = multiple ? mlir::Attribute() : description.owner;
                node.sharedOwner = multiple;
                node.rootScope = multiple ? "" : description.rootScope;
                node.explicitOwner = true;
            }
        }
        llvm::SmallVector<unsigned> owners;
        for (unsigned id = 0; id < nodes.size(); ++id)
            if (nodes[id].live && (nodes[id].owner || nodes[id].sharedOwner)) owners.push_back(id);
        while (!owners.empty()) {
            unsigned id = owners.pop_back_val();
            if (nodes[id].view.literal < 4) continue;
            for (unsigned input : nodes[id].inputs) {
                input = normalized(input);
                if (joinOwner(input, nodes[id].owner, nodes[id].rootScope, nodes[id].sharedOwner)) owners.push_back(input);
            }
        }
        llvm::SmallVector<Description> contexts;
        for (const auto &node : nodes) contexts.push_back({node.anchor, node.scope});
        llvm::SmallVector<unsigned> work;
        for (unsigned id = 0; id < nodes.size(); ++id)
            if (nodes[id].live && !nodes[id].anchor.empty() && join(id, id + 1)) work.push_back(id);
        for (const auto &root : runtimeRoots) {
            unsigned id = normalized(ids.lookup(root.value));
            contexts.push_back({root.label, root.scope});
            if (join(id, contexts.size())) work.push_back(id);
        }
        // Typed aggregate slots are semantic edges, not an opcode search from
        // each constructor. Contexts form a finite lattice; each node changes
        // from absent to unique to shared, never back to a chosen consumer.
        std::map<std::pair<unsigned, std::string>, unsigned> relatedContexts;
        while (!work.empty()) {
            unsigned id = work.pop_back_val();
            if (nodes[id].view.literal < 4) continue;
            for (auto [slot, raw] : llvm::enumerate(nodes[id].inputs)) {
                unsigned input = raw;
                input = normalized(input);
                unsigned context = nodes[id].context;
                const auto &part = nodes[id].inputRoles[slot];
                if (context && context != shared && !part.empty() && !nodes[id].coupledFields) {
                    auto [found, inserted] = relatedContexts.try_emplace({context, part}, contexts.size() + 1);
                    if (inserted) {
                        auto base = contexts[context - 1];
                        base.anchor += "_" + part;
                        contexts.push_back(std::move(base));
                    }
                    context = found->second;
                }
                if (join(input, context)) work.push_back(input);
            }
        }
        for (unsigned id : order) {
            auto &node = nodes[id];
            if (!node.live) continue;
            node.sharedContext = node.context == shared;
            if (node.scope.empty() && node.owner) node.scope = node.rootScope;
            if (!node.anchor.empty()) node.label = node.anchor;
            else if (node.context == shared) node.label = (node.owner ? node.rootScope : "shared") + "_" + node.kind;
            else if (node.context) {
                const auto &context = contexts[node.context - 1];
                node.label = context.anchor.empty() ? node.kind : context.anchor + "_" + node.kind;
                if (node.scope.empty() && !node.sharedScope) node.scope = context.scope;
            } else node.label = node.kind;
            // Keep the full meaning in the plan; identifiers contain a short
            // context and operation, never a serialized Boolean formula.
            if (node.anchor.empty() && node.label.size() > 80) {
                auto context = node.context && node.context != shared ? contexts[node.context - 1].anchor : std::string("shared");
                node.label = context.substr(0, 40) + "_" + node.kind;
            }
            if (node.view.literal < 4 || node.terminal) continue;
            auto expressionCost = [&] {
                unsigned cost = 1;
                for (unsigned input : node.inputs) cost += nodes[normalized(input)].cost;
                return cost;
            };
            unsigned cost = expressionCost();
            while (cost > expressionLimit) {
                unsigned cut = shared, largest = 1;
                for (unsigned input : node.inputs) {
                    input = normalized(input);
                    if (nodes[input].inlineExpression && nodes[input].cost > largest) {
                        largest = nodes[input].cost; cut = input;
                    }
                }
                if (cut == shared) break; // A flat aggregate list is already shallow.
                nodes[cut].inlineExpression = false;
                nodes[cut].cost = 1;
                cost = expressionCost();
            }
            node.rhsCost = cost;
            node.inlineExpression = node.inlineable && node.uses == 1 && cost <= expressionLimit;
            node.cost = node.inlineExpression ? cost : 1;
        }
        planned = true;
        return mlir::success();
    }

    const Node *find(mlir::Value raw) const {
        if (!prepared) return nullptr;
        auto found = ids.find(hooks.canonical(raw));
        return found == ids.end() ? nullptr : &nodes[normalized(found->second)];
    }
    bool ready() const { return prepared; }
    bool complete() const { return planned; }
    bool mayInline(mlir::Value value) const {
        auto node = find(value);
        return planned && node && node->inlineExpression;
    }
    std::optional<unsigned> identity(mlir::Value raw) const {
        auto node = find(raw);
        if (!node) return std::nullopt;
        return ids.lookup(node->value);
    }
    void emitted(mlir::Value raw) {
        if (auto node = const_cast<Node *>(find(raw))) node->emitted = true;
        else unknownEmissions.insert(raw);
    }
    void absorbEmissions(const RtlPresentationPlan &other) {
        for (const auto &node : other.nodes)
            if (node.emitted) emitted(node.value);
        for (auto value : other.unknownEmissions) emitted(value);
    }
    llvm::json::Object report(const std::function<uint64_t(mlir::Value)> &original) const {
        llvm::json::Array values;
        unsigned live = 0, covered = 0, sharedValues = 0, unexpected = unknownEmissions.size();
        for (auto [id, node] : llvm::enumerate(nodes)) {
            if (!node.live && !node.emitted) continue;
            live += node.live;
            covered += node.live && !node.label.empty();
            unexpected += node.emitted && (!node.live || node.label.empty());
            sharedValues += node.uses > 1 && !node.terminal && node.view.literal == 4;
            llvm::json::Array consumers;
            for (unsigned consumer : node.consumers) consumers.push_back(consumer);
            values.emplace_back(llvm::json::Object{
                {"id", id}, {"original_value", original(node.value)}, {"kind", node.kind}, {"context", node.label}, {"scope", node.scope},
                {"uses", node.uses}, {"live", node.live}, {"emitted", node.emitted},
                {"shared_owner", node.sharedOwner}, {"root_scope", node.rootScope},
                {"coupled_fields", node.coupledFields},
                {"shared_context", node.sharedContext}, {"consumers", std::move(consumers)},
                {"materialization", node.terminal ? "boundary" : node.view.literal < 4 ? "literal" :
                    node.inlineExpression ? "single-use bounded expression" : node.uses > 1 ? "shared producer" : "typed expression boundary"},
                {"expression_cost", node.cost}, {"rhs_cost", node.rhsCost}, {"arity", node.inputs.size()}});
        }
        return llvm::json::Object{{"schema", "typed-rtl-presentation-v1"},
            {"live_values", live}, {"covered_values", covered}, {"shared_producers", sharedValues},
            {"unexpected_emitted_values", unexpected}, {"complete", planned && live == covered && !unexpected}, {"values", std::move(values)}};
    }
};
} // namespace acir::compiler
#endif
