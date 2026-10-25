// SSA endpoints keep their complete lexical occurrence and callable invocation.
// Only module-body endpoints become shared raw nodes across transaction plans.
class SourceWriteGrantProof {
  using Core = ac::detail::HardwareGrantProof;
  using Node = Core::Node;
  struct Endpoint {
    const ac::TransactionStatePlan *plan = nullptr;
    std::optional<ac::BoundValueId> bound;
    Value value;
    SmallVector<ac::InstanceOp> scope, prefix;
    std::optional<Core::NodeView> synthetic;
  };
  struct Key {
    const void *scope, *plan, *value;
    uint64_t bound;
  };
  struct Less {
    bool operator()(const Key &a, const Key &b) const {
      std::less<const void *> less;
      for (auto pair : {std::pair(a.scope, b.scope), std::pair(a.plan, b.plan), std::pair(a.value, b.value)}) {
        if (pair.first != pair.second) return less(pair.first, pair.second);
      }
      return a.bound < b.bound;
    }
  };
public:
  SourceWriteGrantProof(ac::ModuleOp root, const ac::HardwareAnalysis &hardware,
                        SourceCheckBudget &budget)
      : root(root), hardware(hardware), budget(budget),
        core([this](Node id, unsigned depth) { return canonical(id, depth); },
             [this](Node id) { return inspect(id); },
             [this](uint64_t work) { return charge(this->budget, this->root, work); }) {}

  FailureOr<bool> disjoint(const ac::TransactionStatePlan &first,
                           ArrayRef<ac::InstanceOp> firstPrefix, ac::StateWriteId a,
                           const ac::TransactionStatePlan &second,
                           ArrayRef<ac::InstanceOp> secondPrefix, ac::StateWriteId c) {
    const auto &left = first.writes[a], &right = second.writes[c];
    size_t common = std::min(left.selectors.size(), right.selectors.size());
    bool bothIndexed = false;
    for (size_t i = 0; i < common; ++i) {
      if (!charge(budget, root, 2)) return failure();
      auto l = cast<DictionaryAttr>(left.selectors[i]);
      auto r = cast<DictionaryAttr>(right.selectors[i]);
      auto lf = l.getAs<StringAttr>("field"), rf = r.getAs<StringAttr>("field");
      if (lf && rf && lf != rf) return true;
      if (bool(lf) != bool(rf)) break;
      if (!lf) bothIndexed = true;
    }
    auto lp = path(first, firstPrefix, a), rp = path(second, secondPrefix, c);
    if (failed(lp) || failed(rp)) return failure();
    if (bothIndexed && left.indices.size() == 1 && right.indices.size() == 1) {
      auto li = bind(first, firstPrefix, left.indices.front());
      auto ri = bind(second, secondPrefix, right.indices.front());
      if (failed(li) || failed(ri)) return failure();
      return core.disjointAtAddress(*lp, *rp, *li, *ri);
    }
    return core.disjoint(*lp, *rp);
  }
  StringRef failureReason() const { return core.failureReason(); }
private:
  uint64_t lookupCost() const {
    uint64_t comparisons = 1;
    for (uint64_t n = index.size() + 1; n > 1; n = n / 2 + n % 2) comparisons += 2;
    return 4 * comparisons;
  }
  FailureOr<Node> save(Endpoint endpoint) {
    if (!product(budget, root, endpoint.scope.size() + endpoint.prefix.size(),
                 SourceCheckBudget::bytes(sizeof(ac::InstanceOp)) + 1)) return failure();
    if (endpoint.synthetic) {
      if (!prepayAppend(budget, root, endpoints)) return failure();
      Node id = endpoints.size(); endpoints.push_back(std::move(endpoint)); return id;
    }
    if (!charge(budget, root, lookupCost() + endpoint.scope.size())) return failure();
    auto scope = routePath(root->getContext(), endpoint.scope);
    Key key{scope.getAsOpaquePointer(), endpoint.plan, endpoint.value.getAsOpaquePointer(),
            endpoint.bound.value_or(0)};
    auto position = index.lower_bound(key);
    if (position != index.end() && !Less{}(key, position->first)) return position->second;
    if (!charge(budget, root, 4 + SourceCheckBudget::bytes(sizeof(decltype(index)::value_type) + 4 * sizeof(void *))) ||
        !prepayAppend(budget, root, endpoints)) return failure();
    Node id = endpoints.size(); endpoints.push_back(std::move(endpoint)); index.emplace_hint(position, key, id); return id;
  }
  FailureOr<Node> bind(const ac::TransactionStatePlan &plan,
                       ArrayRef<ac::InstanceOp> prefix, ac::BoundValueId id) {
    if (id >= plan.values.size() || !charge(budget, root, 2)) return failure();
    const auto &ref = plan.values[id];
    Endpoint endpoint; endpoint.value = ref.value;
    if (!product(budget, root, prefix.size(), 2)) return failure();
    endpoint.scope.assign(prefix.begin(), prefix.end());
    auto local = anchorPath(plan, ref.anchor);
    endpoint.scope.append(local.begin(), local.end());
    if (!moduleValue(ref.value, plan.instances[ref.anchor].definition)) {
      endpoint.plan = &plan; endpoint.bound = id;
      endpoint.prefix.assign(prefix.begin(), prefix.end());
    }
    return save(std::move(endpoint));
  }
  LogicalResult indexPlan(const ac::TransactionStatePlan &plan) {
    if (!charge(budget, root)) return failure();
    if (indexedPlans.contains(&plan)) return success();
    for (auto [id, candidate] : llvm::enumerate(plan.values)) {
      if (!charge(budget, root, 8)) return failure();
      OperandKey key{&plan, {candidate.anchor, {candidate.frame, candidate.value.getAsOpaquePointer()}}};
      operands.try_emplace(key, id);
    }
    for (auto [id, frame] : llvm::enumerate(plan.frames))
      for (const auto *arguments : {&frame.guardArguments, &frame.bodyArguments})
        for (const auto &argument : *arguments) {
          if (!charge(budget, root, 7)) return failure();
          FormalKey key{&plan, {id, argument.formal.getAsOpaquePointer()}};
          formals[key] = argument.actual;
        }
    for (const auto &call : plan.calls)
      for (const auto &result : call.results) {
        if (!charge(budget, root, 6)) return failure();
        aliases[{&plan, result.result}] = result.yielded;
      }
    for (const auto &write : plan.formalWrites) {
      if (!charge(budget, root, 6)) return failure();
      if (write.snapshot)
        aliases.try_emplace(std::make_pair(&plan, *write.snapshot),
                           write.owner ? write.candidate : *write.previous);
    }
    for (const auto &read : plan.reads) {
      if (!charge(budget, root, 6)) return failure();
      const auto &version = plan.versions[read.version];
      // Explicit predecessors replace Q0 with an EHR candidate; never alias
      // that snapshot with another registration's committed old Q.
      if (version.kind == ac::StateVersionKind::OldQ && plan.predecessors.empty())
        aliases.try_emplace(std::make_pair(&plan, read.result), plan.owners[read.owner].oldQ);
    }
    if (!charge(budget, root, 2)) return failure();
    indexedPlans.insert(&plan);
    return success();
  }
  FailureOr<Node> operand(const Endpoint &endpoint, Value value) {
    if (endpoint.plan) {
      const auto &ref = endpoint.plan->values[*endpoint.bound];
      auto frame = moduleValue(value, endpoint.plan->instances[ref.anchor].definition)
                       ? endpoint.plan->rootFrame : ref.frame;
      if (failed(indexPlan(*endpoint.plan))) return failure();
      if (!charge(budget, root)) return failure();
      OperandKey key{endpoint.plan, {ref.anchor, {frame, value.getAsOpaquePointer()}}};
      auto found = operands.find(key);
      if (found == operands.end()) return failure();
      return bind(*endpoint.plan, endpoint.prefix, found->second);
    }
    Endpoint raw; raw.value = value; raw.scope = endpoint.scope; return save(std::move(raw));
  }
  FailureOr<std::reference_wrapper<const ac::HardwareBindings>> bindings(const Endpoint &endpoint) {
    if (!charge(budget, root)) return failure();
    if (endpoint.plan) {
      // Plans and their frame bindings are immutable throughout this proof.
      return std::cref(endpoint.plan->frames[endpoint.plan->values[*endpoint.bound].frame].bindings);
    }
    if (!charge(budget, root, lookupCost() + endpoint.scope.size())) return failure();
    auto scope = routePath(root->getContext(), endpoint.scope).getAsOpaquePointer();
    auto found = scopeBindings.find(scope);
    if (found != scopeBindings.end()) return std::cref(found->second);
    ac::HardwareBindings result; result.owner = root;
    for (auto instance : endpoint.scope) {
      if (!charge(budget, root, 1 + SourceCheckBudget::bindings(result))) return failure();
      auto next = hardware.bindInstance(instance, result);
      if (failed(next)) return failure(); result = std::move(*next);
    }
    if (!charge(budget, root, 8 + SourceCheckBudget::bindings(result))) return failure();
    auto inserted = scopeBindings.emplace(scope, std::move(result));
    return std::cref(inserted.first->second);
  }
  bool payAttribute(Attribute attribute, unsigned depth = 0) {
    if (depth >= 128 || !charge(budget, root)) return false;
    if (auto integer = dyn_cast<ac::MathIntAttr>(attribute))
      return charge(budget, root, integer.getCanonicalValue().size());
    if (auto expression = dyn_cast<ac::StaticExprAttr>(attribute)) return payAttribute(expression.getTree(), depth + 1);
    if (auto dictionary = dyn_cast<DictionaryAttr>(attribute)) {
      for (auto item : dictionary) if (!payAttribute(item.getValue(), depth + 1)) return false;
    } else if (auto array = dyn_cast<ArrayAttr>(attribute)) {
      for (Attribute item : array) if (!payAttribute(item, depth + 1)) return false;
    }
    return true;
  }
  FailureOr<std::optional<llvm::APSInt>> integer(ac::StaticExprAttr expression,
                                                 const ac::HardwareBindings &bound, Operation *site) {
    if (!payAttribute(expression)) return failure();
    if (!hardware.isStaticEvaluable(expression, bound)) return std::optional<llvm::APSInt>();
    auto value = hardware.evaluateStatic(expression, bound, site);
    if (failed(value)) return failure();
    auto number = dyn_cast<ac::MathIntAttr>(*value);
    if (!number) return std::optional<llvm::APSInt>();
    return std::optional<llvm::APSInt>(llvm::APSInt(number.getCanonicalValue()));
  }
  FailureOr<std::optional<uint64_t>> width(Value value, const ac::HardwareBindings &bound) {
    if (isa<ac::EnumType>(value.getType())) {
      auto count = hardware.getPackedWidth(value.getType(), bound, root);
      if (failed(count)) return failure();
      return std::optional<uint64_t>(*count);
    }
    auto type = dyn_cast<ac::BitsType>(value.getType());
    if (!type) return std::optional<uint64_t>();
    auto number = integer(type.getWidth(), bound, root);
    if (failed(number)) return failure();
    if (!*number || (**number).isNegative() || (**number).isZero() || (**number).getActiveBits() > 64)
      return std::optional<uint64_t>();
    return std::optional<uint64_t>((**number).getZExtValue());
  }
  FailureOr<Node> canonical(Node id, unsigned depth) {
    if (!charge(budget, root)) return failure();
    if (auto found = canonicalNodes.find(id); found != canonicalNodes.end()) return found->second;
    auto result = canonicalImpl(id, depth);
    if (failed(result) || !charge(budget, root, 4)) return failure();
    canonicalNodes.try_emplace(id, *result);
    canonicalNodes.try_emplace(*result, *result);
    return *result;
  }
  FailureOr<Node> canonicalImpl(Node id, unsigned depth) {
    for (; depth < 128; ++depth) {
      if (id >= endpoints.size() || !charge(budget, root, 2)) return failure();
      if (!product(budget, root, endpoints[id].scope.size() + endpoints[id].prefix.size(),
                   1 + SourceCheckBudget::bytes(sizeof(ac::InstanceOp)))) return failure();
      Endpoint endpoint = endpoints[id];
      if (endpoint.synthetic) return id;
      std::optional<Node> next;
      if (endpoint.plan) {
        const auto &plan = *endpoint.plan;
        const auto &ref = plan.values[*endpoint.bound];
        if (failed(indexPlan(plan)) || !charge(budget, root, 2)) return failure();
        FormalKey key{&plan, {ref.frame, ref.value.getAsOpaquePointer()}};
        auto formal = formals.find(key);
        auto alias = aliases.find({&plan, *endpoint.bound});
        if (formal != formals.end() || alias != aliases.end()) {
          auto actual = bind(plan, endpoint.prefix,
              formal != formals.end() ? formal->second : alias->second);
          if (failed(actual)) return failure(); next = *actual;
        }
      }
      if (!next) if (auto argument = dyn_cast<BlockArgument>(endpoint.value))
        if (isa<ac::ModuleOp>(argument.getOwner()->getParentOp()) && !endpoint.scope.empty()) {
          auto instance = endpoint.scope.back();
          if (argument.getArgNumber() >= instance->getNumOperands()) return failure();
          Endpoint raw; raw.value = instance->getOperand(argument.getArgNumber());
          raw.scope = endpoint.scope; raw.scope.pop_back();
          auto actual = save(std::move(raw)); if (failed(actual)) return failure(); next = *actual;
        }
      if (!next) {
        auto bound = bindings(endpoint); if (failed(bound)) return failure();
        Value input;
        if (auto toBits = endpoint.value.getDefiningOp<ac::EnumToBitsOp>()) {
          if (failed(hardware.verifyResolvedOperation(toBits, *bound))) return failure();
          input = toBits.getInput();
        } else if (auto fromBits = endpoint.value.getDefiningOp<ac::EnumFromBitsOp>();
                   fromBits && endpoint.value == fromBits.getValue()) {
          if (failed(hardware.verifyResolvedOperation(fromBits, *bound))) return failure();
          input = fromBits.getInput();
        } else if (auto field = endpoint.value.getDefiningOp<ac::StructGetOp>()) {
          if (failed(hardware.verifyResolvedOperation(field, *bound))) return failure();
          auto source = operand(endpoint, field.getValue());
          if (failed(source)) return failure();
          auto base = canonical(*source, depth + 1);
          if (failed(base)) return failure();
          Endpoint aggregate = endpoints[*base];
          if (auto create = aggregate.value ? aggregate.value.getDefiningOp<ac::StructCreateOp>() : ac::StructCreateOp()) {
            auto aggregateBindings = bindings(aggregate);
            if (failed(aggregateBindings) || failed(hardware.verifyResolvedOperation(create, *aggregateBindings))) return failure();
            auto decl = hardware.lookupStruct(cast<ac::StructType>(create.getResult().getType()));
            if (!decl) return failure();
            for (auto [ordinal, member] : llvm::enumerate(decl.getFields())) {
              if (!charge(budget, root)) return failure();
              if (cast<DictionaryAttr>(member).getAs<StringAttr>("name") == field.getFieldAttr()) {
                auto actual = operand(aggregate, create->getOperand(ordinal));
                if (failed(actual)) return failure();
                next = *actual; break;
              }
            }
            if (!next) return failure();
          } else {
            // A projection's identity includes its exact old-Q/candidate base.
            // No identity is shared merely because two FSMs have equal types.
            auto key = std::make_pair(*base, field.getFieldAttr().getAsOpaquePointer());
            if (!charge(budget, root, lookupCost())) return failure();
            auto found = projections.find(key);
            if (found != projections.end()) return found->second;
            auto count = width(endpoint.value, *bound);
            if (failed(count)) return failure();
            Endpoint projected; Core::NodeView view; view.width = *count;
            projected.synthetic = view;
            auto node = save(std::move(projected));
            if (failed(node) || !charge(budget, root, 8)) return failure();
            projections.emplace(key, *node); return *node;
          }
        } else if (auto extract = endpoint.value.getDefiningOp<ac::BitsExtractOp>()) {
          auto low = integer(extract.getLow(), *bound, extract);
          auto from = width(extract.getInput(), *bound), to = width(endpoint.value, *bound);
          if (failed(low) || failed(from) || failed(to)) return failure();
          if (*low && (**low).isZero() && *from && *to && **from == **to) input = extract.getInput();
        } else if (auto resize = endpoint.value.getDefiningOp<ac::BitsResizeOp>()) {
          auto from = width(resize.getInput(), *bound), to = width(endpoint.value, *bound);
          if (failed(from) || failed(to)) return failure();
          if (*from && *to && **from == **to) input = resize.getInput();
        }
        if (input) { auto actual = operand(endpoint, input); if (failed(actual)) return failure(); next = *actual; }
      }
      if (!next || *next == id) return id;
      id = *next;
    }
    return failure();
  }
  FailureOr<Core::NodeView> inspect(Node id) {
    if (id >= endpoints.size() || !charge(budget, root)) return failure();
    if (!product(budget, root, endpoints[id].scope.size() + endpoints[id].prefix.size(),
                 1 + SourceCheckBudget::bytes(sizeof(ac::InstanceOp)))) return failure();
    Endpoint endpoint = endpoints[id];
    if (endpoint.synthetic) return *endpoint.synthetic;
    Core::NodeView view;
    auto bound = bindings(endpoint); if (failed(bound)) return failure();
    auto bits = width(endpoint.value, *bound); if (failed(bits)) return failure(); view.width = *bits;
    auto *operation = endpoint.value.getDefiningOp();
    if (auto constant = dyn_cast_or_null<ac::BitsConstantOp>(operation)) {
      auto code = integer(constant.getValue(), *bound, constant);
      if (failed(code)) return failure();
      if (*bits && *code && !(**code).isNegative() && (**code).getActiveBits() <= **bits) {
        if (**bits > std::numeric_limits<unsigned>::max() ||
            !charge(budget, root, **bits / 64 + (**bits % 64 != 0))) return failure();
        auto pattern = llvm::APSInt((**code).zextOrTrunc(**bits), true);
        view.fullyKnown = Core::Constant{ac::MathIntAttr::get(root->getContext(), pattern), **bits};
      }
    } else if (auto create = dyn_cast_or_null<ac::EnumCreateOp>(operation)) {
      if (failed(hardware.verifyResolvedOperation(create, *bound))) return failure();
      auto enumeration = hardware.resolveEnum(cast<ac::EnumType>(endpoint.value.getType()), create);
      if (failed(enumeration)) return failure();
      for (const auto &member : enumeration->members) {
        if (!charge(budget, root, 1 + member.code.getCanonicalValue().size())) return failure();
        if (member.name == create.getMemberAttr()) {
          view.fullyKnown = Core::Constant{member.code, enumeration->width}; break;
        }
      }
      if (!view.fullyKnown) return failure();
    } else {
      if (auto unary = dyn_cast_or_null<ac::BitsUnaryOp>(operation); unary && unary.getOpcode() == "not") view.kind = Core::NodeView::Not;
      else if (auto binary = dyn_cast_or_null<ac::BitsBinaryOp>(operation)) {
        if (binary.getOpcode() == "and") view.kind = Core::NodeView::And;
        if (binary.getOpcode() == "or") view.kind = Core::NodeView::Or;
      } else if (isa_and_nonnull<ac::BitsSelectOp>(operation)) view.kind = Core::NodeView::Select;
      else if (auto compare = dyn_cast_or_null<ac::BitsCompareOp>(operation)) {
        if (compare.getPredicate() == "eq") view.kind = Core::NodeView::Eq;
        if (compare.getPredicate() == "ne") view.kind = Core::NodeView::Ne;
      }
      if (view.kind != Core::NodeView::Raw) {
        if (failed(hardware.verifyResolvedOperation(operation, *bound))) return failure();
        for (Value source : operation->getOperands()) {
          auto child = operand(endpoint, source); if (failed(child)) return failure(); view.operands.push_back(*child);
        }
      }
    }
    return view;
  }
  FailureOr<Node> combine(Node first, Node second, Core::NodeView::Kind kind = Core::NodeView::And) {
    Endpoint endpoint; Core::NodeView view; view.kind = kind; view.width = 1;
    view.operands.push_back(first); if (kind != Core::NodeView::Not) view.operands.push_back(second);
    endpoint.synthetic = std::move(view); return save(std::move(endpoint));
  }
  FailureOr<Node> path(const ac::TransactionStatePlan &plan, ArrayRef<ac::InstanceOp> prefix,
                       ac::StateWriteId id) {
    const auto &write = plan.writes[id];
    auto result = bind(plan, prefix, write.authoredPath); if (failed(result)) return failure();
    auto ancestry = plan.versions[write.version].validity.path;
    auto dominates = [&](ac::TransactionSourcePath definition) -> FailureOr<bool> {
      auto use = ancestry;
      for (unsigned depth = 0; depth <= 128; ++depth) {
        if (!charge(budget, root)) return failure();
        if (sameSourcePath(definition, use)) return true;
        if (!use.branch) return false;
        use = plan.branches[*use.branch].entry.path;
      }
      return failure();
    };
    for (const auto &guard : plan.guards) {
      auto reached = dominates(plan.controls[guard.control].path);
      if (failed(reached)) return failure();
      if (!*reached) continue;
      auto predicate = bind(plan, prefix, guard.predicate); if (failed(predicate)) return failure();
      result = combine(*result, *predicate); if (failed(result)) return failure();
    }
    for (unsigned depth = 0; ancestry.branch; ++depth) {
      if (depth > 128 || !charge(budget, root)) return failure();
      const auto &branch = plan.branches[*ancestry.branch];
      auto condition = bind(plan, prefix, branch.condition); if (failed(condition)) return failure();
      if (!ancestry.whenTrue) { condition = combine(*condition, 0, Core::NodeView::Not); if (failed(condition)) return failure(); }
      result = combine(*result, *condition); if (failed(result)) return failure();
      ancestry = branch.entry.path;
    }
    return result;
  }
  ac::ModuleOp root;
  const ac::HardwareAnalysis &hardware;
  SourceCheckBudget &budget;
  SmallVector<Endpoint, 0> endpoints;
  std::map<Key, Node, Less> index;
  std::map<std::pair<Node, const void *>, Node> projections;
  llvm::DenseMap<Node, Node> canonicalNodes;
  using OperandKey = std::pair<const ac::TransactionStatePlan *,
      std::pair<uint64_t, std::pair<uint64_t, const void *>>>;
  llvm::DenseMap<OperandKey, ac::BoundValueId> operands;
  using FormalKey = std::pair<const ac::TransactionStatePlan *, std::pair<uint64_t, const void *>>;
  llvm::DenseMap<FormalKey, ac::BoundValueId> formals;
  llvm::DenseMap<std::pair<const ac::TransactionStatePlan *, ac::BoundValueId>, ac::BoundValueId> aliases;
  llvm::DenseSet<const ac::TransactionStatePlan *> indexedPlans;
  std::map<const void *, ac::HardwareBindings> scopeBindings;
  Core core;
};
