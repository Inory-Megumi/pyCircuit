// Included inside QueueWiringProof. This adapter reuses the same four-state
// grant solver as storage writes, with fully scoped typed SSA identities.
  FailureOr<bool> typedSelectorsDisjoint(const PathAtom &left,
                                         const PathAtom &right) {
    using Core = HardwareGrantProof;
    using Node = Core::Node;
    struct NodeEntry {
      std::optional<HardwareIdentityEndpoint> endpoint;
      Core::NodeView view;
    };
    SmallVector<NodeEntry, 0> nodes;
    auto lookupCost = [](size_t size) {
      uint64_t work = 1;
      for (; size; size >>= 1) work += 2;
      return work;
    };
    auto payEndpoint = [&](const HardwareIdentityEndpoint &endpoint) {
      return pay(sizeof(HardwareIdentityEndpoint) +
          SourceCheckBudget::multiply(endpoint.scope.path.size(), sizeof(InstanceOp)) +
          SourceCheckBudget::multiply(8, SourceCheckBudget::bindings(endpoint.scope.rootBindings)));
    };
    auto reserveNode = [&]() -> LogicalResult {
      if (nodes.size() < nodes.capacity()) return step(module);
      uint64_t next = SourceCheckBudget::add(SourceCheckBudget::multiply(nodes.capacity(), 2), 1);
      if (next <= nodes.capacity() || next > nodes.max_size()) return failure();
      if (failed(pay(SourceCheckBudget::multiply(next, sizeof(NodeEntry))))) return failure();
      for (const auto &node : nodes)
        if (node.endpoint && failed(payEndpoint(*node.endpoint))) return failure();
      nodes.reserve(next);
      return success();
    };
    auto synthetic = [&](Core::NodeView view) -> FailureOr<Node> {
      if (failed(reserveNode())) return failure();
      Node id = nodes.size(); nodes.push_back({{}, std::move(view)}); return id;
    };
    auto bind = [&](const HardwareIdentityEndpoint &endpoint) -> FailureOr<Node> {
      for (auto [id, node] : llvm::enumerate(nodes)) {
        if (failed(step(module, 2))) return failure();
        if (node.endpoint && same(*node.endpoint, endpoint)) return id;
      }
      if (failed(payEndpoint(endpoint)) || failed(reserveNode())) return failure();
      Node id = nodes.size(); nodes.push_back({endpoint, {}}); return id;
    };
    auto combine = [&](Node left, Node right, Core::NodeView::Kind kind = Core::NodeView::And) -> FailureOr<Node> {
      Core::NodeView view; view.kind = kind; view.width = 1; view.operands.push_back(left);
      if (kind != Core::NodeView::Not) view.operands.push_back(right);
      return synthetic(std::move(view));
    };
    std::map<std::pair<Node, const void *>, Node> projections;
    std::function<FailureOr<Node>(Node, unsigned)> canonical = [&](Node id, unsigned depth) -> FailureOr<Node> {
      if (depth >= 128 || id >= nodes.size() || failed(budget.debit(1, module))) return failure();
      if (!nodes[id].endpoint) return id;
      auto endpoint = *nodes[id].endpoint;
      if (failed(payEndpoint(endpoint))) return failure();
      auto bindings = scopeBindings(endpoint.scope);
      if (failed(bindings)) return failure();
      Value input;
      if (auto toBits = endpoint.value.getDefiningOp<EnumToBitsOp>()) {
        if (failed(analysis.verifyResolvedOperation(toBits, *bindings))) return failure();
        input = toBits.getInput();
      } else if (auto fromBits = endpoint.value.getDefiningOp<EnumFromBitsOp>();
                 fromBits && endpoint.value == fromBits.getValue()) {
        if (failed(analysis.verifyResolvedOperation(fromBits, *bindings))) return failure();
        input = fromBits.getInput();
      } else if (auto field = endpoint.value.getDefiningOp<StructGetOp>()) {
        if (failed(analysis.verifyResolvedOperation(field, *bindings))) return failure();
        auto source = normal(field.getValue(), endpoint.scope);
        if (failed(source)) return failure();
        auto raw = bind(*source); if (failed(raw)) return failure();
        auto base = canonical(*raw, depth + 1); if (failed(base)) return failure();
        auto aggregate = nodes[*base].endpoint;
        if (auto create = aggregate ? aggregate->value.getDefiningOp<StructCreateOp>() : StructCreateOp()) {
          auto aggregateBindings = scopeBindings(aggregate->scope);
          if (failed(aggregateBindings) || failed(analysis.verifyResolvedOperation(create, *aggregateBindings))) return failure();
          auto decl = analysis.lookupStruct(cast<StructType>(create.getResult().getType()));
          if (!decl) return failure();
          for (auto [ordinal, member] : llvm::enumerate(decl.getFields())) {
            if (failed(budget.debit(1, module))) return failure();
            if (cast<DictionaryAttr>(member).getAs<StringAttr>("name") == field.getFieldAttr()) {
              auto actual = normal(create->getOperand(ordinal), aggregate->scope);
              if (failed(actual)) return failure();
              auto child = bind(*actual); if (failed(child)) return failure();
              return canonical(*child, depth + 1);
            }
          }
          return failure();
        }
        auto key = std::make_pair(*base, field.getFieldAttr().getAsOpaquePointer());
        if (failed(budget.debit(lookupCost(projections.size()), module))) return failure();
        auto found = projections.find(key); if (found != projections.end()) return found->second;
        Core::NodeView view;
        if (isa<BitsType, EnumType>(endpoint.resolvedType)) {
          auto width = analysis.getPackedWidth(endpoint.resolvedType, *bindings, module);
          if (failed(width)) return failure(); view.width = *width;
        }
        auto result = synthetic(view);
        if (failed(result) || failed(pay(8 * sizeof(void *)))) return failure();
        projections.emplace(key, *result); return *result;
      }
      if (!input) return id;
      auto actual = normal(input, endpoint.scope); if (failed(actual)) return failure();
      auto child = bind(*actual); if (failed(child)) return failure();
      return canonical(*child, depth + 1);
    };
    Core proof(canonical, [&](Node id) -> FailureOr<Core::NodeView> {
      if (id >= nodes.size() || failed(budget.debit(1, module))) return failure();
      if (!nodes[id].endpoint) return nodes[id].view;
      // Copy before binding operands: appending nodes may reallocate the vector.
      auto endpoint = *nodes[id].endpoint;
      if (failed(payEndpoint(endpoint))) return failure();
      auto bindings = scopeBindings(endpoint.scope);
      if (failed(bindings)) return failure();
      Core::NodeView view;
      if (!isa<BitsType, EnumType>(endpoint.resolvedType)) return view;
      auto width = analysis.getPackedWidth(endpoint.resolvedType, *bindings, module);
      if (failed(width)) return failure(); view.width = *width;
      auto *operation = endpoint.value.getDefiningOp();
      if (auto constant = dyn_cast_or_null<BitsConstantOp>(operation)) {
        if (failed(analysis.verifyResolvedOperation(constant, *bindings))) return failure();
        auto value = analysis.evaluateStatic(constant.getValue(), *bindings, constant);
        if (failed(value)) return failure();
        if (auto integer = dyn_cast<MathIntAttr>(*value)) {
          if (failed(budget.debit(SourceCheckBudget::add(integer.getCanonicalValue().size(), *width / 64 + 1), constant))) return failure();
          llvm::APSInt number(integer.getCanonicalValue());
          if (!number.isNegative() && number.getActiveBits() <= *width)
            view.fullyKnown = Core::Constant{integer, *width};
        }
        return view;
      }
      if (auto create = dyn_cast_or_null<EnumCreateOp>(operation)) {
        if (failed(analysis.verifyResolvedOperation(create, *bindings))) return failure();
        auto enumeration = analysis.resolveEnum(cast<EnumType>(endpoint.resolvedType), create);
        if (failed(enumeration)) return failure();
        for (const auto &member : enumeration->members) {
          if (failed(budget.debit(1 + member.code.getCanonicalValue().size(), create))) return failure();
          if (member.name == create.getMemberAttr()) {
            view.fullyKnown = Core::Constant{member.code, enumeration->width}; break;
          }
        }
        if (!view.fullyKnown) return failure();
        return view;
      }
      if (auto unary = dyn_cast_or_null<BitsUnaryOp>(operation); unary && unary.getOpcode() == "not") view.kind = Core::NodeView::Not;
      else if (auto binary = dyn_cast_or_null<BitsBinaryOp>(operation)) {
        if (binary.getOpcode() == "and") view.kind = Core::NodeView::And;
        if (binary.getOpcode() == "or") view.kind = Core::NodeView::Or;
      } else if (isa_and_nonnull<BitsSelectOp>(operation)) view.kind = Core::NodeView::Select;
      else if (auto compare = dyn_cast_or_null<BitsCompareOp>(operation)) {
        if (compare.getPredicate() == "eq") view.kind = Core::NodeView::Eq;
        if (compare.getPredicate() == "ne") view.kind = Core::NodeView::Ne;
      }
      // case_eq is deliberately opaque: negative KnownOne includes X/Z.
      if (view.kind != Core::NodeView::Raw) {
        if (failed(analysis.verifyResolvedOperation(operation, *bindings))) return failure();
        for (Value value : operation->getOperands()) {
          auto child = normal(value, endpoint.scope); if (failed(child)) return failure();
          auto node = bind(*child); if (failed(node)) return failure(); view.operands.push_back(*node);
        }
      }
      return view;
    }, [&](uint64_t cost) { return succeeded(budget.debit(cost, module)); });
    auto a = bind(left.value), b = bind(right.value);
    if (failed(a) || failed(b)) return failure();
    if (!left.positive) a = combine(*a, 0, Core::NodeView::Not);
    if (!right.positive) b = combine(*b, 0, Core::NodeView::Not);
    if (failed(a) || failed(b)) return failure();
    return proof.disjoint(*a, *b);
  }
