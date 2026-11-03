  uint64_t actionResult = queueResult + (writeDomains ? writeDomains.size() : 0);
  llvm::DenseMap<Operation *, ActionViewProof> actionViewProofs;
  auto verifyTransport = [&](OpOperand &use) -> LogicalResult {
    auto consumer = dyn_cast<RuleOp>(use.getOwner());
    if (!consumer || !consumer->hasAttr("ac.action_view"))
      return rule.emitOpError() << "private action transport escapes its observation adapter";
    auto found = actionViewProofs.find(consumer);
    if (found == actionViewProofs.end()) {
      auto proof = verifyActionView(consumer, analysis, budget);
      if (failed(proof)) return failure();
      found = actionViewProofs.try_emplace(consumer, std::move(*proof)).first;
    }
    if (!found->second.uses.contains(&use))
      return rule.emitOpError() << "private action transport reaches an unrelated adapter operand";
    return success();
  };
  if (actions) for (Attribute raw : actions) {
    auto action = dyn_cast<DictionaryAttr>(raw);
    NamedAttrList actionCore;
    if (action) actionCore.assign(action.getValue());
    actionCore.erase("forwards");
    if (failed(exact(actionCore.getDictionary(rule.getContext()), {"action", "call", "invocation", "path", "active", "arguments"}, rule,
                     "action export"))) return failure();
    auto identity = action.getAs<DictionaryAttr>("action");
    bool rootEvent = identity && identity.get("registration");
    if (failed(exact(identity, rootEvent ? ArrayRef<StringRef>{"callee", "declaration", "owner", "registration"}
                     : ArrayRef<StringRef>{"callee", "declaration", "owner"}, rule,
                     "action identity"))) return failure();
    auto callee = identity.getAs<SymbolRefAttr>("callee");
    auto owner = identity.getAs<ArrayAttr>("owner");
    if (!callee || callee.getNestedReferences().size() != (rootEvent ? 0 : 1) || !owner ||
        failed(verifyOccurrence(identity.getAs<DictionaryAttr>("declaration"),
            [&] { return rule.emitOpError(); })) ||
        failed(verifyOccurrence(action.getAs<DictionaryAttr>("call"),
            [&] { return rule.emitOpError(); }))) return failure();
    for (Attribute occurrence : owner)
      if (failed(verifyOccurrence(dyn_cast<DictionaryAttr>(occurrence),
          [&] { return rule.emitOpError(); }))) return failure();
    if (rootEvent) {
      auto registered = rule->hasAttr("ac.registration_path")
          ? rule->getAttrOfType<DictionaryAttr>("ac.lexical_registration") : rule.getOccurrence();
      auto ownerPath = rule->hasAttr("ac.registration_path")
          ? rule->getAttrOfType<ArrayAttr>("ac.registration_path")
          : ArrayAttr::get(rule.getContext(), {});
      auto lexical = rule->hasAttr("ac.registration_path")
          ? rule->getAttrOfType<FlatSymbolRefAttr>("ac.registration_owner")
          : FlatSymbolRefAttr::get(module.getSymNameAttr());
      if (identity.get("registration") != registered || owner != ownerPath || callee != lexical)
        return rule.emitOpError() << "root event does not identify its actual producing registration";
    }
    auto active = index(action, "active", rule);
    auto path = parsePath(action, result.controls.size());
    auto invocation = action.getAs<ArrayAttr>("invocation");
    if (!invocation || (!rootEvent && invocation.empty())) return rule.emitOpError() << "action export requires its invocation chain";
    for (Attribute frame : invocation)
      if (failed(validateInvocationFrame(frame))) return failure();
    auto ownerControl = callable(invocation, false);
    if (failed(ownerControl) || failed(path) ||
        (rootEvent && (*ownerControl != &result.controls.front() || path->selectionControl)) ||
        (!rootEvent && cast<DictionaryAttr>(invocation[invocation.size() - 1]).get("call") != action.get("call")) ||
        (rootEvent && (identity.get("registration") != identity.get("declaration") ||
            identity.get("registration") != action.get("call") ||
            failed(verifyOccurrence(identity.getAs<DictionaryAttr>("registration"),
                [&] { return rule.emitOpError(); })))) ||
        failed(validatePath(*path, invocation, *ownerControl))) return failure();
    if (failed(active) || failed(path) || uint64_t(*active) != actionResult ||
        actionResult >= rule->getNumResults() ||
        failed(bitOne(yielded->getOperand(actionResult), analysis, bindings, rule, budget)))
      return rule.emitOpError() << "action event requires its exact suffix slot";
    result.actions.push_back({*path, actionResult, yielded->getOperand(actionResult)});
    if (rule->getResult(actionResult).use_empty())
      return rule.emitOpError() << "action event export has no authenticated observer";
    for (OpOperand &use : rule->getResult(actionResult++).getUses())
      if (failed(verifyTransport(use))) return failure();
    auto arguments = action.getAs<ArrayAttr>("arguments");
    if (!arguments || (rootEvent && !arguments.empty())) return failure();
    llvm::StringSet<> names;
    for (Attribute rawArgument : arguments) {
      auto argument = dyn_cast<DictionaryAttr>(rawArgument);
      if (failed(exact(argument, {"name", "result"}, rule, "action argument export")))
        return failure();
      auto name = argument.getAs<StringAttr>("name");
      auto ordinal = index(argument, "result", rule);
      if (!name || name.getValue().empty() || !names.insert(name.getValue()).second ||
          failed(ordinal) || uint64_t(*ordinal) != actionResult || actionResult >= rule->getNumResults())
        return rule.emitOpError() << "action argument requires a unique name and exact suffix slot";
      for (OpOperand &use : rule->getResult(actionResult++).getUses())
        if (failed(verifyTransport(use))) return failure();
    }
    if (action.get("forwards")) {
      auto forwards = action.getAs<ArrayAttr>("forwards");
      if (!forwards || forwards.empty()) return rule.emitOpError() << "forward export inventory must be nonempty";
      for (Attribute rawForward : forwards) {
        auto row = dyn_cast<DictionaryAttr>(rawForward);
        if (failed(exact(row, {"state", "fields", "result", "writes"}, rule, "forward export"))) return failure();
        auto resultIndex = index(row, "result", rule);
        auto state = row.getAs<DictionaryAttr>("state");
        auto fields = row.getAs<ArrayAttr>("fields");
        auto writes = row.getAs<ArrayAttr>("writes");
        if (failed(resultIndex) || uint64_t(*resultIndex) != actionResult || actionResult >= total ||
            !state || !fields || !writes || writes.empty()) return rule.emitOpError() << "forward export layout is invalid";
        auto owner = resolveTransactionState(module, state, analysis, bindings, budget);
        if (failed(owner)) return failure();
        auto leaf = forwardLeafType(analysis, owner->payloadType, fields, rule,
            [&](uint64_t work) { return budget.debit(work, rule); });
        auto select = yielded->getOperand(actionResult).getDefiningOp<BitsSelectOp>();
        if (failed(leaf) || !select || select->getBlock() != &rule.getBody().front() ||
            !areEquivalentHardwareTypes(*leaf, select.getResult().getType())) return failure();
        Value old = select.getFalseValue();
        for (Attribute field : llvm::reverse(fields)) {
          if (failed(budget.debit(16, rule))) return failure();
          auto get = old.getDefiningOp<StructGetOp>();
          if (!get || get->getBlock() != &rule.getBody().front() || get.getFieldAttr() != field) return failure();
          old = get.getValue();
        }
        if (failed(verifyForwardOldQ(old, state, rule, analysis, budget))) return failure();
        auto condition = select.getCondition().getDefiningOp<BitsBinaryOp>();
        if (!condition || condition.getOpcode() != "and" || condition->getBlock() != &rule.getBody().front()) return failure();
        Value candidate = select.getTrueValue();
        for (Attribute field : llvm::reverse(fields)) {
          if (failed(budget.debit(16, rule))) return failure();
          auto get = candidate.getDefiningOp<StructGetOp>();
          if (!get || get->getBlock() != &rule.getBody().front() || get.getFieldAttr() != field) return failure();
          candidate = get.getValue();
        }
        SampledAdmissionView::Forward forward{state, fields, select, candidate,
            condition.getLhs(), condition.getRhs(), {}, {}};
        Value mask = condition.getLhs();
        for (Attribute rawWrite : llvm::reverse(writes)) {
          if (failed(budget.debit(32, rule))) return failure();
          auto row = dyn_cast<DictionaryAttr>(rawWrite);
          bool whole = row && row.get("whole_owner");
          if (failed(exact(row, whole ? ArrayRef<StringRef>{"whole_owner", "invocation"}
                                     : ArrayRef<StringRef>{"domain", "invocation"}, rule, "forward source write"))) return failure();
          auto frames = row.getAs<ArrayAttr>("invocation");
          if (!frames) return failure();
          for (Attribute frame : frames) if (failed(validateInvocationFrame(frame))) return failure();
          auto prefix = invocationPrefix(invocation, frames);
          auto ownerControl = callable(frames, false);
          if (failed(prefix) || !*prefix || failed(ownerControl)) return failure();
          auto join = mask.getDefiningOp<BitsBinaryOp>();
          if (!join || join.getOpcode() != "or" || join->getBlock() != &rule.getBody().front()) return failure();
          auto term = join.getRhs().getDefiningOp<BitsBinaryOp>();
          if (!term || term.getOpcode() != "and" || term.getLhs() != result.fire ||
              term->getBlock() != &rule.getBody().front() ||
              failed(bitOne(term.getRhs(), analysis, bindings, rule, budget))) return failure();
          std::optional<uint64_t> domain;
          if (whole) {
            auto flag = row.getAs<BoolAttr>("whole_owner");
            if (!flag || !flag.getValue()) return failure();
          } else {
            auto id = index(row, "domain", rule);
            if (failed(id) || uint64_t(*id) >= result.writeDomains.size() ||
                term.getRhs() != result.writeDomains[*id].mask) return failure();
            domain = *id;
          }
          forward.sourceTerms.push_back(join.getRhs());
          forward.sourceDomains.push_back(domain);
          mask = join.getLhs();
        }
        auto zero = mask.getDefiningOp<BitsConstantOp>();
        auto value = zero ? analysis.evaluateStatic(zero.getValue(), bindings, zero) : FailureOr<Attribute>(failure());
        auto number = succeeded(value) ? dyn_cast<MathIntAttr>(*value) : MathIntAttr();
        if (!number || number.getCanonicalValue() != "0") return failure();
        result.forwards.push_back(std::move(forward));
        if (rule->getResult(actionResult).use_empty()) return rule.emitOpError() << "forward export has no authenticated observer";
        for (OpOperand &use : rule->getResult(actionResult++).getUses())
          if (failed(verifyTransport(use))) return failure();
      }
    }
  }
  if (actionResult != total) return rule.emitOpError() << "action suffix inventory is incomplete";
  if (actionInputs) for (Attribute raw : actionInputs) {
    auto input = dyn_cast<DictionaryAttr>(raw);
    NamedAttrList inputCore;
    if (input) inputCore.assign(input.getValue());
    inputCore.erase("state"); inputCore.erase("fields");
    if (failed(exact(inputCore.getDictionary(rule.getContext()), {"capture", "action", "member", "argument", "occurrence"},
            rule, "action input"))) return failure();
    auto capture = index(input, "capture", rule);
    if (failed(capture) || uint64_t(*capture) >= rule->getNumOperands())
      return rule.emitOpError() << "action input is outside its Rule capture layout";
    auto adapter = rule->getOperand(*capture).getDefiningOp<RuleOp>();
    auto proof = adapter ? verifyActionView(adapter, analysis, budget)
                         : FailureOr<ActionViewProof>(failure());
    if (failed(proof) || !proof->uses.contains(&rule->getOpOperand(*capture))) return failure();
  }
