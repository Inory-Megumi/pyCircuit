  LogicalResult forwardValues() {
    bool present = false;
    for (const auto &entry : actionViewProofs) {
      if (failed(budget.debit(1, entry.first))) return failure();
      auto view = entry.first->getAttrOfType<DictionaryAttr>("ac.action_view");
      present |= view.getAs<StringAttr>("member").getValue() == "forward";
    }
    if (!present) return success();
    for (auto [occurrenceID, entry] : llvm::enumerate(occurrences)) {
      if (!entry.wiring) continue;
      for (const auto &writer : entry.wiring->writers) {
        auto sampled = writerAdmission(entry, writer.rule);
        if (failed(sampled)) return failure();
        auto yield = cast<YieldOp>(writer.rule->getRegion(0).front().getTerminator());
        for (const auto &view : (*sampled)->forwards) {
          if (failed(budget.debit(32 + writer.candidates.size(), writer.rule))) return failure();
          auto stateID = target(entry, view.stateID);
          if (failed(stateID)) return failure();
          const TransactionCandidateView *candidate = nullptr;
          uint64_t candidateID = 0;
          for (auto [id, possible] : llvm::enumerate(writer.candidates)) {
            auto physical = target(entry, possible.stateID);
            if (failed(physical)) return failure();
            if (*physical == *stateID) { candidate = &possible; candidateID = id; }
          }
          if (!candidate || view.candidate != yield->getOperand(candidate->dataIndex))
            return writer.rule->emitOpError() << "forward payload is not its actual root writer candidate";
          auto allow = [&](Operation *operation, unsigned operand, PrivateRoute::Kind kind) {
            return allowUse(entry.scope, operation, operand, *stateID, kind);
          };
          auto fields = view.fields;
          auto select = view.select;
          Value data = select.getTrueValue();
          if (fields.empty()) {
            if (failed(allow(select, 1, PrivateRoute::Data))) return failure();
          } else for (Attribute field : llvm::reverse(fields)) {
            auto get = data.getDefiningOp<StructGetOp>();
            if (!get || get.getFieldAttr() != field || failed(allow(get, 0, PrivateRoute::Data))) return failure();
            data = get.getValue();
          }
          auto enabled = select.getCondition().getDefiningOp<BitsBinaryOp>();
          if (!enabled || enabled.getOpcode() != "and" || enabled.getLhs() != view.sourceMask ||
              enabled.getRhs() != view.support) return failure();
          SmallVector<Value, 0> masks;
          bool domains = false;
          for (const auto &domain : (*sampled)->writeDomains) {
            if (failed(budget.debit(8 + domain.selectors.size(), writer.rule))) return failure();
            if (domain.candidate != candidateID) continue;
            domains = true;
            if (domain.selectors.size() > fields.size()) continue;
            bool covers = true;
            for (auto [i, raw] : llvm::enumerate(domain.selectors))
              covers &= cast<DictionaryAttr>(raw).getAs<StringAttr>("field") == fields[i];
            if (!covers) continue;
            if (failed(charge(budget, writer.rule, 1, sizeof(Value)))) return failure();
            masks.push_back(domain.mask);
          }
          Value support = view.support;
          if (domains) {
            auto andOp = support.getDefiningOp<BitsBinaryOp>();
            if (!andOp || andOp.getOpcode() != "and" || andOp.getLhs() != yield->getOperand(candidate->enableIndex) ||
                failed(allow(andOp, 0, PrivateRoute::Enable)))
              return writer.rule->emitOpError() << "forward support lacks the actual candidate enable";
            Value leaves = andOp.getRhs();
            for (Value mask : llvm::reverse(masks)) {
              auto join = leaves.getDefiningOp<BitsBinaryOp>();
              if (!join || join.getOpcode() != "or" || join.getRhs() != mask ||
                  failed(allow(join, 1, PrivateRoute::Mask)))
                return writer.rule->emitOpError() << "forward leaf support differs from actual write domains";
              leaves = join.getLhs();
            }
            auto zero = leaves.getDefiningOp<BitsConstantOp>();
            auto number = zero ? analysis.evaluateStatic(zero.getValue(), entry.bindings, zero) : FailureOr<Attribute>(failure());
            auto integer = succeeded(number) ? dyn_cast<MathIntAttr>(*number) : MathIntAttr();
            if (!integer || integer.getCanonicalValue() != "0") return failure();
          } else if (support != yield->getOperand(candidate->enableIndex) ||
                     failed(allow(enabled, 1, PrivateRoute::Enable)))
            return writer.rule->emitOpError() << "forward support is not the actual whole-owner enable";
          // Raw write masks are observations, never extra commit domains.
          // Source replay authenticates their original statement attribution.
          auto effectUse = [&](Operation *operation, unsigned operand) -> LogicalResult {
            if (failed(budget.debit(16, operation))) return failure();
            forwardEffectUses.insert({occurrenceID, operation, operand});
            return success();
          };
          Value source = view.sourceMask;
          for (auto [term, domainID] : llvm::zip(view.sourceTerms, view.sourceDomains)) {
            auto join = source.getDefiningOp<BitsBinaryOp>();
            if (!join || join.getOpcode() != "or" || join.getRhs() != term || failed(effectUse(join, 1))) return failure();
            auto andOp = term.getDefiningOp<BitsBinaryOp>();
            if (!andOp || andOp.getOpcode() != "and" || andOp.getLhs() != (*sampled)->fire ||
                failed(effectUse(andOp, 0))) return failure();
            if (domainID) {
              const auto &domain = (*sampled)->writeDomains[*domainID];
              if (domain.candidate != candidateID || domain.selectors.size() > fields.size()) return failure();
              for (auto [i, raw] : llvm::enumerate(domain.selectors))
                if (cast<DictionaryAttr>(raw).getAs<StringAttr>("field") != fields[i]) return failure();
              if (failed(allow(andOp, 1, PrivateRoute::Mask))) return failure();
            } else if (domains) {
              return writer.rule->emitOpError() << "observation-only whole-owner mask cannot replace a native write domain";
            }
            source = join.getLhs();
          }
        }
      }
    }
    return success();
  }
