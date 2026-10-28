// Bounded ROBDD fallback for correlations lost by the necessary-fact fast path.
// Every bit is represented by mutually exclusive known-zero/known-one rails.
// X and Z share neither rail. Unsupported operations are independent raw bits,
// so the approximation can lose proofs but cannot invent disjointness.
  using Decision = uint32_t;
  struct DecisionNode { uint32_t variable; Decision low, high; };
  struct Rails { Decision zero, one; };
  SmallVector<DecisionNode, 0> decisions{{UINT32_MAX, 0, 0}, {UINT32_MAX, 1, 1}};
  std::map<std::tuple<uint32_t, Decision, Decision>, Decision> uniqueDecisions;
  llvm::DenseMap<std::pair<unsigned, std::pair<Decision, Decision>>, Decision> applied;
  llvm::DenseMap<Decision, Decision> complemented;
  llvm::DenseMap<std::pair<Node, uint64_t>, Rails> bitCache;
  llvm::DenseSet<std::pair<Node, uint64_t>> bitVisiting;
  uint32_t nextVariable = 0;

  Decision decision(uint32_t variable, Decision low, Decision high) {
    if (!charge()) return 0;
    if (low == high) return low;
    auto key = std::make_tuple(variable, low, high);
    uint64_t cost = 1;
    for (size_t n = uniqueDecisions.size(); n; n >>= 1) cost += 2;
    if (!charge(cost)) return 0;
    auto found = uniqueDecisions.find(key);
    if (found != uniqueDecisions.end()) return found->second;
    if (decisions.size() >= 4096) {
      fail("owner-enable decision node budget exhausted"); return 0;
    }
    if (!charge(1 + sizeof(DecisionNode) / 8 + 8)) return 0;
    Decision id = decisions.size();
    decisions.push_back({variable, low, high});
    uniqueDecisions.emplace(key, id);
    return id;
  }
  Decision apply(bool isOr, Decision a, Decision b, unsigned depth = 0) {
    if (!charge()) return 0;
    if (depth >= 128) {
      fail("owner-enable decision recursion budget exhausted"); return 0;
    }
    if (a > b) std::swap(a, b);
    if (a == b) return a;
    if (isOr) { if (a == 0) return b; if (a == 1) return 1; }
    else { if (a == 0) return 0; if (a == 1) return b; }
    auto key = std::make_pair(unsigned(isOr), std::make_pair(a, b));
    if (auto found = applied.find(key); found != applied.end()) return found->second;
    if (applied.size() >= 4096) {
      fail("owner-enable decision query budget exhausted"); return 0;
    }
    auto left = decisions[a], right = decisions[b];
    uint32_t top = std::min(left.variable, right.variable);
    auto low = apply(isOr, left.variable == top ? left.low : a,
                     right.variable == top ? right.low : b, depth + 1);
    auto high = apply(isOr, left.variable == top ? left.high : a,
                      right.variable == top ? right.high : b, depth + 1);
    auto result = decision(top, low, high);
    if (!charge(4)) return 0;
    applied.try_emplace(key, result);
    return result;
  }
  Decision invert(Decision a, unsigned depth = 0) {
    if (!charge()) return 0;
    if (a < 2) return 1 - a;
    if (depth >= 128) { fail("owner-enable decision recursion budget exhausted"); return 0; }
    if (auto found = complemented.find(a); found != complemented.end()) return found->second;
    auto node = decisions[a];
    auto low = invert(node.low, depth + 1), high = invert(node.high, depth + 1);
    auto result = decision(node.variable, low, high);
    if (!charge(3)) return 0;
    complemented.try_emplace(a, result);
    return result;
  }
  Decision both(Decision a, Decision b) { return apply(false, a, b); }
  Decision either(Decision a, Decision b) { return apply(true, a, b); }
  Rails rawBit() {
    Decision known = decision(nextVariable++, 0, 1);
    Decision value = decision(nextVariable++, 0, 1);
    return {both(known, invert(value)), both(known, value)};
  }
  Rails bit(Node original, uint64_t ordinal, unsigned depth = 0) {
    if (!charge()) return {0, 0};
    auto normalized = canonical(original, depth);
    if (failed(normalized)) { fail("owner-enable bit normalization failed"); return {0, 0}; }
    auto key = std::make_pair(*normalized, ordinal);
    if (auto found = bitCache.find(key); found != bitCache.end()) return found->second;
    if (bitCache.size() + bitVisiting.size() >= 4096 || !bitVisiting.insert(key).second) {
      fail("owner-enable bit query budget or cycle"); return {0, 0};
    }
    auto inspected = describe(*normalized);
    if (failed(inspected)) { fail("owner-enable bit inspection failed"); return {0, 0}; }
    // describe() and recursive bit() may rehash the underlying view map.
    NodeView view = **inspected;
    if (!view.width || ordinal >= *view.width) {
      fail("owner-enable bit requires exact typed width"); return {0, 0};
    }
    Rails result{0, 0};
    if (view.fullyKnown) {
      if (!charge(view.fullyKnown->value.getCanonicalValue().size())) return result;
      llvm::APSInt value(view.fullyKnown->value.getCanonicalValue());
      bool one = ordinal < value.getBitWidth() && value[ordinal];
      result = {Decision(!one), Decision(one)};
    } else if (view.kind == NodeView::Raw) {
      result = rawBit();
    } else if (view.kind == NodeView::IsTrue) {
      auto input = canonical(view.operands[0], depth + 1);
      if (failed(input)) { fail("known-one normalization failed"); return result; }
      auto inputWidth = width(*input);
      if (failed(inputWidth) || !*inputWidth || **inputWidth != 1 || *view.width != 1) {
        fail("known-one proof requires single-bit input and result"); return result;
      }
      auto a = bit(*input, 0, depth + 1);
      result = {invert(a.one), a.one};
    } else if (view.kind == NodeView::Not) {
      auto a = bit(view.operands[0], ordinal, depth + 1);
      result = {a.one, a.zero};
    } else if (view.kind == NodeView::And || view.kind == NodeView::Or) {
      auto a = bit(view.operands[0], ordinal, depth + 1);
      auto b = bit(view.operands[1], ordinal, depth + 1);
      result = view.kind == NodeView::And
          ? Rails{either(a.zero, b.zero), both(a.one, b.one)}
          : Rails{both(a.zero, b.zero), either(a.one, b.one)};
    } else if (view.kind == NodeView::Select) {
      auto s = bit(view.operands[0], 0, depth + 1);
      auto a = bit(view.operands[1], ordinal, depth + 1);
      auto b = bit(view.operands[2], ordinal, depth + 1);
      // Equal known arms survive an unknown selector (SV ternary semantics).
      result = {
          either(either(both(s.one, a.zero), both(s.zero, b.zero)), both(a.zero, b.zero)),
          either(either(both(s.one, a.one), both(s.zero, b.one)), both(a.one, b.one))};
    } else {
      auto left = canonical(view.operands[0], depth + 1);
      auto right = canonical(view.operands[1], depth + 1);
      if (failed(left) || failed(right)) { fail("owner-enable comparison normalization failed"); return result; }
      auto aWidth = width(*left), bWidth = width(*right);
      if (failed(aWidth) || failed(bWidth) || !*aWidth || !*bWidth || **aWidth != **bWidth) {
        fail("owner-enable comparison requires equal typed widths"); return result;
      }
      // A known mismatch makes == false even if other bit pairs contain X/Z.
      result = {0, 1};
      for (uint64_t i = 0; i < **aWidth; ++i) {
        auto a = bit(*left, i, depth + 1), b = bit(*right, i, depth + 1);
        result.zero = either(result.zero, either(both(a.zero, b.one), both(a.one, b.zero)));
        result.one = both(result.one, either(both(a.zero, b.zero), both(a.one, b.one)));
        if (!reason.empty()) return {0, 0};
      }
      if (view.kind == NodeView::Ne) std::swap(result.zero, result.one);
    }
    bitVisiting.erase(key);
    if (charge(5)) bitCache.try_emplace(key, result);
    return result;
  }
  FailureOr<bool> bitDisjoint(Node a, Node b) {
    // Bound retained decision state per query, without resetting caller work.
    if (!charge(decisions.size() + applied.size() + bitCache.size())) return failure();
    decisions.resize(2); uniqueDecisions.clear(); applied.clear();
    complemented.clear(); bitCache.clear(); bitVisiting.clear(); nextVariable = 0;
    auto left = bit(a, 0), right = bit(b, 0);
    auto overlap = both(left.one, right.one);
    if (!reason.empty()) return failure();
    return overlap == 0;
  }
