#include "Dialect/ACIR/HardwareGrantProof.h"
#include "pycircuit/Dialect/ACIR/ACIRDialect.h"
#include "mlir/IR/MLIRContext.h"
#include "llvm/ADT/APSInt.h"
#include "gtest/gtest.h"
#include <array>

namespace {
using acir::ac::detail::HardwareGrantProof;
using Node = HardwareGrantProof::Node;
using View = HardwareGrantProof::NodeView;
class HardwareGrantProofTest : public ::testing::Test {
protected:
  mlir::MLIRContext context;
  llvm::SmallVector<View> nodes;
  void SetUp() override { context.loadDialect<acir::ac::ACIRDialect>(); }
  Node raw(uint64_t width = 1) {
    View v; v.width = width; nodes.push_back(v); return nodes.size() - 1;
  }
  Node constant(unsigned value, unsigned width = 1) {
    View v; v.width = width;
    v.fullyKnown = HardwareGrantProof::Constant{
        acir::ac::MathIntAttr::get(&context, llvm::APSInt(llvm::APInt(width, value), true)), width};
    nodes.push_back(v); return nodes.size() - 1;
  }
  Node op(View::Kind kind, std::initializer_list<Node> args, uint64_t width = 1) {
    View v; v.kind = kind; v.operands.assign(args); v.width = width;
    nodes.push_back(v); return nodes.size() - 1;
  }
  std::unique_ptr<HardwareGrantProof> proof(uint64_t allowance = 100000) {
    return std::make_unique<HardwareGrantProof>(
        [this](Node node, unsigned) -> mlir::FailureOr<Node> {
          if (node >= nodes.size()) return mlir::failure();
          return node;
        },
        [this](Node node) -> mlir::FailureOr<View> {
          if (node >= nodes.size()) return mlir::failure();
          return nodes[node];
        },
        [left = allowance](uint64_t units) mutable {
          if (units > left) return false;
          left -= units; return true;
        });
  }
};
TEST_F(HardwareGrantProofTest, BoundNodeIdentityIncludesZeroAndDistinctInvocations) {
  Node first = raw(), second = raw();
  Node notFirst = op(View::Not, {first}), notSecond = op(View::Not, {second});
  auto p = proof();
  auto a = p->disjoint(first, notFirst), b = p->disjoint(first, notSecond);
  ASSERT_TRUE(mlir::succeeded(a)); ASSERT_TRUE(mlir::succeeded(b));
  EXPECT_TRUE(*a); EXPECT_FALSE(*b);
}
TEST_F(HardwareGrantProofTest, EqualSelectArmsDoNotEstablishSelectorKnownness) {
  Node selector = raw(), one = constant(1), zero = constant(0);
  Node always = op(View::Select, {selector, one, one});
  Node inverse = op(View::Not, {selector});
  Node gated = op(View::Select, {selector, one, zero});
  auto p = proof();
  auto equalArms = p->disjoint(always, inverse);
  auto complementary = p->disjoint(gated, inverse);
  ASSERT_TRUE(mlir::succeeded(equalArms)); ASSERT_TRUE(mlir::succeeded(complementary));
  EXPECT_FALSE(*equalArms); EXPECT_TRUE(*complementary);
}
TEST_F(HardwareGrantProofTest, PossibleAddressCollisionRetainsUnknownEquality) {
  // Index Node zero is legal and must not be confused with 'no collision'.
  Node i = raw(2), j = raw(2), a = raw(), b = raw();
  Node unequal = op(View::Ne, {i, j});
  Node equal = op(View::Eq, {i, j});
  Node notA = op(View::Not, {a});
  Node grant = op(View::And, {b, op(View::Or, {notA, unequal})});
  Node invalid = op(View::And, {b, op(View::Or, {notA, equal})});
  auto p = proof();
  auto separated = p->disjointAtAddress(a, grant, i, j);
  auto unscoped = p->disjoint(a, grant);
  auto overlapping = p->disjointAtAddress(a, invalid, i, j);
  ASSERT_TRUE(mlir::succeeded(separated)); ASSERT_TRUE(mlir::succeeded(unscoped));
  ASSERT_TRUE(mlir::succeeded(overlapping));
  EXPECT_TRUE(*separated); EXPECT_FALSE(*unscoped); EXPECT_FALSE(*overlapping);
  // Independent four-state oracle: a possible collision is any equality not
  // known false. X and Z never count as a known-one enable.
  constexpr int X = -1, Z = -2;
  auto conjunction = [](int x, int y) { return x == 0 || y == 0 ? 0 : x == 1 && y == 1 ? 1 : X; };
  auto disjunction = [](int x, int y) { return x == 1 || y == 1 ? 1 : x == 0 && y == 0 ? 0 : X; };
  for (int x : {0, 1, X, Z}) for (int y : {0, 1, X, Z})
    for (int left : {0, 1, 2, 3, X, Z}) for (int right : {0, 1, 2, 3, X, Z}) {
      int eq = left < 0 || right < 0 ? X : int(left == right);
      int ne = eq < 0 ? X : 1 - eq;
      int inv = x < 0 ? X : 1 - x;
      int enabled = conjunction(y, disjunction(inv, ne));
      if (eq != 0) EXPECT_FALSE(x == 1 && enabled == 1);
    }
}
TEST_F(HardwareGrantProofTest, ReservedAdapterNodeIdentitiesFailClosed) {
  auto p = proof();
  Node first = raw();
  EXPECT_TRUE(mlir::failed(p->disjoint(first, UINT64_MAX)));
  EXPECT_FALSE(p->failureReason().empty());
}
TEST_F(HardwareGrantProofTest, WidthAndConstantAuthorityRemainExact) {
  Node a = raw(), b = raw(), i = raw(4), j = raw(8);
  Node small = constant(3, 4), same = constant(3, 8), other = constant(7, 8);
  auto p = proof();
  auto dynamic = p->disjointAtAddress(a, b, i, j);
  auto equal = p->disjointAtAddress(a, b, small, same);
  auto different = p->disjointAtAddress(a, b, small, other);
  ASSERT_TRUE(mlir::succeeded(dynamic)); ASSERT_TRUE(mlir::succeeded(equal));
  ASSERT_TRUE(mlir::succeeded(different));
  EXPECT_FALSE(*dynamic); EXPECT_FALSE(*equal); EXPECT_TRUE(*different);
  auto exhausted = proof(1);
  EXPECT_TRUE(mlir::failed(exhausted->disjoint(a, b)));
}

TEST_F(HardwareGrantProofTest, HierarchicalAlternativesRetainCorrelatedFields) {
  Node phase = raw(2), kind = raw(), received = raw(2), mask = raw(2);
  Node active = op(View::Eq, {phase, constant(1, 2)});
  Node read = op(View::Eq, {kind, constant(0)});
  Node write = op(View::Eq, {kind, constant(1)});
  Node full = op(View::Eq, {received, constant(3, 2)});
  Node next = op(View::Or, {received, mask}, 2);
  Node progress = op(View::Ne, {received, next});
  Node take = op(View::And, {active, op(View::Or, {read, op(View::And, {write, full})})});
  Node receive = op(View::And, {active, op(View::And, {write, progress})});
  auto p = proof();
  auto disjoint = p->disjoint(take, receive);
  ASSERT_TRUE(mlir::succeeded(disjoint)); EXPECT_TRUE(*disjoint);
  // Removing actual progress permits a capture/data collision at received=3.
  auto overlapping = p->disjoint(take, op(View::And, {active, write}));
  ASSERT_TRUE(mlir::succeeded(overlapping)); EXPECT_FALSE(*overlapping);
}
TEST_F(HardwareGrantProofTest, FourStateOracleChecksAllGrantPairs) {
  Node a = raw(), b = raw(), c = raw(), zero = constant(0), one = constant(1);
  Node ab = op(View::And, {a, b}), ac = op(View::And, {a, c});
  Node either = op(View::Or, {b, c});
  Node inverse = op(View::Not, {a});
  op(View::And, {a, either});
  op(View::Or, {ab, ac});
  op(View::Select, {c, a, b});
  op(View::Select, {c, one, one});
  op(View::Select, {c, zero, one});
  op(View::Select, {c, ab, ac});
  op(View::Eq, {a, b});
  op(View::Ne, {a, b});
  op(View::Eq, {inverse, b});
  // Independent scalar 0/1/X/Z evaluation, not the two-rail construction.
  constexpr int X = 2;
  auto and4 = [](int x, int y) { return x == 0 || y == 0 ? 0 : x == 1 && y == 1 ? 1 : X; };
  auto or4 = [](int x, int y) { return x == 1 || y == 1 ? 1 : x == 0 && y == 0 ? 0 : X; };
  std::vector<std::vector<int>> rows;
  for (int x = 0; x < 4; ++x) for (int y = 0; y < 4; ++y) for (int z = 0; z < 4; ++z) {
    std::vector<int> values(nodes.size(), X);
    values[a] = x; values[b] = y; values[c] = z;
    for (size_t i = 3; i < nodes.size(); ++i) {
      auto &n = nodes[i];
      if (n.fullyKnown) { values[i] = llvm::APSInt(n.fullyKnown->value.getCanonicalValue()).isZero() ? 0 : 1; continue; }
      int p = values[n.operands[0]], q = n.operands.size() > 1 ? values[n.operands[1]] : X;
      if (n.kind == View::Not) values[i] = p < 2 ? 1 - p : X;
      else if (n.kind == View::And) values[i] = and4(p, q);
      else if (n.kind == View::Or) values[i] = or4(p, q);
      else if (n.kind == View::Eq || n.kind == View::Ne)
        values[i] = p < 2 && q < 2 ? int((p == q) == (n.kind == View::Eq)) : X;
      else if (n.kind == View::Select) {
        int r = values[n.operands[2]];
        values[i] = p == 1 ? q : p == 0 ? r : q == r ? q : X;
      }
    }
    rows.push_back(std::move(values));
  }
  for (size_t i = 0; i < nodes.size(); ++i) for (size_t j = i; j < nodes.size(); ++j) {
    bool expected = true;
    for (const auto &row : rows) expected &= !(row[i] == 1 && row[j] == 1);
    auto p = proof(); auto actual = p->disjoint(i, j);
    ASSERT_TRUE(mlir::succeeded(actual)) << i << "," << j << ": " << p->failureReason().str();
    EXPECT_EQ(*actual, expected) << i << "," << j;
  }
}
TEST_F(HardwareGrantProofTest, IndependentFieldsAndUnknownValuesCannotAcquireFacts) {
  Node first = raw(2), second = raw(2), full = constant(3, 2), mask = raw(2);
  Node ready = op(View::Eq, {first, full});
  Node next = op(View::Or, {second, mask}, 2);
  Node progress = op(View::Ne, {second, next});
  auto p = proof(); auto result = p->disjoint(ready, progress);
  ASSERT_TRUE(mlir::succeeded(result)); EXPECT_FALSE(*result);
  // An opaque case-equality result cannot be substituted for logical equality.
  Node caseEquality = raw();
  auto opaque = p->disjoint(op(View::Not, {caseEquality}), progress);
  ASSERT_TRUE(mlir::succeeded(opaque)); EXPECT_FALSE(*opaque);
}

TEST_F(HardwareGrantProofTest,
       ConstantAddressCollisionStillUsesComplementaryEnableProof) {
  Node enabled = raw();
  Node disabled = op(View::Not, {enabled});
  Node address = constant(3, 4);
  Node sameAddress = constant(3, 4);
  Node otherAddress = constant(7, 4);
  Node widerSameAddress = constant(3, 8);
  auto p = proof();

  auto complementary =
      p->disjointAtAddress(enabled, disabled, address, sameAddress);
  auto overlapping =
      p->disjointAtAddress(enabled, enabled, address, sameAddress);
  auto separate =
      p->disjointAtAddress(enabled, enabled, address, otherAddress);
  auto widerComplementary =
      p->disjointAtAddress(enabled, disabled, address, widerSameAddress);
  auto widerOverlapping =
      p->disjointAtAddress(enabled, enabled, address, widerSameAddress);
  ASSERT_TRUE(mlir::succeeded(complementary));
  ASSERT_TRUE(mlir::succeeded(overlapping));
  ASSERT_TRUE(mlir::succeeded(separate));
  ASSERT_TRUE(mlir::succeeded(widerComplementary));
  ASSERT_TRUE(mlir::succeeded(widerOverlapping));
  // A known collision needs the enable proof; unequal known addresses alone
  // suffice. Numeric address equality is unaffected by its storage width.
  EXPECT_TRUE(*complementary);
  EXPECT_FALSE(*overlapping);
  EXPECT_TRUE(*separate);
  EXPECT_TRUE(*widerComplementary);
  EXPECT_FALSE(*widerOverlapping);
}

} // namespace
