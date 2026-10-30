#include "Dialect/ACIR/SourceValueSemantics.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Diagnostics.h"
#include "pycircuit/Dialect/ACIR/ACIRAttributes.h"
#include "pycircuit/Dialect/ACIR/ACIRDialect.h"
#include "pycircuit/Dialect/ACIR/SourceValueNames.h"
#include "mlir/IR/OperationSupport.h"
#include "llvm/ADT/APSInt.h"
#include "llvm/Support/raw_ostream.h"
#include "gtest/gtest.h"

#include <array>
#include <string>

namespace acir::ac {
namespace {
using namespace detail;

class SourceValueNamesTest : public ::testing::Test {
protected:
    SourceValueNamesTest() : builder(&context) {
        context.allowUnregisteredDialects();
    }
    mlir::OwningOpRef<mlir::Operation *> producer() {
        mlir::OperationState state(site, "test.named_values");
        state.addTypes({builder.getI8Type(), builder.getI8Type()});
        return mlir::OwningOpRef<mlir::Operation *>(mlir::Operation::create(state));
    }
    mlir::MLIRContext context;
    mlir::Builder builder;
    mlir::Location site = mlir::FileLineColLoc::get(&context, "names.py", 7, 3);
};

TEST_F(SourceValueNamesTest, NamesArePerResultAndRetainSharedAliases) {
    auto operation = producer();
    auto first = operation->getResult(0), second = operation->getResult(1);
    retainSourceValueName(first, "total", "Module.rule", site);
    retainSourceValueName(second, "index", "Module.rule", site);
    retainSourceValueName(first, "shared", "Module.rule", site);
    retainSourceValueName(first, "shared", "Module.rule", site);
    auto firstNames = sourceValueNames(first), secondNames = sourceValueNames(second);
    ASSERT_EQ(firstNames.size(), 2u);
    ASSERT_EQ(secondNames.size(), 1u);
    EXPECT_EQ(firstNames.front().name.getValue(), "total");
    EXPECT_EQ(firstNames.back().name.getValue(), "shared");
    EXPECT_EQ(secondNames.front().name.getValue(), "index");
}

TEST_F(SourceValueNamesTest, NamesDoNotChangeCseEquivalenceHashOrLiveness) {
    auto first = producer(), second = producer();
    auto attributes = first->getAttrDictionary();
    retainSourceValueName(first->getResult(0), "total", "Module.rule", site);
    retainSourceValueName(second->getResult(0), "other", "Other.rule", site);
    EXPECT_EQ(first->getAttrDictionary(), attributes);
    EXPECT_TRUE(first->getResult(0).use_empty());
    EXPECT_TRUE(mlir::OperationEquivalence::isEquivalentTo(first.get(), second.get(),
        mlir::OperationEquivalence::IgnoreLocations));
    auto hash = [](mlir::Operation *operation) {
        return mlir::OperationEquivalence::computeHash(operation,
            mlir::OperationEquivalence::ignoreHashValue,
            mlir::OperationEquivalence::ignoreHashValue,
            mlir::OperationEquivalence::IgnoreLocations);
    };
    EXPECT_EQ(hash(first.get()), hash(second.get()));
}

TEST_F(SourceValueNamesTest, ReplacementRetainsAliasesAcrossResultNumbers) {
    auto original = producer(), replacement = producer();
    retainSourceValueName(original->getResult(1), "saved", "Source.rule", site);
    retainSourceValueName(replacement->getResult(0), "shared", "Other.rule", site);
    retainSourceValueNames(original->getResult(1), replacement->getResult(0));
    auto names = sourceValueNames(replacement->getResult(0));
    ASSERT_EQ(names.size(), 2u);
    EXPECT_EQ(names.back().name.getValue(), "saved");
    EXPECT_TRUE(sourceValueNames(replacement->getResult(1)).empty());
}

TEST_F(SourceValueNamesTest, ArgumentAliasesTransferToOperationResults) {
    mlir::Block block;
    auto argument = block.addArgument(builder.getI8Type(), site);
    retainSourceValueName(argument, "incoming", "Module.rule", site);
    auto replacement = producer();
    retainSourceValueNames(argument, replacement->getResult(1));
    auto names = sourceValueNames(replacement->getResult(1));
    ASSERT_EQ(names.size(), 1u);
    EXPECT_EQ(names.front().name.getValue(), "incoming");
    EXPECT_TRUE(argument.use_empty());
}

TEST_F(SourceValueNamesTest, AuthenticationRetainsTheOriginalSourceLocation) {
    auto operation = producer();
    retainSourceValueName(operation->getResult(0), "total", "Module.rule", site);
    EXPECT_EQ(sourceIdentityLocation(operation->getLoc()), site);
    auto different = mlir::FileLineColLoc::get(&context, "other.py", 8, 1);
    operation->setLoc(different);
    retainSourceValueName(operation->getResult(0), "total", "Module.rule", site);
    EXPECT_EQ(sourceIdentityLocation(operation->getLoc()), different);
    EXPECT_NE(sourceIdentityLocation(operation->getLoc()), site);
}

TEST_F(SourceValueNamesTest, DerivedPositionDoesNotAuthorizeAnotherValueName) {
    auto original = producer();
    retainSourceValueName(original->getResult(0), "accepted", "Module.rule", site);
    // Even matching operation names and types do not make a fresh result the
    // original binding. Only a clone or an explicit value mapping may do that.
    mlir::OperationState state(sourceIdentityLocation(original->getLoc()), "test.named_values");
    state.addTypes(original->getResultTypes());
    mlir::OwningOpRef<mlir::Operation *> derived(mlir::Operation::create(state));
    EXPECT_TRUE(sourceValueNames(derived->getResult(0)).empty());
    mlir::OwningOpRef<mlir::Operation *> copy(original->clone());
    ASSERT_EQ(sourceValueNames(copy->getResult(0)).size(), 1u);
    retainSourceValueNames(original->getResult(0), derived->getResult(1));
    ASSERT_EQ(sourceValueNames(derived->getResult(1)).size(), 1u);
    EXPECT_TRUE(sourceValueNames(derived->getResult(0)).empty());
}

TEST_F(SourceValueNamesTest, NestedDiagnosticPositionsDoNotLeakBindings) {
    auto original = producer();
    retainSourceValueName(original->getResult(0), "accepted", "Module.rule", site);
    auto named = mlir::NameLoc::get(builder.getStringAttr("diagnostic"), original->getLoc());
    auto metadata = builder.getStringAttr("unrelated-context");
    auto nested = mlir::FusedLoc::get(&context, {named, site}, metadata);
    auto position = sourceIdentityLocation(nested);
    auto fused = mlir::dyn_cast<mlir::FusedLoc>(position);
    ASSERT_TRUE(fused);
    EXPECT_EQ(fused.getMetadata(), metadata);
    auto other = producer();
    other->setLoc(position);
    EXPECT_TRUE(sourceValueNames(other->getResult(0)).empty());
}

TEST_F(SourceValueNamesTest, RtlOwnershipHasNoSemanticAttributesUsesOrIdentity) {
    auto first = producer(), second = producer();
    auto owner = builder.getDictionaryAttr({builder.getNamedAttr("definition", builder.getStringAttr("Counter"))});
    retainSourceRtlOwner(first.get(), owner);
    EXPECT_EQ(sourceIdentityLocation(first->getLoc()), site);
    EXPECT_TRUE(first->getResult(0).use_empty());
    EXPECT_EQ(first->getAttrDictionary(), second->getAttrDictionary());
    EXPECT_TRUE(mlir::OperationEquivalence::isEquivalentTo(first.get(), second.get(),
        mlir::OperationEquivalence::IgnoreLocations));
    auto hash = [](mlir::Operation *operation) {
        return mlir::OperationEquivalence::computeHash(operation,
            mlir::OperationEquivalence::ignoreHashValue,
            mlir::OperationEquivalence::ignoreHashValue,
            mlir::OperationEquivalence::IgnoreLocations);
    };
    EXPECT_EQ(hash(first.get()), hash(second.get()));
}

TEST_F(SourceValueNamesTest, SharedReplacementRetainsAllRtlOwnersAndBindings) {
    auto first = producer(), second = producer();
    auto owner = [&](llvm::StringRef name) {
        return builder.getDictionaryAttr({builder.getNamedAttr("definition", builder.getStringAttr(name))});
    };
    retainSourceRtlOwner(first.get(), owner("Counter"));
    retainSourceRtlOwner(second.get(), owner("Caller"));
    retainSourceValueName(first->getResult(0), "saved", "Counter", site);
    retainSourceValueNames(first->getResult(0), second->getResult(1));
    EXPECT_EQ(sourceRtlOwners(second->getLoc()).size(), 2u);
    EXPECT_EQ(sourceValueNames(second->getResult(1)).size(), 1u);
    EXPECT_TRUE(sourceValueNames(second->getResult(0)).empty());
    EXPECT_EQ(sourceIdentityLocation(second->getLoc()), site);
}

TEST_F(SourceValueNamesTest, DisplayRolesArePerResultAndDoNotBecomeBindings) {
    auto operation = producer();
    auto role = builder.getDictionaryAttr({builder.getNamedAttr("scope", builder.getStringAttr("finish")),
        builder.getNamedAttr("role", builder.getStringAttr("condition"))});
    retainSourceRtlRole(operation->getResult(1), role);
    retainSourceRtlRole(operation->getResult(1), role);
    EXPECT_TRUE(sourceRtlRoles(operation->getResult(0)).empty());
    ASSERT_EQ(sourceRtlRoles(operation->getResult(1)).size(), 1u);
    EXPECT_TRUE(sourceValueNames(operation->getResult(1)).empty());
    EXPECT_EQ(sourceIdentityLocation(operation->getLoc()), site);
}

TEST_F(SourceValueNamesTest, DisplayRolesKeepCseHashEquivalenceAndDeadValueLiveness) {
    auto first = producer(), second = producer();
    retainSourceRtlRole(first->getResult(0), builder.getDictionaryAttr({
        builder.getNamedAttr("scope", builder.getStringAttr("first"))}));
    retainSourceRtlRole(second->getResult(0), builder.getDictionaryAttr({
        builder.getNamedAttr("scope", builder.getStringAttr("second"))}));
    EXPECT_EQ(first->getAttrDictionary(), second->getAttrDictionary());
    EXPECT_TRUE(first->getResult(0).use_empty());
    EXPECT_TRUE(mlir::OperationEquivalence::isEquivalentTo(first.get(), second.get(),
        mlir::OperationEquivalence::IgnoreLocations));
    auto hash = [](mlir::Operation *operation) {
        return mlir::OperationEquivalence::computeHash(operation,
            mlir::OperationEquivalence::ignoreHashValue,
            mlir::OperationEquivalence::ignoreHashValue,
            mlir::OperationEquivalence::IgnoreLocations);
    };
    EXPECT_EQ(hash(first.get()), hash(second.get()));
}

TEST_F(SourceValueNamesTest, SharedReplacementRetainsEveryDisplayRoleAtItsNewResult) {
    auto first = producer(), second = producer();
    for (auto [operation, name] : {std::pair(first.get(), "receive"), std::pair(second.get(), "release")})
        retainSourceRtlRole(operation->getResult(1), builder.getDictionaryAttr({
            builder.getNamedAttr("scope", builder.getStringAttr(name))}));
    retainSourceValueNames(first->getResult(1), second->getResult(1));
    ASSERT_EQ(sourceRtlRoles(second->getResult(1)).size(), 2u);
    EXPECT_TRUE(sourceRtlRoles(second->getResult(0)).empty());
    EXPECT_TRUE(sourceValueNames(second->getResult(1)).empty());
    EXPECT_EQ(sourceIdentityLocation(second->getLoc()), site);
}

class SourceValueSemanticsTest : public ::testing::Test {
protected:
  SourceValueSemanticsTest() : builder(&context) {
    context.loadDialect<ACIRDialect>();
  }
  MathIntAttr integer(llvm::StringRef value) {
    return MathIntAttr::get(&context, llvm::APSInt(value));
  }
  mlir::Attribute boolean(bool value) { return builder.getBoolAttr(value); }
  mlir::FailureOr<mlir::Attribute>
  evaluate(ValueOpcode opcode, llvm::ArrayRef<mlir::Attribute> values) {
    diagnostics.clear();
    mlir::ScopedDiagnosticHandler capture(&context, [&](mlir::Diagnostic &d) {
      llvm::raw_string_ostream stream(diagnostics);
      d.print(stream);
      return mlir::success();
    });
    auto emit = [&] {
      return mlir::emitError(mlir::UnknownLoc::get(&context));
    };
    return evaluateValue(opcode, values, emit);
  }
  void expectInteger(ValueOpcode opcode, llvm::ArrayRef<mlir::Attribute> values,
                     llvm::StringRef expected) {
    auto result = evaluate(opcode, values);
    ASSERT_TRUE(mlir::succeeded(result)) << diagnostics;
    ASSERT_TRUE(mlir::isa<MathIntAttr>(*result));
    EXPECT_EQ(mlir::cast<MathIntAttr>(*result).getCanonicalValue(), expected);
    EXPECT_TRUE(diagnostics.empty()) << diagnostics;
  }
  void expectBoolean(ValueOpcode opcode, llvm::ArrayRef<mlir::Attribute> values,
                     bool expected) {
    auto result = evaluate(opcode, values);
    ASSERT_TRUE(mlir::succeeded(result)) << diagnostics;
    ASSERT_TRUE(mlir::isa<mlir::BoolAttr>(*result));
    EXPECT_EQ(mlir::cast<mlir::BoolAttr>(*result).getValue(), expected);
  }
  void rejects(ValueOpcode opcode, llvm::ArrayRef<mlir::Attribute> values) {
    EXPECT_TRUE(mlir::failed(evaluate(opcode, values)));
    EXPECT_FALSE(diagnostics.empty());
  }

  mlir::MLIRContext context;
  mlir::Builder builder;
  std::string diagnostics;
};

struct OpcodeCase {
  llvm::StringRef name;
  ValueOpcode opcode;
  unsigned arity;
  ValueKindConstraint operand;
  ValueKind result;
  ValueEvaluation evaluation = ValueEvaluation::Strict;
  bool mayCheck = false;
};

// Expectations come from the packet's operation semantics, independently of
// the implementation's metadata table or any generated emitter.
constexpr OpcodeCase cases[] = {
    {"neg", ValueOpcode::Neg, 1, ValueKindConstraint::Integer,
     ValueKind::Integer},
    {"invert", ValueOpcode::Invert, 1, ValueKindConstraint::Integer,
     ValueKind::Integer},
    {"not", ValueOpcode::Not, 1, ValueKindConstraint::Boolean,
     ValueKind::Boolean},
    {"to_int", ValueOpcode::ToInt, 1, ValueKindConstraint::BooleanOrInteger,
     ValueKind::Integer},
    {"add", ValueOpcode::Add, 2, ValueKindConstraint::Integer,
     ValueKind::Integer},
    {"sub", ValueOpcode::Sub, 2, ValueKindConstraint::Integer,
     ValueKind::Integer},
    {"mul", ValueOpcode::Mul, 2, ValueKindConstraint::Integer,
     ValueKind::Integer},
    {"floordiv", ValueOpcode::FloorDiv, 2, ValueKindConstraint::Integer,
     ValueKind::Integer, ValueEvaluation::Strict, true},
    {"mod", ValueOpcode::Mod, 2, ValueKindConstraint::Integer,
     ValueKind::Integer, ValueEvaluation::Strict, true},
    {"and_bits", ValueOpcode::AndBits, 2, ValueKindConstraint::Integer,
     ValueKind::Integer},
    {"or_bits", ValueOpcode::OrBits, 2, ValueKindConstraint::Integer,
     ValueKind::Integer},
    {"xor_bits", ValueOpcode::XorBits, 2, ValueKindConstraint::Integer,
     ValueKind::Integer},
    {"shl", ValueOpcode::Shl, 2, ValueKindConstraint::Integer,
     ValueKind::Integer, ValueEvaluation::Strict, true},
    {"shr", ValueOpcode::Shr, 2, ValueKindConstraint::Integer,
     ValueKind::Integer, ValueEvaluation::Strict, true},
    {"eq", ValueOpcode::Eq, 2, ValueKindConstraint::Integer,
     ValueKind::Boolean},
    {"ne", ValueOpcode::Ne, 2, ValueKindConstraint::Integer,
     ValueKind::Boolean},
    {"lt", ValueOpcode::Lt, 2, ValueKindConstraint::Integer,
     ValueKind::Boolean},
    {"le", ValueOpcode::Le, 2, ValueKindConstraint::Integer,
     ValueKind::Boolean},
    {"gt", ValueOpcode::Gt, 2, ValueKindConstraint::Integer,
     ValueKind::Boolean},
    {"ge", ValueOpcode::Ge, 2, ValueKindConstraint::Integer,
     ValueKind::Boolean},
    {"and_bool", ValueOpcode::AndBool, 2, ValueKindConstraint::Boolean,
     ValueKind::Boolean, ValueEvaluation::AndShortCircuit},
    {"or_bool", ValueOpcode::OrBool, 2, ValueKindConstraint::Boolean,
     ValueKind::Boolean, ValueEvaluation::OrShortCircuit},
};

TEST_F(SourceValueSemanticsTest, ClosedNamesAndMetadataDescribeKindsAndSafety) {
  for (const auto &item : cases) {
    SCOPED_TRACE(item.name.str());
    auto opcode = parseValueOpcode(item.name);
    ASSERT_TRUE(opcode);
    EXPECT_EQ(*opcode, item.opcode);
    auto info = getValueOpcodeInfo(*opcode);
    EXPECT_EQ(info.arity, item.arity);
    for (unsigned operand = 0; operand < item.arity; ++operand)
      EXPECT_EQ(info.operands[operand], item.operand);
    EXPECT_EQ(info.result, item.result);
    EXPECT_EQ(info.evaluation, item.evaluation);
    EXPECT_EQ(info.mayCheck, item.mayCheck);
  }
  for (llvm::StringRef name : {"", "unknown", "ADD", "div", "int_cast", "add "})
    EXPECT_FALSE(parseValueOpcode(name)) << name.str();
}

TEST_F(SourceValueSemanticsTest,
       MathematicalArithmeticDoesNotWrapAtHostOrOperandWidth) {
  const auto power64 = integer("18446744073709551616");
  const auto power128 = integer("340282366920938463463374607431768211456");
  expectInteger(ValueOpcode::Add, {power128, integer("1")},
                "340282366920938463463374607431768211457");
  expectInteger(ValueOpcode::Sub, {integer("0"), power128},
                "-340282366920938463463374607431768211456");
  expectInteger(ValueOpcode::Mul, {power64, power64},
                "340282366920938463463374607431768211456");
  expectInteger(ValueOpcode::Mul, {integer("-18446744073709551616"), power64},
                "-340282366920938463463374607431768211456");
  expectInteger(ValueOpcode::Neg,
                {integer("-170141183460469231731687303715884105728")},
                "170141183460469231731687303715884105728");
  expectInteger(
      ValueOpcode::Add,
      {integer("-18446744073709551617"), integer("18446744073709551616")},
      "-1");
  expectInteger(ValueOpcode::Sub,
                {integer("-1"), integer("18446744073709551616")},
                "-18446744073709551617");
}

TEST_F(SourceValueSemanticsTest,
       FloorDivisionAndModuloFollowAllSignCombinations) {
  struct Division {
    const char *a;
    const char *b;
    const char *q;
    const char *r;
  };
  for (const auto &item : std::array<Division, 6>{{{"7", "3", "2", "1"},
                                                   {"-7", "3", "-3", "2"},
                                                   {"7", "-3", "-3", "-2"},
                                                   {"-7", "-3", "2", "-1"},
                                                   {"-6", "3", "-2", "0"},
                                                   {"6", "-3", "-2", "0"}}}) {
    auto a = integer(item.a), b = integer(item.b);
    expectInteger(ValueOpcode::FloorDiv, {a, b}, item.q);
    expectInteger(ValueOpcode::Mod, {a, b}, item.r);
    auto q = evaluate(ValueOpcode::FloorDiv, {a, b});
    auto r = evaluate(ValueOpcode::Mod, {a, b});
    ASSERT_TRUE(mlir::succeeded(q) && mlir::succeeded(r));
    auto product = evaluate(ValueOpcode::Mul, {*q, b});
    ASSERT_TRUE(mlir::succeeded(product));
    expectInteger(ValueOpcode::Add, {*product, *r}, item.a);
  }
  expectInteger(
      ValueOpcode::FloorDiv,
      {integer("-170141183460469231731687303715884105728"), integer("-1")},
      "170141183460469231731687303715884105728");
  expectInteger(
      ValueOpcode::Mod,
      {integer("-170141183460469231731687303715884105728"), integer("-1")},
      "0");
  expectInteger(ValueOpcode::FloorDiv,
                {integer("18446744073709551617"), integer("3")},
                "6148914691236517205");
  expectInteger(ValueOpcode::Mod,
                {integer("18446744073709551617"), integer("3")}, "2");
}

TEST_F(SourceValueSemanticsTest,
       NegativeBitwiseValuesUseMathematicalSignExtension) {
  expectInteger(ValueOpcode::Invert, {integer("0")}, "-1");
  expectInteger(ValueOpcode::Invert, {integer("-1")}, "0");
  expectInteger(ValueOpcode::Invert, {integer("18446744073709551616")},
                "-18446744073709551617");
  expectInteger(ValueOpcode::AndBits, {integer("-5"), integer("3")}, "3");
  expectInteger(ValueOpcode::OrBits, {integer("-5"), integer("3")}, "-5");
  expectInteger(ValueOpcode::XorBits, {integer("-5"), integer("3")}, "-8");
  expectInteger(ValueOpcode::AndBits,
                {integer("-1"), integer("18446744073709551616")},
                "18446744073709551616");
  expectInteger(ValueOpcode::OrBits,
                {integer("-1"), integer("18446744073709551616")}, "-1");
  expectInteger(ValueOpcode::XorBits,
                {integer("-1"), integer("18446744073709551616")},
                "-18446744073709551617");
}

TEST_F(SourceValueSemanticsTest,
       ShiftsKeepArithmeticMeaningAndHandleHugeCounts) {
  expectInteger(ValueOpcode::Shl, {integer("-3"), integer("5")}, "-96");
  expectInteger(ValueOpcode::Shl, {integer("1"), integer("100")},
                "1267650600228229401496703205376");
  expectInteger(ValueOpcode::Shr, {integer("-5"), integer("1")}, "-3");
  expectInteger(ValueOpcode::Shr, {integer("-5"), integer("2")}, "-2");
  expectInteger(ValueOpcode::Shr,
                {integer("-18446744073709551617"), integer("64")}, "-2");
  expectInteger(ValueOpcode::Shr,
                {integer("18446744073709551617"), integer("64")}, "1");
  const auto huge = integer("1267650600228229401496703205376");
  expectInteger(ValueOpcode::Shr, {integer("-5"), huge}, "-1");
  expectInteger(ValueOpcode::Shr, {integer("5"), huge}, "0");
  expectInteger(ValueOpcode::Shr, {integer("0"), huge}, "0");
  expectInteger(ValueOpcode::Shl, {integer("0"), huge}, "0");
  // Nonzero left shift would need an unrepresentable compiler allocation width;
  // diagnosing capacity is different from wrapping or changing mathematical
  // value.
  rejects(ValueOpcode::Shl, {integer("1"), huge});
}

TEST_F(SourceValueSemanticsTest, IntegerComparisonsRemainExactBeyondHostWidth) {
  const auto smaller = integer("340282366920938463463374607431768211456");
  const auto greater = integer("340282366920938463463374607431768211457");
  expectBoolean(ValueOpcode::Eq, {smaller, smaller}, true);
  expectBoolean(ValueOpcode::Eq, {smaller, greater}, false);
  expectBoolean(ValueOpcode::Ne, {smaller, greater}, true);
  expectBoolean(ValueOpcode::Lt, {smaller, greater}, true);
  expectBoolean(ValueOpcode::Le, {smaller, smaller}, true);
  expectBoolean(ValueOpcode::Gt, {greater, smaller}, true);
  expectBoolean(ValueOpcode::Ge, {smaller, smaller}, true);
  expectBoolean(ValueOpcode::Lt,
                {integer("-18446744073709551617"), integer("-1")}, true);
}

TEST_F(SourceValueSemanticsTest, BooleansAndIntegerZeroOrOneAreDifferentKinds) {
  for (bool bit : {false, true}) {
    expectBoolean(ValueOpcode::Not, {boolean(bit)}, !bit);
    expectInteger(ValueOpcode::ToInt, {boolean(bit)}, bit ? "1" : "0");
    expectInteger(ValueOpcode::ToInt, {integer(bit ? "1" : "0")},
                  bit ? "1" : "0");
    rejects(ValueOpcode::Not, {integer(bit ? "1" : "0")});
    rejects(ValueOpcode::Eq, {boolean(bit), integer(bit ? "1" : "0")});
    rejects(ValueOpcode::Add, {boolean(bit), integer("1")});
  }
  struct Truth {
    bool a, b, conjunction, disjunction;
  };
  for (const auto &row : std::array<Truth, 4>{{{false, false, false, false},
                                               {false, true, false, true},
                                               {true, false, false, true},
                                               {true, true, true, true}}}) {
    expectBoolean(ValueOpcode::AndBool, {boolean(row.a), boolean(row.b)},
                  row.conjunction);
    expectBoolean(ValueOpcode::OrBool, {boolean(row.a), boolean(row.b)},
                  row.disjunction);
  }
  rejects(ValueOpcode::AndBool, {boolean(false), integer("0")});
  rejects(ValueOpcode::OrBool, {boolean(true), integer("1")});
  expectInteger(ValueOpcode::ToInt,
                {integer("-340282366920938463463374607431768211456")},
                "-340282366920938463463374607431768211456");
}

TEST_F(SourceValueSemanticsTest, ArithmeticErrorsAndMalformedValuesDiagnose) {
  for (auto opcode : {ValueOpcode::FloorDiv, ValueOpcode::Mod})
    rejects(opcode, {integer("-7"), integer("0")});
  for (auto opcode : {ValueOpcode::Shl, ValueOpcode::Shr}) {
    rejects(opcode, {integer("5"), integer("-1")});
    rejects(opcode, {integer("0"), integer("-1")});
  }
  for (const auto &item : cases) {
    SCOPED_TRACE(item.name.str());
    rejects(item.opcode, {});
    if (item.arity == 2)
      rejects(item.opcode, {integer("1")});
    else
      rejects(item.opcode, {integer("1"), integer("2")});
  }
  rejects(ValueOpcode::Add, {builder.getI64IntegerAttr(1), integer("2")});
  rejects(ValueOpcode::ToInt, {builder.getStringAttr("1")});
  rejects(ValueOpcode::Neg, {mlir::Attribute{}});
  rejects(ValueOpcode::Mul, {integer("2"), builder.getDictionaryAttr({})});
}

} // namespace
} // namespace acir::ac
