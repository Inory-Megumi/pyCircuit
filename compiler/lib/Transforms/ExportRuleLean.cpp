#include "pycircuit/Dialect/ACIR/HardwareAnalysis.h"
#include "pycircuit/Dialect/ACIR/SourceMethodAnalysis.h"
#include "pycircuit/Dialect/ACIR/SourceTransactionStateAnalysis.h"
#include "pycircuit/Dialect/ACIR/SourceUnitValidation.h"
#include "pycircuit/Transforms/Passes.h"

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"
#include <optional>
#include <string>

using namespace mlir;

namespace acir {
namespace {

// This is a bounded serializer of existing typed operations and state plans.
// It neither evaluates hardware nor reconstructs source-language semantics.
class RuleLeanExporter {
public:
  RuleLeanExporter(ac::ModuleOp module, ac::HardwareAnalysis &hardware,
                   const ac::SourceTransactionStateAnalysis &analysis)
      : module(module), hardware(hardware), analysis(analysis) {
    bindings.owner = module;
  }

  FailureOr<std::string> run() {
    if (failed(inventory()) || failed(order()) || failed(emitModel()))
      return failure();
    return std::move(text);
  }

private:
  static constexpr uint64_t maxNodes = 100000;
  static constexpr size_t maxText = 8 * 1024 * 1024;
  static constexpr unsigned maxDepth = 256;

  LogicalResult error(Operation *site, StringRef message) {
    return site->emitError() << "Rule Lean export: " << message;
  }
  LogicalResult pay(Operation *site, unsigned depth = 0) {
    if (depth > maxDepth || nodes == maxNodes)
      return error(site, "expression/structure expansion limit exceeded");
    ++nodes;
    return success();
  }
  LogicalResult put(StringRef piece) {
    if (piece.size() > maxText - text.size())
      return error(module, "generated text exceeds 8 MiB");
    text.append(piece.data(), piece.size());
    return success();
  }
  LogicalResult number(uint64_t value) { return put(std::to_string(value)); }
  LogicalResult quoted(StringRef value) {
    if (failed(put("\"")))
      return failure();
    for (unsigned char byte : value.bytes()) {
      StringRef escape;
      switch (byte) {
      case '"':
        escape = "\\\"";
        break;
      case '\\':
        escape = "\\\\";
        break;
      case '\n':
        escape = "\\n";
        break;
      case '\r':
        escape = "\\r";
        break;
      case '\t':
        escape = "\\t";
        break;
      default:
        if (byte < 32 || byte == 127)
          return error(module, "unsupported control character in source name");
        break;
      }
      char character = static_cast<char>(byte);
      if (failed(put(escape.empty() ? StringRef(&character, 1) : escape)))
        return failure();
    }
    return put("\"");
  }

  FailureOr<uint64_t> width(Type type, Operation *site) {
    if (!isa<ac::BitsType>(type)) {
      (void)error(site, "only fixed Bits payloads are supported");
      return failure();
    }
    auto resolved = hardware.getPackedWidth(type, bindings, site);
    if (failed(resolved))
      return failure();
    if (!*resolved) {
      (void)error(site, "zero-width source payload is outside this profile");
      return failure();
    }
    return *resolved;
  }

  FailureOr<uint64_t> outputWidth(Type type, Operation *site) {
    if (!isa<ac::StructType>(type))
      return width(type, site);
    auto resolved = hardware.getPackedWidth(type, bindings, site);
    if (failed(resolved) || !*resolved) {
      (void)error(site, "a nonempty finite packed output is required");
      return failure();
    }
    return *resolved;
  }

  FailureOr<StringRef> literal(ac::BitsConstantOp constant) {
    auto value =
        hardware.evaluateStatic(constant.getValue(), bindings, constant);
    if (failed(value))
      return failure();
    auto integer = dyn_cast<ac::MathIntAttr>(*value);
    if (!integer || integer.getCanonicalValue().starts_with("-")) {
      (void)error(constant, "a known unsigned integer literal is required");
      return failure();
    }
    if (integer.getCanonicalValue().size() > maxText) {
      (void)error(constant, "literal exceeds generated-text limit");
      return failure();
    }
    return integer.getCanonicalValue();
  }

  FailureOr<Value> identity(Value value, unsigned depth = 0) {
    Operation *site = value.getDefiningOp();
    if (!site)
      site = module;
    if (failed(pay(site, depth)))
      return failure();
    Value source;
    if (auto extract = value.getDefiningOp<ac::BitsExtractOp>()) {
      auto low = hardware.evaluateStatic(extract.getLow(), bindings, extract);
      if (failed(low))
        return failure();
      auto integer = dyn_cast<ac::MathIntAttr>(*low);
      if (!integer || integer.getCanonicalValue() != "0") {
        (void)error(extract, "only identity extraction is supported");
        return failure();
      }
      source = extract.getInput();
    } else if (auto resize = value.getDefiningOp<ac::BitsResizeOp>()) {
      source = resize.getInput();
    } else {
      return value;
    }
    auto before = width(source.getType(), site),
         after = width(value.getType(), site);
    if (failed(before) || failed(after))
      return failure();
    if (*before != *after) {
      (void)error(site, "nonidentity extraction/resize is unsupported");
      return failure();
    }
    return identity(source, depth + 1);
  }

  LogicalResult checkPure(Operation *op) {
    if (failed(pay(op)))
      return failure();
    if (auto constant = dyn_cast<ac::BitsConstantOp>(op)) {
      if (failed(literal(constant)))
        return failure();
    } else if (auto binary = dyn_cast<ac::BitsBinaryOp>(op)) {
      if (binary.getOpcode() != "add" && binary.getOpcode() != "sub" &&
          binary.getOpcode() != "and" && binary.getOpcode() != "or")
        return error(op, "unsupported binary operation");
      auto lhs = width(binary.getLhs().getType(), op);
      auto rhs = width(binary.getRhs().getType(), op);
      auto result = width(binary.getResult().getType(), op);
      if (failed(lhs) || failed(rhs) || failed(result))
        return failure();
      if (*lhs != *rhs || *lhs != *result ||
          ((binary.getOpcode() == "and" || binary.getOpcode() == "or") &&
           *result != 1))
        return error(op, "unsupported binary operand widths");
    } else if (auto compare = dyn_cast<ac::BitsCompareOp>(op)) {
      if (compare.getPredicate() != "eq" && compare.getPredicate() != "ult" &&
          compare.getPredicate() != "ugt")
        return error(op, "unsupported comparison");
    } else if (auto unary = dyn_cast<ac::BitsUnaryOp>(op)) {
      auto result = width(unary.getResult().getType(), op);
      if (failed(result))
        return failure();
      if (unary.getOpcode() != "not" || *result != 1)
        return error(op, "only one-bit predicate negation is supported");
    } else if (isa<ac::BitsExtractOp, ac::BitsResizeOp>(op)) {
      if (failed(identity(op->getResult(0))))
        return failure();
    } else if (isa<ac::BitsSelectOp>(op)) {
      for (Type type : op->getOperandTypes())
        if (failed(width(type, op)))
          return failure();
    } else if (isa<ac::StructCreateOp>(op)) {
      if (!op->getNumOperands())
        return error(op, "empty output records are unsupported");
      for (Type type : op->getOperandTypes())
        if (failed(outputWidth(type, op)))
          return failure();
    } else {
      return error(op, "unsupported operation in selected executable closure");
    }
    for (Type type : op->getResultTypes())
      if (failed(outputWidth(type, op)))
        return failure();
    return success();
  }

  LogicalResult inventory() {
    auto parameters = module->getAttrOfType<ArrayAttr>("parameters");
    auto typeParameters = module->getAttrOfType<ArrayAttr>("type_parameters");
    if (!parameters || !parameters.empty() || !typeParameters ||
        !typeParameters.empty())
      return error(module, "a concrete nonparameterized module is required");
    auto domain = module->getAttrOfType<DictionaryAttr>("ac.domain_inputs");
    auto clockAttr =
        domain ? domain.getAs<IntegerAttr>("clock") : IntegerAttr();
    auto resetAttr =
        domain ? domain.getAs<IntegerAttr>("reset") : IntegerAttr();
    auto &body = module.getBody().front();
    if (!clockAttr || !resetAttr || clockAttr.getInt() < 0 ||
        resetAttr.getInt() < 0 ||
        static_cast<uint64_t>(clockAttr.getInt()) >= body.getNumArguments() ||
        static_cast<uint64_t>(resetAttr.getInt()) >= body.getNumArguments() ||
        clockAttr == resetAttr)
      return error(module, "verified clock/reset input ordinals are required");
    clock = body.getArgument(clockAttr.getInt());
    reset = body.getArgument(resetAttr.getInt());
    for (auto [ordinal, argument] : llvm::enumerate(body.getArguments())) {
      if (failed(pay(module)))
        return failure();
      auto bits = width(argument.getType(), module);
      if (failed(bits))
        return failure();
      if (argument == clock || argument == reset) {
        if (*bits != 1)
          return error(module, "domain inputs must be one bit");
        continue;
      }
      inputIndices[argument] = inputWidths.size();
      inputWidths.push_back(*bits);
      inputNames.push_back(
          cast<StringAttr>(module.getInputNames()[ordinal]).getValue());
    }
    for (Operation &op : body) {
      if (auto declaration = dyn_cast<ac::SourceStateOp>(op)) {
        if (failed(pay(&op)))
          return failure();
        if (declaration.isDWire() || declaration.getClk() != clock ||
            declaration.getRst() != reset)
          return error(&op,
                       "only registers in the selected domain are supported");
        auto bits = width(declaration.getQ().getType(), &op);
        auto original = identity(declaration.getInitial());
        if (failed(bits) || failed(original))
          return failure();
        auto constant = original->getDefiningOp<ac::BitsConstantOp>();
        if (!constant)
          return error(&op, "register initialization must be a known constant");
        auto value = literal(constant);
        if (failed(value))
          return failure();
        registerIndices[declaration] = registerWidths.size();
        registerWidths.push_back(*bits);
        registerNames.push_back(declaration.getInstanceName());
        initialValues.push_back(*value);
        std::string key;
        llvm::raw_string_ostream keyStream(key);
        declaration.getOccurrence().print(keyStream);
        registerKeys.push_back(std::move(key));
      } else if (isa<ac::SourceTransactionOp, ac::SourceMethodOp, ac::YieldOp>(
                     op)) {
        continue;
      } else if (failed(checkPure(&op))) {
        return failure();
      }
    }
    auto yield = dyn_cast<ac::YieldOp>(body.back());
    if (!yield || yield.getValues().size() != module.getOutputNames().size())
      return error(module, "public output observations are required");
    for (Value result : yield.getValues()) {
      auto bits = outputWidth(result.getType(), module);
      if (failed(bits))
        return failure();
      outputValues.push_back(result);
      outputWidths.push_back(*bits);
    }
    return success();
  }

  LogicalResult checkPlan(const ac::TransactionStatePlan &plan) {
    if (plan.lexicalModule != module || plan.routingModule != module ||
        !plan.registrationPath.empty() || plan.instances.size() != 1 ||
        plan.frames.size() != 1 || plan.rootFrame != 0 ||
        plan.domain.clock.value != clock || plan.domain.reset.value != reset ||
        plan.domain.clock.anchor != 0 || plan.domain.reset.anchor != 0 ||
        plan.guards.size() != 1 || plan.guard != 0 || !plan.calls.empty() ||
        !plan.formalWrites.empty() || !plan.branches.empty() ||
        !plan.joins.empty() || !plan.branchResults.empty() ||
        !plan.queueOwners.empty() || !plan.memoryOwners.empty() ||
        !plan.bodyChecks.empty() || !plan.observations.empty() ||
        !plan.results.empty())
      return error(plan.transaction,
                   "unsupported transaction closure/domain/effects");
    auto registration = ac::getSourceRegistrationEntry(plan.transaction);
    if (failed(registration))
      return failure();
    Operation *entry = plan.transaction;
    if (*registration) {
      if (plan.frames[0].method != (**registration).method ||
          plan.frames[0].registrationEntry != (**registration).call)
        return error(plan.transaction,
                     "registration entry differs from checked plan");
      entry = (**registration).method;
      usedMethods.insert(entry);
    } else if (plan.frames[0].method || plan.frames[0].registrationEntry) {
      return error(plan.transaction, "unexpected registration frame");
    }
    // Captures are frozen module SSA, never dynamically rebound registers.
    // Check all of them, including unused formals, before exporting any Rule.
    auto checkCapture = [&](Value captured) -> LogicalResult {
      auto original = identity(captured);
      if (failed(original))
        return failure();
      if (*original == clock || *original == reset)
        return error(entry, "domain input captured as data");
      if (inputIndices.contains(*original))
        return success();
      if (auto constant = original->getDefiningOp<ac::BitsConstantOp>())
        return success(succeeded(literal(constant)));
      if (original->getDefiningOp<ac::SourceStateOp>())
        return error(entry,
                     "module-body state snapshot capture is unsupported");
      return error(entry, "captures require data inputs or known literals with "
                          "identity wiring");
    };
    auto transaction = plan.transaction;
    for (Value capture : transaction.getCaptures())
      if (failed(checkCapture(capture)))
        return failure();
    if (auto method = dyn_cast<ac::SourceMethodOp>(entry))
      for (Value capture : method.getCaptures())
        if (failed(checkCapture(capture)))
          return failure();
    for (Region &region : entry->getRegions()) {
      if (!region.hasOneBlock())
        return error(entry, "single-block callable regions are required");
      for (Operation &op : region.front()) {
        if (isa<ac::YieldOp, ac::SourceStateReadOp, ac::SourceStateWriteOp>(op))
          continue;
        if (failed(checkPure(&op)))
          return failure();
      }
    }
    for (const auto &owner : plan.owners)
      if (owner.anchor != 0 || !owner.instancePath.empty() ||
          !registerIndices.contains(owner.declaration) ||
          !(owner.domain == plan.domain))
        return error(plan.transaction,
                     "state owner is outside the selected register bank");
    if (plan.versions.size() != plan.owners.size() + plan.writes.size())
      return error(plan.transaction, "unsupported state-version graph");
    if (plan.writes.size() > maxDepth)
      return error(plan.transaction, "command nesting exceeds depth 256");
    return success();
  }

  LogicalResult order() {
    for (const auto &plan : analysis.getPlans()) {
      if (plan.lexicalModule != module)
        continue;
      if (failed(pay(plan.transaction)) || failed(checkPlan(plan)))
        return failure();
      plans.push_back(&plan);
    }
    if (plans.empty())
      return error(module, "at least one autonomous Rule is required");
    unsigned roots = 0;
    for (auto transaction :
         module.getBody().front().getOps<ac::SourceTransactionOp>()) {
      if (failed(pay(transaction)))
        return failure();
      ++roots;
    }
    if (roots != plans.size())
      return error(module, "incomplete transaction occurrence inventory");
    llvm::sort(plans, [](const auto *left, const auto *right) {
      return left->predecessorIndices.size() < right->predecessorIndices.size();
    });
    for (auto [index, plan] : llvm::enumerate(plans)) {
      if (plan->predecessorIndices.size() != index)
        return error(plan->transaction,
                     "all roots must have an explicit total after order");
      for (unsigned earlier = 0; earlier < index; ++earlier)
        if (!llvm::is_contained(plan->predecessorIndices,
                                plans[earlier]->ordinal))
          return error(plan->transaction,
                       "after order is not a complete local chain");
    }
    for (auto method : module.getBody().front().getOps<ac::SourceMethodOp>())
      if (!usedMethods.contains(method))
        return error(method,
                     "unregistered/general Methods are outside this profile");
    return success();
  }

  FailureOr<Value> normalize(Value value, unsigned depth) {
    if (failed(pay(module, depth)))
      return failure();
    auto argument = dyn_cast<BlockArgument>(value);
    if (!argument || argument.getOwner() == &module.getBody().front())
      return value;
    const auto &frame = active->frames[0];
    for (const auto *bindings : {&frame.guardArguments, &frame.bodyArguments})
      for (const auto &binding : *bindings)
        if (binding.formal == argument) {
          if (binding.actual >= active->values.size())
            return failure();
          const auto &actual = active->values[binding.actual];
          if (actual.anchor != 0 || actual.frame != 0)
            return failure();
          return normalize(actual.value, depth + 1);
        }
    (void)error(module, "unresolved callable SSA argument");
    return failure();
  }

  LogicalResult emitValue(Value original, bool predicate, unsigned depth = 0) {
    auto normalized = normalize(original, depth);
    if (failed(normalized))
      return failure();
    Value value = *normalized;
    Operation *site = value.getDefiningOp();
    if (!site)
      site = module;
    auto bits = width(value.getType(), site);
    if (failed(bits))
      return failure();
    if (predicate && *bits != 1)
      return error(site, "predicates must have width one");
    if (auto extract = dyn_cast<ac::BitsExtractOp>(site))
      return emitValue(extract.getInput(), predicate, depth + 1);
    if (auto resize = dyn_cast<ac::BitsResizeOp>(site))
      return emitValue(resize.getInput(), predicate, depth + 1);
    if (predicate) {
      if (auto compare = dyn_cast<ac::BitsCompareOp>(site)) {
        if (failed(put(compare.getPredicate() == "eq" ? "(.eq " : "(.ult ")))
          return failure();
        Value left = compare.getLhs(), right = compare.getRhs();
        if (compare.getPredicate() == "ugt")
          std::swap(left, right);
        if (failed(emitValue(left, false, depth + 1)) || failed(put(" ")) ||
            failed(emitValue(right, false, depth + 1)))
          return failure();
        return put(")");
      }
      if (auto binary = dyn_cast<ac::BitsBinaryOp>(site);
          binary &&
          (binary.getOpcode() == "and" || binary.getOpcode() == "or")) {
        bool disjunction = binary.getOpcode() == "or";
        if (failed(put(disjunction ? "(.not (.and (.not " : "(.and ")) ||
            failed(emitValue(binary.getLhs(), true, depth + 1)) ||
            failed(put(disjunction ? ") (.not " : " ")) ||
            failed(emitValue(binary.getRhs(), true, depth + 1)))
          return failure();
        return put(disjunction ? ")))" : ")");
      }
      if (auto unary = dyn_cast<ac::BitsUnaryOp>(site);
          unary && unary.getOpcode() == "not") {
        if (failed(put("(.not ")) ||
            failed(emitValue(unary.getInput(), true, depth + 1)))
          return failure();
        return put(")");
      }
      if (failed(put("(.eq ")) || failed(emitValue(value, false, depth + 1)))
        return failure();
      return put(" (.bitsLit (BitVec.ofNat 1 1)))");
    }
    auto input = inputIndices.find(value);
    if (input != inputIndices.end()) {
      if (failed(put("(.input ")) || failed(number(input->second)))
        return failure();
      return put(")");
    }
    if (value == clock || value == reset)
      return error(site, "domain input used as data");
    if (isa<ac::SourceStateOp>(site)) {
      if (!outputContext || !registerIndices.contains(site))
        return error(
            site, "module-body state snapshots cannot become candidate reads");
      if (failed(put("(.reg ")) || failed(number(registerIndices.lookup(site))))
        return failure();
      return put(")");
    }
    if (auto read = dyn_cast<ac::SourceStateReadOp>(site)) {
      if (outputContext || !active)
        return error(site, "output cannot observe a Rule-local candidate");
      for (const auto &binding : active->reads) {
        if (binding.operation != read || binding.frame != 0)
          continue;
        if (binding.owner >= current.size() ||
            current[binding.owner] != binding.version)
          return error(site, "stale SSA state snapshot is not representable");
        if (!binding.selectors.empty() || !binding.indices.empty())
          return error(site, "selected reads are unsupported");
        if (failed(put("(.reg ")) ||
            failed(number(registerIndices.lookup(
                active->owners[binding.owner].declaration))))
          return failure();
        return put(")");
      }
      return error(site,
                   "candidate read is absent from the current invocation plan");
    }
    if (auto constant = dyn_cast<ac::BitsConstantOp>(site)) {
      auto integer = literal(constant);
      if (failed(integer) || failed(put("(.bitsLit (BitVec.ofNat ")) ||
          failed(number(*bits)) || failed(put(" ")) || failed(put(*integer)))
        return failure();
      return put("))");
    }
    if (auto select = dyn_cast<ac::BitsSelectOp>(site)) {
      if (failed(put("(.ite ")) ||
          failed(emitValue(select.getCondition(), true, depth + 1)) ||
          failed(put(" ")) ||
          failed(emitValue(select.getTrueValue(), false, depth + 1)) ||
          failed(put(" ")) ||
          failed(emitValue(select.getFalseValue(), false, depth + 1)))
        return failure();
      return put(")");
    }
    auto binary = dyn_cast<ac::BitsBinaryOp>(site);
    if (isa<ac::BitsCompareOp, ac::BitsUnaryOp>(site) ||
        (binary &&
         (binary.getOpcode() == "and" || binary.getOpcode() == "or"))) {
      if (*bits != 1)
        return error(site, "Boolean payload conversion requires one bit");
      if (failed(put("(.bit ")) || failed(emitValue(value, true, depth + 1)))
        return failure();
      return put(")");
    }
    if (auto binary = dyn_cast<ac::BitsBinaryOp>(site)) {
      if (binary.getOpcode() != "add" && binary.getOpcode() != "sub")
        return error(site, "predicate result used as a Bits payload");
      if (failed(put(binary.getOpcode() == "add" ? "(.add " : "(.sub ")) ||
          failed(emitValue(binary.getLhs(), false, depth + 1)) ||
          failed(put(" ")) ||
          failed(emitValue(binary.getRhs(), false, depth + 1)))
        return failure();
      return put(")");
    }
    return error(site, "unsupported payload expression");
  }

  LogicalResult emitOutput(Value value, unsigned depth = 0) {
    if (failed(pay(module, depth)))
      return failure();
    if (auto record = value.getDefiningOp<ac::StructCreateOp>()) {
      // StructCreate operands are verified in declaration order; packed RTL
      // places the first declared field at the most significant end.
      unsigned count = record->getNumOperands();
      if (!count)
        return error(record, "empty output record is unsupported");
      for (unsigned index = 0; index < count; ++index) {
        if ((index + 1 < count && failed(put("(.concat "))) ||
            failed(emitOutput(record->getOperand(index), depth + index + 1)) ||
            (index + 1 < count && failed(put(" "))))
          return failure();
      }
      for (unsigned index = 1; index < count; ++index)
        if (failed(put(")")))
          return failure();
      return success();
    }
    return emitValue(value, false, depth + 1);
  }

  LogicalResult names(StringRef name, ArrayRef<StringRef> values) {
    if (failed(put("def ")) || failed(put(name)) ||
        failed(put(" : List String := [")))
      return failure();
    for (auto [index, value] : llvm::enumerate(values)) {
      if (failed(pay(module)) || (index && failed(put(", "))) ||
          failed(quoted(value)))
        return failure();
    }
    return put("]\n");
  }

  LogicalResult layout(StringRef label, ArrayRef<uint64_t> widths, bool types) {
    if (failed(put(label)))
      return failure();
    if (widths.empty())
      return put("fun index => Fin.elim0 index");
    if (failed(put("fun index => match index.val with ")))
      return failure();
    for (auto [index, bits] : llvm::enumerate(widths)) {
      if (failed(pay(module)) || failed(put("| ")) ||
          failed(index + 1 == widths.size() ? put("_") : number(index)) ||
          failed(put(types ? " => .bits " : " => ")) || failed(number(bits)) ||
          failed(put(" ")))
        return failure();
    }
    return success();
  }

  LogicalResult emitRule(const ac::TransactionStatePlan &plan,
                         uint64_t ordinal) {
    active = &plan;
    current.assign(plan.owners.size(), uint64_t(-1));
    for (auto [index, version] : llvm::enumerate(plan.versions)) {
      if (failed(pay(plan.transaction)))
        return failure();
      if (version.owner >= current.size())
        return error(plan.transaction, "invalid version owner");
      if (version.kind == ac::StateVersionKind::OldQ) {
        if (current[version.owner] != uint64_t(-1) || version.ordinal != 0 ||
            version.predecessor || version.write || version.join ||
            version.value != plan.owners[version.owner].oldQ)
          return error(plan.transaction, "invalid entry state version");
        current[version.owner] = index;
      }
    }
    if (llvm::is_contained(current, uint64_t(-1)))
      return error(plan.transaction, "missing entry version");
    if (failed(put("def rule")) || failed(number(ordinal)) ||
        failed(put(" : RuleDef signature :=\n  { guard := ")))
      return failure();
    const auto &guard = plan.guards[0];
    if (guard.frame != 0 || guard.predicate >= plan.values.size())
      return failure();
    if (failed(emitValue(plan.values[guard.predicate].value, true)) ||
        failed(put("\n    body := ")))
      return failure();
    unsigned emitted = 0;
    for (const auto &event : plan.events) {
      if (failed(pay(plan.transaction)))
        return failure();
      using Kind = ac::TransactionStateEventKind;
      if (event.kind == Kind::Write) {
        if (!event.write || *event.write >= plan.writes.size())
          return failure();
        const auto &write = plan.writes[*event.write];
        if (write.frame != 0 || write.owner >= current.size() ||
            current[write.owner] != write.predecessor || !write.pathFact ||
            !write.pathFact.getValue() || !write.selectors.empty() ||
            !write.indices.empty() || write.forwardedProposal ||
            write.version >= plan.versions.size() ||
            write.value >= plan.values.size())
          return error(plan.transaction,
                       "unsupported write or predecessor state version");
        const auto &version = plan.versions[write.version];
        if (version.kind != ac::StateVersionKind::Write ||
            version.owner != write.owner ||
            version.predecessor != write.predecessor ||
            version.write != *event.write || version.value != write.value ||
            version.join)
          return error(plan.transaction, "write/version graph differs");
        if (failed(put("(.seq (.assign ")) ||
            failed(number(registerIndices.lookup(
                plan.owners[write.owner].declaration))) ||
            failed(put(" ")) ||
            failed(emitValue(plan.values[write.value].value, false)) ||
            failed(put(") ")))
          return failure();
        current[write.owner] = write.version;
        ++emitted;
      } else if (event.kind == Kind::Read) {
        if (!event.read || *event.read >= plan.reads.size())
          return failure();
        const auto &read = plan.reads[*event.read];
        if (read.frame != 0 || read.owner >= current.size() ||
            read.version != current[read.owner] || !read.selectors.empty() ||
            !read.indices.empty())
          return error(plan.transaction,
                       "read/version graph differs at statement point");
      } else if (event.kind != Kind::TransactionEnter &&
                 event.kind != Kind::TransactionExit &&
                 event.kind != Kind::GuardEnter &&
                 event.kind != Kind::GuardExit && event.kind != Kind::Read) {
        return error(plan.transaction, "unsupported transaction event");
      }
    }
    if (emitted != plan.writes.size())
      return error(plan.transaction, "incomplete write event inventory");
    for (auto final : plan.finalVersions)
      if (final.owner >= current.size() ||
          current[final.owner] != final.version)
        return error(plan.transaction, "final state version differs");
    if (failed(put(".skip")))
      return failure();
    for (unsigned index = 0; index < emitted; ++index)
      if (failed(put(")")))
        return failure();
    return put(" }\n\n");
  }

  LogicalResult emitModel() {
    if (failed(put("import RuleSemantics.Syntax\n\nnamespace "
                   "PycircuitExport\nopen RuleSemantics.Syntax\n\n")) ||
        failed(put("abbrev signature : Signature :=\n  { nr := ")) ||
        failed(number(registerWidths.size())) || failed(put(", ni := ")) ||
        failed(number(inputWidths.size())) ||
        failed(layout(", regWidth := ", registerWidths, false)) ||
        failed(layout(", inputType := ", inputWidths, true)) ||
        failed(put(" }\n\n")))
      return failure();
    if (failed(put("def initialState : State signature :=\n  fun register => "
                   "BitVec.ofNat (signature.regWidth register) ")))
      return failure();
    if (initialValues.empty()) {
      if (failed(put("(Fin.elim0 register)\n\n")))
        return failure();
    } else {
      if (failed(put("(match register.val with ")))
        return failure();
      for (auto [index, value] : llvm::enumerate(initialValues))
        if (failed(put("| ")) ||
            failed(index + 1 == initialValues.size() ? put("_")
                                                     : number(index)) ||
            failed(put(" => ")) || failed(put(value)) || failed(put(" ")))
          return failure();
      if (failed(put(")\n\n")))
        return failure();
    }
    SmallVector<StringRef> outputNames;
    for (Attribute name : module.getOutputNames())
      outputNames.push_back(cast<StringAttr>(name).getValue());
    SmallVector<StringRef> keys;
    for (const auto &key : registerKeys)
      keys.push_back(key);
    if (failed(put("def definitionName : String := ")) ||
        failed(quoted(module.getSymName())) || failed(put("\n")) ||
        failed(names("inputNames", inputNames)) ||
        failed(names("registerNames", registerNames)) ||
        failed(names("registerKeys", keys)) ||
        failed(names("outputNames", outputNames)) ||
        failed(put("def outputExpressions : List (Output signature) := [")))
      return failure();
    outputContext = true;
    for (auto [index, value] : llvm::enumerate(outputValues)) {
      if ((index && failed(put(", "))) || failed(put("{ width := ")) ||
          failed(number(outputWidths[index])) ||
          failed(put(", expression := ")) || failed(emitOutput(value)) ||
          failed(put(" }")))
        return failure();
    }
    outputContext = false;
    if (failed(put("]\n\n")))
      return failure();
    for (auto [index, plan] : llvm::enumerate(plans))
      if (failed(emitRule(*plan, index)))
        return failure();
    if (failed(put("def rules : List (RuleDef signature) := [")))
      return failure();
    for (uint64_t index = 0; index < plans.size(); ++index)
      if ((index && failed(put(", "))) || failed(put("rule")) ||
          failed(number(index)))
        return failure();
    return put("]\n\nend PycircuitExport\n");
  }

  ac::ModuleOp module;
  ac::HardwareAnalysis &hardware;
  const ac::SourceTransactionStateAnalysis &analysis;
  ac::HardwareBindings bindings;
  uint64_t nodes = 0;
  std::string text;
  Value clock, reset;
  llvm::DenseMap<Value, unsigned> inputIndices;
  llvm::DenseMap<Operation *, unsigned> registerIndices;
  llvm::DenseSet<Operation *> usedMethods;
  SmallVector<uint64_t> inputWidths, registerWidths, outputWidths;
  SmallVector<Value> outputValues;
  SmallVector<std::string> registerKeys;
  SmallVector<StringRef> inputNames, registerNames, initialValues;
  SmallVector<const ac::TransactionStatePlan *> plans;
  const ac::TransactionStatePlan *active = nullptr;
  SmallVector<ac::StateVersionId> current;
  bool outputContext = false;
};

class ExportRuleLeanPass
    : public PassWrapper<ExportRuleLeanPass, OperationPass<mlir::ModuleOp>> {
public:
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(ExportRuleLeanPass)
  ExportRuleLeanPass() = default;
  ExportRuleLeanPass(const ExportRuleLeanPass &other) : PassWrapper(other) {}
  StringRef getArgument() const final { return "ac-export-rule-lean"; }
  StringRef getDescription() const final {
    return "Export a bounded closed Rule model from verified typed source IR";
  }

  void runOnOperation() final {
    markAllAnalysesPreserved();
    auto package = getOperation();
    if (top.empty() || output.empty()) {
      package.emitError("Rule Lean export requires top and output options");
      signalPassFailure();
      return;
    }
    auto source = ac::verifySourceBodyStructure(
        package, [&] { return package.emitError(); });
    if (failed(source)) {
      signalPassFailure();
      return;
    }
    auto &hardware = getAnalysis<ac::HardwareAnalysis>();
    auto selected =
        dyn_cast_or_null<ac::ModuleOp>(hardware.lookupDefinition(top));
    if (!selected) {
      package.emitError(
          "Rule Lean export top must select an exact module definition");
      signalPassFailure();
      return;
    }
    auto &analysis = getAnalysis<ac::SourceTransactionStateAnalysis>();
    if (!analysis.isValid()) {
      signalPassFailure();
      return;
    }
    RuleLeanExporter exporter(selected, hardware, analysis);
    auto model = exporter.run();
    if (failed(model)) {
      signalPassFailure();
      return;
    }

    // A same-directory temporary preserves the destination on every rejection
    // and makes the only publication step an atomic rename.
    SmallString<256> temporary;
    int descriptor;
    std::error_code status = llvm::sys::fs::createUniqueFile(
        output.getValue() + ".tmp-%%%%%%", descriptor, temporary);
    if (status) {
      package.emitError() << "Rule Lean export cannot create temporary output: "
                          << status.message();
      signalPassFailure();
      return;
    }
    auto cleanup =
        llvm::scope_exit([&] { (void)llvm::sys::fs::remove(temporary); });
    llvm::raw_fd_ostream stream(descriptor, true);
    stream << *model;
    stream.close();
    if (stream.has_error()) {
      package.emitError() << "Rule Lean export cannot write output: "
                          << stream.error().message();
      stream.clear_error();
      signalPassFailure();
      return;
    }
    status = llvm::sys::fs::rename(temporary, output);
    if (status) {
      package.emitError() << "Rule Lean export cannot publish output: "
                          << status.message();
      signalPassFailure();
    }
  }

private:
  Option<std::string> top{*this, "top",
                          llvm::cl::desc("Exact source module symbol"),
                          llvm::cl::init("")};
  Option<std::string> output{*this, "output",
                             llvm::cl::desc("Destination Lean file"),
                             llvm::cl::init("")};
};

} // namespace

std::unique_ptr<mlir::Pass> createExportRuleLeanPass() {
  return std::make_unique<ExportRuleLeanPass>();
}

} // namespace acir
