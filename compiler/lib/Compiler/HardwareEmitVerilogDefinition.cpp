#include "FinalCppNames.h"
#include "HardwareEmitCommon.h"
#include "pycircuit/Dialect/ACIR/SourceValueNames.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include <array>
#include <limits>
#include <memory>
using namespace mlir;
namespace acir::compiler {
namespace {
#include "HardwareEmitVerilogSections.inc"
class NetEmitter {
public:
  NetEmitter(HardwareEmitContext &context, ac::ModuleOp definition,
             raw_ostream &out, const RtlOwnershipPartition *partition = nullptr)
      : context(context), definition(definition), readableSections(out, context.isSynthesis()),
        out(context.isSynthesis() ? static_cast<raw_ostream &>(readableSections) : out), ownership(partition) {
    unsigned direction = 0;
    for (auto ports : {definition.getInputNames(), definition.getOutputNames()}) {
      for (auto [index, raw] : llvm::enumerate(ports)) {
        if ((!direction && context.rtlOmittedInput(definition, index)) ||
            (direction && (context.rtlForwardedInput(definition, index) || context.rtlOmittedOutput(definition, index)))) continue;
        auto id = context.rtlPortName(definition, cast<StringAttr>(raw).getValue());
        if (succeeded(id))
          readableNames.insert(rtlIdentifierStem(*id));
      }
      ++direction;
    }
    for (auto raw : definition.getParameters()) {
      auto name = cast<DictionaryAttr>(raw).getAs<StringAttr>("name");
      auto id = context.rtlFormalName(name.getValue(), definition);
      if (succeeded(id))
        readableNames.insert(rtlIdentifierStem(*id));
    }
    for (auto raw : definition.getTypeParameters()) {
      auto id = context.rtlFormalName(cast<StringAttr>(raw).getValue(), definition);
      if (succeeded(id))
        readableNames.insert(rtlIdentifierStem(*id));
    }
  }
  LogicalResult initializeOwnership() {
    if (ownership) {
      for (const auto &[value, source] : ownership->aliases) ownershipAliases[value] = source;
      for (const auto &port : ownership->exports) readableNames.insert(rtlIdentifierStem(port.name));
      for (const auto &[index, value] : ownership->replacedInputs)
        ownershipAliases[definition.getBody().front().getArgument(index)] = value;
      for (const auto &port : ownership->captures) {
        if (port.local && port.local != port.value) ownershipAliases[port.value] = port.local;
        else if (port.local) continue;
        else {
          names[port.value] = port.name;
          ownershipOpaque.insert(port.value);
          readableNames.insert(rtlIdentifierStem(port.name));
        }
      }
    }
    for (const auto &partition : context.rtlPartitions) {
      if (!partition->active || !context.rtlChildPartition(partition.get(), definition, ownership)) continue;
      auto instance = readableInstanceName(partition->allocation);
      if (failed(instance)) return failure();
      for (const auto &port : partition->exports) {
        auto type = context.rtlType(port.value.getType(), definition);
        if (failed(type)) return failure();
        auto name = readableName(rtlIdentifierStem(*instance) + "_" + rtlIdentifierStem(port.name));
        readableDeclaration("wire", *type, name);
        names[port.value] = name;
        ownershipOpaque.insert(port.value);
      }
    }
    initializeReadableRoles();
    return initializeReadableInstanceArrays();
  }
  FailureOr<std::string> physicalInitializer(Value value, unsigned depth = 0) {
    if (context.isPhysical() && depth <= 256) {
      if (auto literal = readableLiteral(value))
        return *literal;
      auto source = readableFullExtract(value);
      if (source != value)
        return physicalInitializer(source, depth + 1);
    }
    auto known = initializers.find(value);
    if (known != initializers.end())
      return known->second;
    auto *op = value.getDefiningOp();
    if (!op || depth > 256)
      return definition.emitOpError()
             << "physical initializer has no bounded constant DAG";
    SmallVector<std::string> operands;
    for (Value operand : op->getOperands()) {
      auto rendered = physicalInitializer(operand, depth + 1);
      if (failed(rendered))
        return failure();
      operands.push_back(*rendered);
    }
    auto type = context.rtlType(value.getType(), op);
    if (failed(type))
      return failure();
    std::string expression;
    if (auto pattern = dyn_cast<ac::BitsConstant4Op>(op)) {
      expression = std::to_string(pattern.getPattern().size()) + "'b" +
                   pattern.getPattern().str();
    } else if (auto constant = dyn_cast<ac::BitsConstantOp>(op)) {
      auto literal = context.staticRtlValue(constant.getValue(), op);
      auto width = context.payloadWidth(value.getType(), op, true);
      if (failed(literal) || failed(width))
        return failure();
      if (context.isClosedStatic(constant.getValue())) {
        llvm::APSInt value(*literal);
        *literal = std::to_string(std::max(1u, value.getActiveBits())) + "'d" +
                   *literal;
      }
      expression = "(" + *width + ")'(" + *literal + ")";
    } else if (auto create = dyn_cast<ac::EnumCreateOp>(op)) {
      auto member = context.rtlEnumMember(create.getResult().getType(),
                                           create.getMemberAttr(), op);
      if (failed(member))
        return failure();
      expression = *member;
    } else if (isa<ac::StructCreateOp, ac::TableCreateOp>(op)) {
      expression = "{" + join(operands, ", ") + "}";
    } else if (auto splat = dyn_cast<ac::TableSplatOp>(op)) {
      auto count = context.shapeSize(splat.getShape(), op, true);
      if (failed(count))
        return failure();
      expression = "{(" + *count + "){" + operands[0] + "}}";
    } else if (auto get = dyn_cast<ac::StructGetOp>(op)) {
      auto field =
          rtlIdentifier(get.getField(), [&] { return op->emitOpError(); });
      if (failed(field))
        return failure();
      expression = operands[0] + "." + *field;
    } else if (isa<ac::EnumToBitsOp>(op)) {
      expression = operands[0];
    } else if (auto extract = dyn_cast<ac::BitsExtractOp>(op)) {
      auto low = context.staticRtlValue(extract.getLow(), op);
      auto width = context.payloadWidth(value.getType(), op, true);
      if (failed(low) || failed(width))
        return failure();
      expression = operands[0] + "[(" + *low + ") +: (" + *width + ")]";
    } else if (auto resize = dyn_cast<ac::BitsResizeOp>(op)) {
      auto width = context.payloadWidth(value.getType(), op, true);
      if (failed(width))
        return failure();
      expression = "(" + *width + ")'(" +
                   (resize.getMode() == "sext" ? "$signed(" : "$unsigned(") +
                   operands[0] + "))";
    }
    if (expression.empty())
      return op->emitOpError()
             << "physical initializer lacks constant RTL rendering";
    // Typed elaboration constants keep constructor layout and widths. No live
    // initializer wire participates in the primitive startup operation.
    auto name = readableName((context.isSynthesis() ? "reset_value_" : "initial_value_") +
                            std::to_string(initializers.size()));
    readableDeclaration("localparam", *type, name, expression);
    initializers.try_emplace(value, name);
    return name;
  }
  LogicalResult emitSourceChecks() {
    if (context.isSynthesis() || (context.isPhysical() && !context.hasPhysicalChecks())) return success();
    if (context.isPhysical()) {
      for (const auto &binding : context.sourceChecks().bindings) {
        if (binding.definition != definition)
          continue;
        if (readableKnownBit(binding.condition) && readableKnownBit(binding.path))
          continue;
        auto condition = net(binding.condition), path = net(binding.path);
        if (failed(condition) || failed(path))
          return failure();
        auto name = "guard_error_" + std::to_string(readableErrors.size());
        SmallVector<std::string> terms;
        if (!readableKnownBit(binding.path)) terms.push_back("$isunknown(" + *path + ")");
        if (!readableKnownBit(binding.condition)) {
          std::string term = "(" + context.rtlProtocolName("pyc_reset_active") + " === 1'b0)";
          if (readableBit(binding.path) != true) term += " && (" + *path + " === 1'b1)";
          terms.push_back("(" + term + " && $isunknown(" + *condition + "))");
        }
        readableErrors.emplace_back(name, join(terms, " || "));
        localErrors.push_back("__checks." + name);
      }
      for (const auto &control : context.physicalProjection().controls) {
        if (control.definition != definition || readableKnownBit(control.raw) ||
            readableBit(control.reached) == false) continue;
        auto raw = net(control.raw), reached = net(control.reached);
        if (failed(raw) || failed(reached)) return failure();
        auto name = "admission_error_" + std::to_string(readableErrors.size());
        std::string term = "(" + context.rtlProtocolName("pyc_reset_active") + " === 1'b0)";
        if (readableBit(control.reached) != true)
          term += " && (" + *reached + " === 1'b1)";
        term += " && $isunknown(" + *raw + ")";
        readableErrors.emplace_back(name, term);
        localErrors.push_back("__checks." + name);
      }
      return success();
    }
    if (!context.managesChecks())
      return success();
    for (auto [index, binding] :
         llvm::enumerate(context.sourceChecks().samplingBindings)) {
      if (binding.definition != definition)
        continue;
      auto clock = net(binding.clock);
      auto reset = net(binding.reset);
      if (failed(clock) || failed(reset))
        return failure();
      auto name = "pyc_sampling_" + std::to_string(binding.localOrdinal);
      samplingNames.try_emplace(index, name);
      localCompletions.push_back(name + "_complete");
      localSamplingErrors.push_back("(" + name + "_fault != 2'd0)");
      // These records observe the existing managed storage transaction; they
      // are verification instrumentation, not additional hardware state.
      out << "`ifndef SYNTHESIS\n"
          << "  logic " << name << "_clock = 1'b0;\n"
          << "  logic " << name << "_pending_clock = 1'b0;\n"
          << "  logic " << name << "_pending_valid = 1'b0;\n"
          << "  logic " << name << "_complete = 1'b0;\n"
          << "  logic " << name << "_sampled_clock = 1'b0;\n"
          << "  logic " << name << "_sampled_reset = 1'b0;\n"
          << "  logic " << name << "_rising = 1'b0;\n"
          << "  logic " << name << "_reset_active = 1'b0;\n"
          << "  logic [1:0] " << name << "_fault = 2'd0;\n"
          << "  always @(pyc_phase) begin\n"
          << "    case (pyc_phase)\n"
          << "      3'd1: begin\n"
          << "        " << name << "_complete = 1'b0;\n"
          << "        " << name << "_pending_valid = 1'b0;\n"
          << "        " << name << "_fault = 2'd0;\n"
          << "        " << name << "_rising = 1'b0;\n"
          << "        " << name << "_reset_active = 1'b0;\n"
          << "        " << name << "_sampled_clock = " << *clock << ";\n"
          << "        " << name
          << "_sampled_reset = " << context.rtlReset(*reset) << ";\n"
          << "        if ($isunknown(" << name << "_sampled_clock))\n"
          << "          " << name << "_fault = 2'd1;\n"
          << "        else begin\n"
          << "          " << name << "_rising = (" << name
          << "_clock === 1'b0) && (" << name << "_sampled_clock === 1'b1);\n"
          << "          if (" << name << "_rising && $isunknown(" << name
          << "_sampled_reset))\n"
          << "            " << name << "_fault = 2'd2;\n"
          << "          else begin\n"
          << "            " << name << "_reset_active = " << name
          << "_rising && (" << name << "_sampled_reset === 1'b1);\n"
          << "            " << name << "_pending_clock = " << name
          << "_sampled_clock;\n"
          << "            " << name << "_pending_valid = 1'b1;\n"
          << "          end\n"
          << "        end\n"
          << "        " << name << "_complete = 1'b1;\n"
          << "      end\n"
          << "      3'd2: begin\n"
          << "        if ((pyc_root_commit_ok === 1'b1) && (" << name
          << "_pending_valid === 1'b1)) begin\n"
          << "          " << name << "_clock = " << name << "_pending_clock;\n"
          << "          " << name << "_pending_valid = 1'b0;\n"
          << "        end\n"
          << "        if (pyc_root_commit_ok === 1'b1)\n"
          << "          " << name << "_complete = 1'b0;\n"
          << "      end\n"
          << "      3'd3, 3'd4: begin\n"
          << "        " << name << "_complete = 1'b0;\n"
          << "        " << name << "_sampled_clock = 1'b0;\n"
          << "        " << name << "_sampled_reset = 1'b0;\n"
          << "        " << name << "_rising = 1'b0;\n"
          << "        " << name << "_reset_active = 1'b0;\n"
          << "        " << name << "_fault = 2'd0;\n"
          << "        " << name << "_pending_clock = 1'b0;\n"
          << "        " << name << "_pending_valid = (pyc_phase == 3'd4);\n"
          << "      end\n"
          << "      default: begin end\n"
          << "    endcase\n"
          << "  end\n"
          << "`else\n"
          << "  wire " << name << "_complete = 1'b1;\n"
          << "  wire [1:0] " << name << "_fault = 2'd0;\n"
          << "`endif\n";
    }
    std::string reset = "pyc_reset_active";
    if (auto domain =
            definition->getAttrOfType<DictionaryAttr>("ac.domain_inputs")) {
      if (auto ordinal = domain.getAs<IntegerAttr>("reset")) {
        if (ordinal.getValue().getActiveBits() > 64 ||
            ordinal.getValue().getZExtValue() >=
                definition.getBody().front().getNumArguments())
          return definition.emitOpError()
                 << "RTL source-check reset input is outside the module";
        auto localReset = net(definition.getBody().front().getArgument(
            ordinal.getValue().getZExtValue()));
        if (failed(localReset))
          return failure();
        reset = std::move(*localReset);
      }
    }
    for (const auto &binding : context.sourceChecks().bindings) {
      if (binding.definition != definition)
        continue;
      auto condition = net(binding.condition);
      auto path = net(binding.path);
      if (failed(condition) || failed(path))
        return failure();
      auto name = "pyc_check_error_" + std::to_string(localErrors.size());
      if (binding.samplingBindingIndex) {
        auto found = samplingNames.find(*binding.samplingBindingIndex);
        if (found == samplingNames.end())
          return binding.expect->emitOpError()
                 << "RTL source check has no local sampling binding";
        const auto &sampling = found->second;
        localCompletions.push_back(name + "_complete");
        out << "`ifndef SYNTHESIS\n"
            << "  logic " << name << "_condition = 1'b0;\n"
            << "  logic " << name << "_path = 1'b0;\n"
            << "  logic " << name << "_complete = 1'b0;\n"
            << "  always @(pyc_phase) begin\n"
            << "    case (pyc_phase)\n"
            << "      3'd1: begin\n"
            << "        " << name << "_complete = 1'b0;\n"
            << "        " << name << "_condition = " << *condition << ";\n"
            << "        " << name << "_path = " << *path << ";\n"
            << "        " << name << "_complete = 1'b1;\n"
            << "      end\n"
            << "      3'd2: begin\n"
            << "        if (pyc_root_commit_ok === 1'b1)\n"
            << "          " << name << "_complete = 1'b0;\n"
            << "      end\n"
            << "      3'd3, 3'd4: begin\n"
            << "        " << name << "_complete = 1'b0;\n"
            << "        " << name << "_condition = 1'b0;\n"
            << "        " << name << "_path = 1'b0;\n"
            << "      end\n"
            << "      default: begin end\n"
            << "    endcase\n"
            << "  end\n"
            << "  wire " << name << " = $isunknown(" << name << "_path) || ("
            << sampling << "_rising && !" << sampling << "_reset_active && ("
            << name << "_path === 1'b1) && "
            << "$isunknown(" << name << "_condition));\n"
            << "`else\n"
            << "  wire " << name << "_complete = 1'b1;\n"
            << "  wire " << name << " = 1'b0;\n"
            << "`endif\n";
        localErrors.push_back(std::move(name));
        continue;
      }
      // Ordinary assertions retain their four-state truth table, evaluated
      // from the same prepared inputs that participate in the root barrier.
      localCompletions.push_back(name + "_complete");
      out << "`ifndef SYNTHESIS\n"
          << "  logic " << name << "_condition = 1'b0;\n"
          << "  logic " << name << "_path = 1'b0;\n"
          << "  logic " << name << "_reset = 1'b0;\n"
          << "  logic " << name << "_complete = 1'b0;\n"
          << "  always @(pyc_phase) begin\n"
          << "    case (pyc_phase)\n"
          << "      3'd1: begin\n"
          << "        " << name << "_complete = 1'b0;\n"
          << "        " << name << "_condition = " << *condition << ";\n"
          << "        " << name << "_path = " << *path << ";\n"
          << "        " << name << "_reset = " << context.rtlReset(reset)
          << ";\n"
          << "        " << name << "_complete = 1'b1;\n"
          << "      end\n"
          << "      3'd2: begin\n"
          << "        if (pyc_root_commit_ok === 1'b1)\n"
          << "          " << name << "_complete = 1'b0;\n"
          << "      end\n"
          << "      3'd3, 3'd4: begin\n"
          << "        " << name << "_complete = 1'b0;\n"
          << "        " << name << "_condition = 1'b0;\n"
          << "        " << name << "_path = 1'b0;\n"
          << "        " << name << "_reset = 1'b0;\n"
          << "      end\n"
          << "      default: begin end\n"
          << "    endcase\n"
          << "  end\n"
          << "  wire " << name << " = ((" << name << "_path & ~" << name
          << "_reset & ~" << name << "_condition) !== 1'b0);\n"
          << "`else\n"
          << "  wire " << name << "_complete = 1'b1;\n"
          << "  wire " << name << " = 1'b0;\n"
          << "`endif\n";
      localErrors.push_back(std::move(name));
    }
    return success();
  }
  LogicalResult emitObservations() {
    if (!context.isSystem())
      return success();
    auto plan = observationEmissionPlan(context);
    if (failed(plan))
      return failure();
    auto found = plan->definitions.find(definition);
    if (found == plan->definitions.end() || found->second.empty())
      return success();
    for (auto [index, site] : llvm::enumerate(found->second)) {
      auto observe = cast<ac::SourceObserveOp>(site.op);
      auto path = net(observe.getPath());
      Value observed = site.carriesValue ? observe.getValues()[site.valueIndex]
                                         : observe.getPath();
      auto value = net(observed);
      auto type = context.rtlType(observed.getType(), observe);
      if (failed(path) || failed(value) || failed(type))
        return failure();
      out << "  " << *type << " pyc_observation_value_" << index << " = '0;\n"
          << "  logic pyc_observation_pending_" << index << " = 1'b0;\n"
          << "  logic pyc_observation_valid_" << index << " = 1'b0;\n"
          << "  logic pyc_observation_path_" << index << " = 1'b0;\n"
          << "  always @(pyc_phase) begin\n"
          << "    case (pyc_phase)\n"
          << "      3'd1: begin\n"
          << "        pyc_observation_value_" << index << " = " << *value
          << ";\n"
          << "        pyc_observation_valid_" << index << " = !$isunknown("
          << *path << ");\n"
          << "        pyc_observation_path_" << index << " = (" << *path
          << " === 1'b1);\n"
          << "        pyc_observation_pending_" << index << " = 1'b1;\n"
          << "      end\n"
          << "      3'd0, 3'd3, 3'd4: begin\n"
          << "        pyc_observation_pending_" << index << " = 1'b0;\n"
          << "        pyc_observation_valid_" << index << " = 1'b0;\n"
          << "        pyc_observation_path_" << index << " = 1'b0;\n"
          << "        pyc_observation_value_" << index << " = '0;\n"
          << "      end\n"
          << "    endcase\n"
          << "  end\n";
    }
    return success();
  }
#include "HardwareEmitVerilogReadability.inc"
#include "HardwareEmitVerilogRoles.inc"
#include "HardwareEmitVerilogDerivedNames.inc"
#include "HardwareEmitVerilogSectionPlan.inc"
#include "HardwareEmitVerilogLayout.inc"
#include "HardwareEmitVerilogAggregates.inc"
#include "HardwareEmitVerilogSelectLayout.inc"
#include "HardwareEmitVerilogTableLanes.inc"
#include "HardwareEmitVerilogInstanceArrays.inc"
  FailureOr<std::string> net(Value value) {
    auto section = readableSection(value);
    if (auto alias = ownershipAliases.find(value); alias != ownershipAliases.end())
      return net(alias->second);
    if (auto found = names.find(value); found != names.end()) {
      if (readablePending.contains(value))
        readableRetained.insert(value);
      return found->second;
    }
    if (auto literal = context.rtlRootConstants.find(value); literal != context.rtlRootConstants.end()) {
      auto rendered = literal->second;
      if (!isa<ac::BitsType, ac::EnumType>(value.getType())) {
        auto type = context.rtlType(value.getType(), definition);
        if (failed(type)) return failure();
        auto local = readableName("argument_default_" + std::to_string(next++));
        readableDeclaration("localparam", *type, local, rendered);
        rendered = local;
      }
      names[value] = rendered;
      return rendered;
    }
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      auto *parent = argument.getOwner()->getParentOp();
      if (parent == definition) {
        auto port = cast<StringAttr>(
            definition.getInputNames()[argument.getArgNumber()]);
        auto id = context.rtlPortName(definition, port.getValue());
        if (failed(id))
          return failure();
        names.try_emplace(value, *id);
        return *id;
      }
      if (auto rule = dyn_cast<ac::RuleOp>(parent))
        return net(rule.getCaptures()[argument.getArgNumber()]);
      return definition.emitOpError() << "unexpected RTL block argument";
    }
    auto *op = value.getDefiningOp();
    if (!op)
      return definition.emitOpError() << "RTL wire has no producer";
    if (context.isPhysical()) {
      if (auto rendered = readableControlProjection(value); succeeded(rendered)) {
        if (readableEndpointValues.contains(readableSource(value))) {
          auto name = sourceNetName(readableSource(value));
          readableDeclaration("wire", "logic [0:0]", name, *rendered);
          names.try_emplace(value, name);
          return name;
        }
        names.try_emplace(value, *rendered);
        return *rendered;
      }
      if (isa<ac::TableType>(value.getType())) {
        bool accepted = false;
        auto rendered = readableTableLaneNet(value, accepted);
        if (succeeded(rendered)) return *rendered;
        if (accepted) return failure();
      }
      if (ac::sourceValueNames(value).empty()) {
        Value operand = readableEnumOperand(value);
        if (operand != value) {
          // net() memoizes the real producer: forwarding a representation does
          // not clone its arithmetic, selection, or membership computation.
          auto rendered = net(operand);
          if (succeeded(rendered)) names.try_emplace(value, *rendered);
          return rendered;
        }
      }
      if (auto choice = readableAggregateChoice(value))
        return emitReadableAggregateChoice(value, *choice);
      llvm::DenseSet<Value> visited;
      if (ac::sourceValueNames(value).empty() && readableInlineUses(value, visited)) {
        if (auto rendered = readableCanonicalBit(value); succeeded(rendered)) {
          names.try_emplace(value, *rendered);
          return *rendered;
        }
        if (auto literal = readableLiteral(value)) {
          names.try_emplace(value, *literal);
          return *literal;
        }
        auto source = readableFullExtract(value);
        if (source != value) {
          auto rendered = net(source);
          if (succeeded(rendered))
            names.try_emplace(value, *rendered);
          return rendered;
        }
      }
      if (auto rendered = readableStructuredMux(value); succeeded(rendered))
        return *rendered;
      if (auto rendered = readableGuardedRequirement(value); succeeded(rendered))
        return *rendered;
      if (auto rendered = readableRequirementBlock(value); succeeded(rendered))
        return *rendered;
      if (auto rendered = readableSelectExpression(value); succeeded(rendered))
        return *rendered;
    }
    if (isa<ac::InstanceOp, ac::CollectionOp>(op)) {
      bool readable = isReadableRegister(op);
      bool ordinaryModule = false;
      if (context.isPhysical())
        if (auto instance = dyn_cast<ac::InstanceOp>(op))
          ordinaryModule = isa_and_nonnull<ac::ModuleOp>(context.analysis.resolveCallee(instance));
      std::string name;
      if (readable) {
        auto id = rtlIdentifier(op->getAttrOfType<StringAttr>("instance_name").getValue(),
                                     [&] { return op->emitOpError(); });
        if (failed(id))
          return failure();
        name = readableName(*id, true);
      } else if (!ordinaryModule) name = sourceNetName(value);
      if (context.isPhysical() && !readable) {
        if (auto instance = dyn_cast<ac::InstanceOp>(op)) {
          auto child = dyn_cast<ac::ModuleOp>(context.analysis.resolveCallee(instance));
          if (child) {
            unsigned index = cast<OpResult>(value).getResultNumber();
            if (auto projection = context.rtlOutputProjection(child, index)) {
              auto source = net(instance.getResult(projection->output));
              if (failed(source)) return failure();
              std::string expression = *source;
              for (const auto &field : projection->fields) {
                auto name = rtlIdentifier(field, [&] { return instance.emitOpError(); });
                if (failed(name)) return failure();
                expression += "." + *name;
              }
              names.try_emplace(value, expression);
              readableBypassedResults.insert(value);
              return expression;
            }
            if (auto input = context.rtlForwardedInput(child, index)) {
              auto alias = net(instance.getOperand(*input));
              if (failed(alias)) return failure();
              names.try_emplace(value, *alias);
              instances.insert(op);
              return *alias;
            }
            auto layout = ac::getModulePortLayout(child);
            if (failed(layout)) return failure();
            Value source = readableSource(cast<ac::YieldOp>(child.getBody().front().back()).getValues()[index]);
            if (auto argument = dyn_cast<BlockArgument>(source)) {
              if (index >= layout->sourceOutputCount && argument.getOwner()->getParentOp() == child) {
                auto alias = net(instance.getOperand(argument.getArgNumber()));
                if (failed(alias)) return failure();
                names.try_emplace(value, *alias);
                readableBypassedResults.insert(value);
                instances.insert(op);
                return *alias;
              }
            }
            auto owner = readableInstanceName(instance);
            auto port = context.rtlPortName(child, cast<StringAttr>(child.getOutputNames()[index]).getValue());
            if (failed(owner) || failed(port)) return failure();
            std::string preferred = rtlIdentifierStem(*owner) + "_" + rtlIdentifierStem(*port);
            if (auto state = source.getDefiningOp<ac::InstanceOp>())
              if (isReadableRegister(state)) {
                auto id = rtlIdentifier(state.getInstanceName(), [&] { return state.emitOpError(); });
                if (failed(id)) return failure();
                preferred = rtlIdentifierStem(*owner) + "_" + rtlIdentifierStem(*id);
              }
            name = readableName(preferred);
          }
        }
      }
      auto type = context.rtlType(value.getType(), op);
      if (failed(type))
        return failure();
      readableDeclaration(readable ? "" : "wire", *type, name, {}, readable);
      names.try_emplace(value, name);
      instances.insert(op);
      return name;
    }
    if (auto rule = dyn_cast<ac::RuleOp>(op)) {
      auto yield = cast<ac::YieldOp>(rule.getBody().front().back());
      auto source =
          net(yield.getValues()[cast<OpResult>(value).getResultNumber()]);
      if (failed(source))
        return failure();
      names.try_emplace(value, *source);
      return *source;
    }
    if (isa<ac::TableCreateOp, ac::TableSplatOp, ac::TableMapOp,
            ac::TableViewOp, ac::TableIndexOp, ac::TableReadOp, ac::TableGetOp, ac::TableMatchOp,
            ac::TableChooseOp, ac::TableFoldOp, ac::ValueMergeOp>(op)) {
      if (failed(tableOperation(op, value)))
        return failure();
      return names.lookup(value);
    }
    // Register the complete net before following producers. A legal
    // field-level graph can refer to another field of this same aggregate.
    auto name = sourceNetName(value);
    auto type = context.rtlType(value.getType(), op);
    if (failed(type))
      return failure();
    bool combinationalDivRem = false;
    if (auto binary = dyn_cast<ac::BitsBinaryOp>(op))
      combinationalDivRem =
          binary.getOpcode() == "udiv" || binary.getOpcode() == "urem";
    if (!context.isPhysical())
      readableDeclaration(combinationalDivRem ? "" : "wire", *type, name);
    names.try_emplace(value, name);
    readablePending.insert(value);
    SmallVector<std::string> operands;
    auto runtimeOperands = op->getOperands();
    if (isa<ac::ValueRequireOp>(op))
      runtimeOperands = runtimeOperands.drop_front();
    for (auto input : runtimeOperands) {
      auto item = net(input);
      if (failed(item))
        return failure();
      operands.push_back(readableTypedOperand(input, value, op, *item));
    }
    std::string expression;
    if (isa<ac::ValueRequireOp>(op))
      expression = "(" + operands[1] + " ? " + operands[0] + " : 1'b1)";
    else if (auto create = dyn_cast<ac::EnumCreateOp>(op)) {
      auto member = context.rtlEnumMember(create.getResult().getType(),
                                           create.getMemberAttr(), op);
      if (failed(member))
        return failure();
      expression = *member;
    } else if (isa<ac::EnumToBitsOp>(op))
      expression = operands[0];
    else if (auto fromBits = dyn_cast<ac::EnumFromBitsOp>(op)) {
      if (cast<OpResult>(value).getResultNumber() == 0)
        expression = operands[0];
      else {
        auto definition =
            context.analysis.resolveEnum(fromBits.getValue().getType(), op);
        if (failed(definition))
          return failure();
        for (const auto &member : definition->members) {
          auto symbol = context.rtlEnumMember(fromBits.getValue().getType(), member.name, op);
          if (failed(symbol)) return failure();
          auto equal = "(" + operands[0] + " == " + *symbol + ")";
          expression = expression.empty()
                           ? equal
                           : "(" + expression + " | " + equal + ")";
        }
      }
    } else if (auto pattern = dyn_cast<ac::BitsConstant4Op>(op)) {
      expression = std::to_string(pattern.getPattern().size()) + "'b" +
                   pattern.getPattern().str();
    } else if (auto constant = dyn_cast<ac::BitsConstantOp>(op)) {
      auto literal = context.staticRtlValue(constant.getValue(), op);
      if (failed(literal))
        return failure();
      auto width = context.staticRtlValue(
          cast<ac::BitsType>(value.getType()).getWidth(), op);
      if (failed(width))
        return failure();
      if (context.isClosedStatic(constant.getValue())) {
        llvm::APSInt value(*literal);
        *literal = std::to_string(std::max(1u, value.getActiveBits())) + "'d" +
                   *literal;
      }
      expression = "(" + *width + ")'( " + *literal + " )";
    } else if (auto unary = dyn_cast<ac::BitsUnaryOp>(op)) {
      if (unary.getOpcode() != "not")
        return op->emitOpError() << "unsupported RTL unary op";
      expression = std::string(context.isPhysical() && readableKnownBit(value) ? "(!" : "(~") + operands[0] + ")";
    } else if (auto binary = dyn_cast<ac::BitsBinaryOp>(op)) {
      if (binary.getOpcode() == "udiv" || binary.getOpcode() == "urem") {
        const auto &lhs = operands[0];
        const auto &rhs = operands[1];
        expression = "($unsigned(" + lhs + ") " +
                     (binary.getOpcode() == "udiv" ? "/" : "%") +
                     " $unsigned(" + rhs + "))";
      } else {
        auto symbol = llvm::StringSwitch<StringRef>(binary.getOpcode())
                          .Case("and", "&")
                          .Case("or", "|")
                          .Case("xor", "^")
                          .Case("add", "+")
                          .Case("sub", "-")
                          .Case("mul", "*")
                          .Case("shl", "<<")
                          .Case("lshr", ">>")
                          .Case("ashr", ">>>")
                          .Default("");
        if (symbol.empty())
          return op->emitOpError() << "unsupported RTL binary op";
        if (context.isPhysical() && readableKnownBit(value)) {
          if (binary.getOpcode() == "and") symbol = "&&";
          if (binary.getOpcode() == "or") symbol = "||";
        }
        expression =
            "(" +
            (binary.getOpcode() == "ashr" ? "$signed(" + operands[0] + ")"
                                          : operands[0]) +
            " " + symbol.str() + " " + operands[1] + ")";
      }
    } else if (auto compare = dyn_cast<ac::BitsCompareOp>(op)) {
      auto predicate = llvm::StringSwitch<StringRef>(compare.getPredicate())
                           .Case("eq", "==")
                           .Case("ne", "!=")
                           .Case("case_eq", "===")
                           .Case("ult", "<")
                           .Case("ule", "<=")
                           .Case("ugt", ">")
                           .Case("uge", ">=")
                           .Case("slt", "<")
                           .Case("sle", "<=")
                           .Case("sgt", ">")
                           .Case("sge", ">=")
                           .Default("");
      if (predicate.empty())
        return op->emitOpError() << "unsupported RTL comparison";
      bool signedCompare = compare.getPredicate().starts_with("s");
      expression = std::string("(") + (signedCompare ? "$signed(" : "") +
                   operands[0] + (signedCompare ? ")" : "") + " " +
                   predicate.str() + " " + (signedCompare ? "$signed(" : "") +
                   operands[1] + (signedCompare ? ")" : "") + ")";
    } else if (isa<ac::BitsSelectOp>(op))
      expression =
          "(" + operands[0] + " ? " + operands[1] + " : " + operands[2] + ")";
    else if (isa<ac::BitsConcatOp>(op)) {
      expression = "{";
      for (auto [i, item] : llvm::enumerate(operands))
        expression += (i ? ", " : "") + item;
      expression += "}";
    } else if (auto extracted = dyn_cast<ac::BitsExtractOp>(op)) {
      auto low = context.staticRtlValue(extracted.getLow(), op);
      if (failed(low))
        return failure();
      auto type = context.rtlType(value.getType(), op);
      if (failed(type))
        return failure();
      auto width = context.staticRtlValue(
          cast<ac::BitsType>(value.getType()).getWidth(), op);
      if (failed(width))
        return failure();
      expression = readableFullExtract(value) != value
          ? operands[0]
          : operands[0] + "[(" + *low + ") +: " + *width + "]";
    } else if (auto resized = dyn_cast<ac::BitsResizeOp>(op)) {
      auto type = context.rtlType(value.getType(), op);
      if (failed(type))
        return failure();
      auto width = context.staticRtlValue(
          cast<ac::BitsType>(value.getType()).getWidth(), op);
      if (failed(width))
        return failure();
      if (resized.getMode() == "sext")
        expression = "(" + *width + ")'($signed(" + operands[0] + "))";
      else if (resized.getMode() == "zext")
        expression = "(" + *width + ")'($unsigned(" + operands[0] + "))";
      else if (resized.getMode() == "trunc")
        expression = "(" + *width + ")'(" + operands[0] + ")";
      else
        return op->emitOpError() << "unsupported RTL resize";
    } else if (isa<ac::StructCreateOp>(op)) {
      expression = "{";
      for (auto [i, item] : llvm::enumerate(operands))
        expression += (i ? ", " : "") + item;
      expression += "}";
    } else if (auto get = dyn_cast<ac::StructGetOp>(op)) {
      auto name =
          rtlIdentifier(get.getField(), [&] { return op->emitOpError(); });
      if (failed(name))
        return failure();
      expression = operands[0] + "." + *name;
    } else
      return op->emitOpError() << "operation lacks RTL hardware emission";
    readablePending.erase(value);
    if (context.isPhysical() && !combinationalDivRem && !readableRetained.contains(value) &&
        readableExpressionCost(value) <= readableExpressionLimit && canInlineReadable(value, op)) {
      // Field and slice references already have their declared self-determined
      // width. Unlike arithmetic, they cannot widen an interior computation.
      std::string rendered = isa<ac::StructGetOp, ac::BitsExtractOp>(op) || readableKnownBit(value) ? expression :
          std::to_string(*readableWidth(value)) + "'(" + expression + ")";
      if ((isa<ac::BitsResizeOp>(op) &&
           cast<ac::BitsResizeOp>(op).getMode() == "sext") ||
          (isa<ac::BitsBinaryOp>(op) &&
           cast<ac::BitsBinaryOp>(op).getOpcode() == "ashr"))
        rendered = "$unsigned(" + rendered + ")";
      names[value] = rendered;
      readableInlineExpressions[value] = expression;
      readableInlineCosts[value] = readableExpressionCost(value);
      return rendered;
    }
    if (context.isPhysical())
      readableDeclaration(combinationalDivRem ? "" : "wire", *type, name);
    readableAssignment(name, expression, combinationalDivRem);
    return name;
  }
  LogicalResult tableOperation(Operation *op, Value requested) {
    for (Value result : op->getResults()) {
      if (readableUnusedTableResult(result, requested)) continue;
      auto type = context.rtlType(result.getType(), op);
      if (failed(type))
        return failure();
      auto name = sourceNetName(result);
      readableDeclaration("wire", *type, name);
      names.try_emplace(result, name);
    }
    SmallVector<std::string> operands;
    for (auto [ordinal, value] : llvm::enumerate(op->getOperands())) {
      if (context.isPhysical() && isa<ac::TableMapOp>(op) && isa<ac::TableType>(value.getType()) &&
          readableBroadcast(value)) {
        operands.emplace_back();
        continue;
      }
      // A folded, representable Table index needs no otherwise-unused wire.
      // Keep every runtime operand when either the index or extent is symbolic.
      if (auto get = dyn_cast<ac::TableGetOp>(op); get && ordinal == 1 &&
          readableConstantIndex(value)) {
        auto table = cast<ac::TableType>(get.getInput().getType());
        auto extent = context.shapeSize(table.getShape(), op, true);
        if (failed(extent)) return failure();
        if (readableUnsigned(*extent)) {
          operands.emplace_back();
          continue;
        }
      }
      auto source = net(value);
      if (failed(source))
        return failure();
      operands.push_back(*source);
    }
    auto resultName = [&](unsigned i = 0) {
      return names.lookup(op->getResult(i));
    };
    auto width = [&](Type type) {
      return context.payloadWidth(type, op, true);
    };
    auto count = [&](ac::TableType type) {
      return context.shapeSize(type.getShape(), op, true);
    };
    auto element = [&](StringRef value, StringRef ordinal,
                       ac::TableType type) -> FailureOr<std::string> {
      return readablePackedElement(value, ordinal, type, op);
    };
    auto generate = [&](StringRef n, StringRef label) {
      auto prefix = resultName().empty() ? names.lookup(requested) : resultName();
      std::string i = context.isPhysical() ? readableName(rtlIdentifierStem(prefix) + "_index")
                                          : "pyc_index_" + std::to_string(next++);
      std::string block = context.isPhysical() ? readableName(rtlIdentifierStem(prefix) + "_elements")
                                               : label.str();
      out << "  for (genvar " << i << "=0; " << i << " < (" << n << "); ++" << i
          << ") begin : " << block << "\n";
      readableSections.beginScope();
      return i;
    };
    if (auto create = dyn_cast<ac::TableCreateOp>(op)) {
      auto type = cast<ac::TableType>(create.getResult().getType());
      for (auto [i, input] : llvm::enumerate(operands)) {
        auto target = element(resultName(), std::to_string(i), type);
        if (failed(target))
          return failure();
        out << "  assign " << *target << " = " << input << ";\n";
      }
      return success();
    }
    if (auto splat = dyn_cast<ac::TableSplatOp>(op)) {
      auto n = context.shapeSize(splat.getShape(), op, true);
      auto w = width(splat.getInput().getType());
      if (failed(n) || failed(w))
        return failure();
      if (readableUnsigned(*n)) {
        out << "  assign " << resultName() << " = {" << *n << "{" << operands[0]
            << "}};\n";
        return success();
      }
      auto i = generate(*n, "pyc_broadcast_" + resultName());
      out << "    assign " << resultName() << "[((" << *n << ")-1-" << i
          << ")*(" << *w << ") +: (" << *w << ")] = " << operands[0]
          << ";\n";
      finishReadableGenerate();
      return success();
    }
    if (auto view = dyn_cast<ac::TableViewOp>(op)) {
      auto srcType = cast<ac::TableType>(view.getInput().getType());
      auto dstType = cast<ac::TableType>(view.getResult().getType());
      auto n = count(dstType);
      if (failed(n))
        return failure();
      auto i = generate(*n, "pyc_view_" + resultName());
      auto mapped = context.viewIndex(view, i, true);
      if (failed(mapped))
        return failure();
      auto src = element(operands[0], *mapped, srcType);
      auto dst = element(resultName(), i, dstType);
      if (failed(src) || failed(dst))
        return failure();
      out << "    assign " << *dst << " = " << *src << ";\n";
      finishReadableGenerate();
      return success();
    }
    if (auto index = dyn_cast<ac::TableIndexOp>(op)) {
      auto n = context.shapeSize(index.getShape(), op, true);
      auto targetWidth = width(index.getResult().getType());
      if (failed(n) || failed(targetWidth))
        return failure();
      SmallVector<std::string> shape, widths;
      std::string sumWidth = "64";
      for (auto raw : index.getShape()) {
        auto dim = context.staticRtlValue(cast<ac::StaticExprAttr>(raw), op);
        if (failed(dim))
          return failure();
        shape.push_back(*dim);
      }
      for (auto value : index.getCoords()) {
        auto bits = width(value.getType());
        if (failed(bits))
          return failure();
        widths.push_back(*bits);
        sumWidth += " + (" + *bits + ")";
      }
      std::string inBounds = "1'b1", sum = "(" + sumWidth + ")'(0)";
      std::string stride = "1";
      for (size_t axis = shape.size(); axis-- > 0;) {
        auto compareWidth = readableTableBoundWidth(shape[axis], widths[axis]);
        inBounds += " & ((" + compareWidth + ")'($unsigned(" + operands[axis] +
                    ")) < (" + compareWidth + ")'(" + shape[axis] + "))";
        sum += " + (" + sumWidth + ")'($unsigned(" + operands[axis] + ")) * (" +
               sumWidth + ")'(" + stride + ")";
        stride = "(" + stride + " * (" + shape[axis] + "))";
      }
      out << "  assign " << resultName() << " = (" << inBounds << ") ? ("
          << *targetWidth << ")'(" << sum << ") : (" << *targetWidth << ")'("
          << *n << ");\n";
      return success();
    }
    if (isa<ac::TableReadOp, ac::TableGetOp>(op)) {
      auto type = cast<ac::TableType>(op->getOperand(0).getType());
      auto n = count(type), k = width(op->getOperand(1).getType());
      if (failed(n) || failed(k)) return failure();
      auto w = readableTableBoundWidth(*n, *k);
      auto index = readableConstantIndex(op->getOperand(1));
      auto size = readableUnsigned(*n);
      bool membership = isa<ac::TableGetOp>(op);
      if (index && size) {
        bool valid = *index < *size;
        auto selected = valid ? element(operands[0], std::to_string(*index), type)
                              : FailureOr<std::string>(std::string("'x"));
        if (failed(selected)) return failure();
        if (membership)
          out << "  assign " << resultName(1) << " = " << (valid ? "1'b1" : "1'b0") << ";\n";
        out << "  assign " << resultName() << " = " << *selected << ";\n";
        return success();
      }
      auto selected = element(operands[0], "$unsigned(" + operands[1] + ")", type);
      if (failed(selected)) return failure();
      std::string range = "(" + w + ")'($unsigned(" + operands[1] + ")) < (" + w + ")'(" + *n + ")";
      if (membership) {
        out << "  assign " << resultName(1) << " = " << range << ";\n";
        range = resultName(1);
      }
      out << "  assign " << resultName() << " = " << range << " ? "
          << *selected << " : 'x;\n";
      return success();
    }
    if (isa<ac::TableMapOp, ac::TableMatchOp>(op)) {
      bool isMap = isa<ac::TableMapOp>(op);
      SmallVector<Value> tables;
      if (isMap)
        llvm::append_range(tables, cast<ac::TableMapOp>(op).getTables());
      else
        tables.push_back(op->getOperand(0));
      auto shape =
          isMap ? cast<ac::TableMapOp>(op).getShape()
                : cast<ac::TableType>(op->getOperand(0).getType()).getShape();
      auto n = context.shapeSize(shape, op, true);
      if (failed(n))
        return failure();
      auto i = generate(*n, "pyc_map_" + resultName());
      Block &block = op->getRegion(0).front();
      unsigned arg = 0;
      if (isMap) {
        auto w = width(block.getArgument(0).getType());
        if (failed(w))
          return failure();
        names[block.getArgument(arg++)] = "(" + *w + ")'(" + i + ")";
      }
      for (auto [j, value] : llvm::enumerate(tables)) {
        auto type = cast<ac::TableType>(value.getType());
        auto selected = context.isPhysical() && readableBroadcast(value)
            ? net(readableBroadcast(value)) : element(operands[j], i, type);
        auto dataType = context.rtlType(type.getElementType(), op);
        if (failed(selected) || failed(dataType))
          return failure();
        auto local = context.isPhysical() ? readableName(rtlIdentifierStem(resultName()) + "_input_" + std::to_string(j))
                                         : "pyc_lane_" + std::to_string(next++);
        readableDeclaration("wire", *dataType, local, *selected, false, 4);
        names[block.getArgument(arg++)] = local;
      }
      for (size_t j = tables.size(); j < operands.size(); ++j)
        names[block.getArgument(arg++)] = operands[j];
      auto yielded = cast<ac::YieldOp>(block.back()).getValues();
      for (auto [j, value] : llvm::enumerate(yielded)) {
        if (isMap && resultName(j).empty()) continue;
        auto source = net(value);
        if (failed(source))
          return failure();
        if (isMap) {
          auto dst = element(resultName(j), i,
                             cast<ac::TableType>(op->getResult(j).getType()));
          if (failed(dst))
            return failure();
          out << "    assign " << *dst << " = " << *source << ";\n";
        } else
          out << "    assign " << resultName() << "[" << i << "] = " << *source
              << ";\n";
      }
      finishReadableGenerate();
      return success();
    }
    if (auto choose = dyn_cast<ac::TableChooseOp>(op)) {
      auto type = cast<ac::TableType>(choose.getInput().getType());
      auto n = count(type), w = width(choose.getResults().front().getType());
      if (failed(n) || failed(w))
        return failure();
      auto c = choose.getCount();
      auto prefix = "choice_" + rtlIdentifierStem(resultName());
      auto mask = context.isPhysical() ? readableName(prefix + "_mask") : prefix + "_mask";
      auto index = context.isPhysical() ? readableName(prefix + "_index") : prefix + "_index";
      auto valid = context.isPhysical() ? readableName(prefix + "_valid") : prefix + "_valid";
      readableDeclaration("wire", "[(" + *n + ")-1:0]", mask + " [0:" + std::to_string(c) + "]");
      readableDeclaration("wire", "[(" + *w + ")-1:0]", index + " [0:" + std::to_string(c - 1) + "][0:(" + *n + ")]");
      readableDeclaration("wire", "", valid + " [0:" + std::to_string(c - 1) + "]");
      out << "  assign " << mask << "[0] = " << operands[1] << ";\n";
      auto pass = generate(std::to_string(c), prefix + "_passes");
      out << "    assign " << index << "[" << pass << "][0] = '0;\n"
          << "    assign " << valid << "[" << pass << "] = |" << mask
          << "[" << pass << "];\n";
      auto step = generate(*n, prefix + "_scan");
      auto k =
          choose.getOrder() == "low" ? "((" + *n + ")-1-" + step + ")" : step;
      out << "    assign " << index << "[" << pass << "][" << step
          << "+1] = " << mask << "[" << pass << "][" << k << "] ? ("
          << *w << ")'(" << k << ") : " << index << "[" << pass << "]["
          << step << "];\n"
          << "    assign " << mask << "[" << pass << "+1][" << step
          << "] = " << mask << "[" << pass << "][" << step << "] & ~("
          << valid << "[" << pass << "] & (" << index << "["
          << pass << "][" << *n << "] == (" << *w << ")'(" << step << ")));\n"
          ;
      finishReadableGenerate();
      finishReadableGenerate();
      for (int64_t j = 0; j < c; ++j)
        out << "  assign " << resultName(j) << " = " << index << "[" << j
            << "][" << *n << "];\n"
            << "  assign " << resultName(c + j) << " = " << valid << "["
            << j << "];\n";
      return success();
    }
    if (auto fold = dyn_cast<ac::TableFoldOp>(op)) {
      auto type = cast<ac::TableType>(fold.getInput().getType());
      auto n = count(type), w = width(type.getElementType());
      if (failed(n) || failed(w))
        return failure();
      auto preferred = "fold_" + rtlIdentifierStem(resultName());
      auto prefix = context.isPhysical() ? readableName(preferred) : preferred;
      readableDeclaration("wire", "[(" + *n + ")*(" + *w + ")-1:0]", prefix + " [0:$clog2(" + *n + ")]");
      out << "  assign " << prefix << "[0] = " << operands[0] << ";\n";
      auto level = generate("$clog2(" + *n + ")", prefix + "_levels");
      auto previousCount = "(((" + *n + ") + ((64'd1 << " + level +
                           ")-1)) / (64'd1 << " + level + "))";
      auto lane = generate("((" + previousCount + "+1)/2)", prefix + "_pairs");
      auto a = prefix + "[" + level + "][((" + *n + ")-1-2*" + lane + ")*(" +
               *w + ") +: (" + *w + ")]";
      auto b = prefix + "[" + level + "][((" + *n + ")-2-2*" + lane + ")*(" +
               *w + ") +: (" + *w + ")]";
      auto dst = prefix + "[" + level + "+1][((" + *n + ")-1-" + lane + ")*(" +
                 *w + ") +: (" + *w + ")]";
      std::string expression;
      if (fold.getKind() == "min" || fold.getKind() == "max")
        expression = "(" + a + (fold.getKind() == "min" ? " <= " : " >= ") + b +
                     " ? " + a + " : " + b + ")";
      else {
        auto symbol = llvm::StringSwitch<StringRef>(fold.getKind())
                          .Case("add", "+")
                          .Case("mul", "*")
                          .Case("and", "&")
                          .Case("or", "|")
                          .Case("xor", "^")
                          .Default("");
        expression = "(" + a + " " + symbol.str() + " " + b + ")";
      }
      out << "    if (2*" << lane << "+1 < " << previousCount << ") begin\n"
          << "      assign " << dst << " = " << expression << ";\n"
          << "    end else begin\n      assign " << dst << " = " << a
          << ";\n    end\n";
      finishReadableGenerate();
      finishReadableGenerate();
      out << "  assign " << resultName() << " = " << prefix << "[$clog2(" << *n
          << ")][((" << *n << ")-1)*(" << *w << ") +: (" << *w << ")];\n";
      return success();
    }
    if (auto merge = dyn_cast<ac::ValueMergeOp>(op)) {
      auto field = [&](StringRef base,
                       ArrayRef<StringAttr> path) -> FailureOr<std::string> {
        std::string text = base.str();
        for (auto item : path) {
          auto id = rtlIdentifier(item.getValue(),
                                       [&] { return op->emitOpError(); });
          if (failed(id))
            return failure();
          text += "." + *id;
        }
        return text;
      };
      ac::HardwareBindings bindings;
      bindings.owner = definition;
      auto leaves = context.analysis.getFieldPaths(merge.getBase().getType(),
                                                   bindings, op);
      if (failed(leaves))
        return failure();
      // Empty-path whole-Table merge selects the complete packed value.
      // Dependency paths descend Table element records, but RTL Tables are
      // packed vectors. Preserve such a field as one complete packed value.
      SmallVector<ac::FieldPath> packedPaths;
      for (auto path : *leaves) {
        Type type = merge.getBase().getType();
        for (size_t i = 0; i < path.size(); ++i) {
          auto resolved = context.analysis.resolveType(type, bindings, op);
          if (failed(resolved))
            return failure();
          if (isa<ac::TableType>(*resolved)) {
            path.resize(i);
            break;
          }
          auto record = dyn_cast<ac::StructType>(*resolved);
          auto declaration =
              record ? context.analysis.lookupStruct(record) : ac::StructOp();
          if (!declaration)
            return op->emitOpError() << "RTL merge has unresolved field path";
          auto fields = declaration.getFields();
          auto found = llvm::find_if(fields, [&](Attribute raw) {
            return cast<DictionaryAttr>(raw).getAs<StringAttr>("name") ==
                   path[i];
          });
          if (found == fields.end())
            return op->emitOpError() << "RTL merge has unknown field path";
          type =
              cast<DictionaryAttr>(*found).getAs<TypeAttr>("type").getValue();
        }
        if (!llvm::is_contained(packedPaths, path))
          packedPaths.push_back(std::move(path));
      }
      std::string enables = "1'b0";
      for (auto [j, raw] : llvm::enumerate(merge.getPaths())) {
        auto attr = cast<ArrayAttr>(raw);
        ac::FieldPath path;
        for (auto item : attr)
          path.push_back(cast<StringAttr>(item));
        auto dst = field(resultName(), path), old = field(operands[0], path);
        if (failed(dst) || failed(old))
          return failure();
        auto guard = operands[1 + j];
        auto value = operands[1 + merge.getGuards().size() + j];
        out << "  assign " << *dst << " = " << guard << " ? " << value << " : "
            << *old << ";\n";
        enables += " | " + guard;
      }
      for (auto &path : packedPaths) {
        bool written = llvm::any_of(merge.getPaths(), [&](Attribute raw) {
          auto p = cast<ArrayAttr>(raw);
          return p.size() <= path.size() &&
                 std::equal(p.begin(), p.end(), path.begin());
        });
        if (written)
          continue;
        auto dst = field(resultName(), path), old = field(operands[0], path);
        if (failed(dst) || failed(old))
          return failure();
        out << "  assign " << *dst << " = " << *old << ";\n";
      }
      if (!resultName(1).empty())
        out << "  assign " << resultName(1) << " = " << enables << ";\n";
      return success();
    }
    return op->emitOpError() << "table operation lacks RTL emission";
  }

  LogicalResult emitInstances() {
    for (auto &operation : definition.getBody().front()) {
      if (auto grouped = readableInstanceArrayLanes.find(&operation); grouped != readableInstanceArrayLanes.end()) {
        if (grouped->second.second == 0 && failed(emitReadableInstanceArray(grouped->second.first))) return failure();
        continue;
      }
      auto sectionName = operation.getAttrOfType<StringAttr>("instance_name");
      auto section = readableSections.select("instance:" + (sectionName ? sectionName.getValue().str() : ""),
          (isReadableRegister(&operation) ? "State update: " : "Instance: ") + (sectionName ? sectionName.getValue().str() : ""), 3000);
      if (auto queue = dyn_cast<ac::InstanceOp>(operation);
          queue && ac::isQueueInstance(queue)) {
        SmallVector<std::string> pins;
        for (auto input : queue->getOperands()) {
          auto value = net(input);
          if (failed(value))
            return failure();
          pins.push_back(*value);
        }
        for (auto output : queue->getResults()) {
          auto value = net(output);
          if (failed(value))
            return failure();
          pins.push_back(*value);
        }
        auto config = ac::getQueueConfiguration(queue);
        if (failed(config))
          return failure();
        auto payload = context.rtlType(queue.getInputs()[3].getType(), queue);
        auto depth = context.staticRtlValue(
            config->getAs<ac::StaticExprAttr>("depth"), queue);
        auto latency = context.unsignedStaticValue(
            config->getAs<ac::StaticExprAttr>("availability_latency"), queue,
            true);
        auto name = context.isPhysical()
            ? rtlIdentifier(queue.getInstanceName(), [&] { return queue.emitOpError(); })
            : legalizeIdentifier(queue.getInstanceName(), [&] { return queue.emitOpError(); });
        if (failed(payload) || failed(depth) || failed(latency) || failed(name))
          return failure();
        unsigned policy =
            config->getAs<StringAttr>("ready_policy").getValue() ==
                    "local_occupancy"
                ? 0
                : 1;
        std::string error;
        if (context.managesChecks()) {
          error = "pyc_child_error_" + std::to_string(localErrors.size());
          out << "  wire " << error << ";\n";
          localErrors.push_back(error);
        }
        out << "  fifo #(.T(" << *payload << "), .DEPTH(" << *depth
            << "), .READY_POLICY(" << policy << "), .AVAILABILITY_LATENCY("
            << *latency;
        if (context.managesChecks())
          out << "), .pyc_managed(1'b1";
        auto queueName = context.isPhysical() ? readableInstanceName(queue)
            : FailureOr<std::string>("pyc_instance_" + rtlIdentifierStem(*name));
        if (failed(queueName)) return failure();
        readableInstanceNames[queue] = *queueName;
        out << ")) " << *queueName << " (\n";
        const StringRef ports[] = {"clk",       "rst",       "in_valid",
                                   "in_data",   "out_ready", "in_ready",
                                   "out_valid", "out_data",  "local_capacity"};
        pins[1] = context.rtlReset(pins[1]);
        for (auto [index, port] : llvm::enumerate(ports))
          out << "    ." << port << "(" << pins[index] << ")"
              << (index + 1 == std::size(ports) && !context.managesChecks()
                      ? "\n"
                      : ",\n");
        if (context.managesChecks())
          out << "    .pyc_phase(pyc_phase),\n"
                 "    .pyc_root_commit_ok(pyc_root_commit_ok),\n"
                 "    .pyc_local_error("
              << error << ")\n  );\n";
        else
          out << "  );\n";
        continue;
      }
      if (!isa<ac::InstanceOp, ac::CollectionOp>(operation))
        continue;
      if (isReadableRegister(&operation)) {
        auto result = isa<ac::CollectionOp>(operation)
            ? emitReadableCollection(cast<ac::CollectionOp>(operation))
            : emitReadableRegister(cast<ac::InstanceOp>(operation));
        if (failed(result))
          return failure();
        continue;
      }
      Operation *occurrence = &operation;
      bool collection = isa<ac::CollectionOp>(operation);
      auto *callee =
          collection
              ? context.analysis.resolveCallee(
                    cast<ac::CollectionOp>(operation))
              : context.analysis.resolveCallee(cast<ac::InstanceOp>(operation));
      auto bindings =
          collection
              ? context.analysis.bindInstance(cast<ac::CollectionOp>(operation))
              : context.analysis.bindInstance(cast<ac::InstanceOp>(operation));
      if (failed(bindings))
        return failure();
      auto kind = context.analysis.getPrimitiveKind(callee);
      if (context.isSynthesis() && !kind.empty() && kind != "sync_mem")
        return occurrence->emitOpError() << "synthesis RTL requires supported DFF/DFFE storage";
      bool managedPrimitive = false;
      if (!context.isSynthesis() &&
          (context.managesChecks() || context.isPhysical()) && !kind.empty())
        managedPrimitive =
            llvm::any_of(context.sourceChecks().commits,
                         [&](const ac::HardwareCheckCommitEndpoint &endpoint) {
                           return endpoint.allocation == occurrence;
                         });
      SmallVector<std::string> inputs, outputs;
      auto planned = collection ? nullptr : context.rtlPartition(cast<ac::InstanceOp>(occurrence), ownership);
      for (auto [inputIndex, input] : llvm::enumerate(occurrence->getOperands())) {
        if ((planned && planned->replacedInputs.count(inputIndex)) || context.rtlOmittedInput(callee, inputIndex)) {
          inputs.emplace_back();
          continue;
        }
        auto value = net(input);
        if (failed(value))
          return failure();
        inputs.push_back(*value);
      }
      for (auto [outputIndex, output] : llvm::enumerate(occurrence->getResults())) {
        if (context.rtlForwardedInput(callee, outputIndex) || context.rtlOmittedOutput(callee, outputIndex)) {
          outputs.emplace_back();
          continue;
        }
        auto value = net(output);
        if (failed(value))
          return failure();
        outputs.push_back(*value);
      }
      auto parameters =
          collection
              ? context.rtlInstanceParameters(cast<ac::CollectionOp>(operation))
              : context.rtlInstanceParameters(cast<ac::InstanceOp>(operation));
      if (succeeded(parameters) && planned && !planned->parameters.empty()) {
        SmallVector<std::string> additions;
        for (const auto &parameter : planned->parameters) {
          auto value = context.rtlParameterName(FlatSymbolRefAttr::get(SymbolTable::getSymbolName(parameter.owner)),
              parameter.name.getValue(), occurrence);
          if (failed(value)) return failure();
          additions.push_back(*value);
        }
        if (parameters->empty()) *parameters = " #( " + join(additions, ", ") + " )";
        else {
          auto close = parameters->rfind(')');
          if (close == std::string::npos) return occurrence->emitOpError() << "malformed scoped parameter list";
          parameters->insert(close, ", " + join(additions, ", "));
        }
      }
      if (planned) {
        for (const auto &port : planned->captures)
          if (!port.local) {
            auto signal = net(port.value);
            if (failed(signal)) return failure();
            names[port.value] = *signal;
          }
        for (const auto &port : planned->exports) {
          auto signal = net(port.value);
          if (failed(signal)) return failure();
        }
      }
      auto rawName = occurrence->getAttrOfType<StringAttr>("instance_name").getValue();
      auto name = context.isPhysical()
          ? rtlIdentifier(rawName, [&] { return occurrence->emitOpError(); })
          : legalizeIdentifier(rawName, [&] { return occurrence->emitOpError(); });
      if (failed(parameters) || failed(name))
        return failure();
      if (managedPrimitive) {
        if (parameters->empty())
          *parameters = (context.isPhysical() ? " #( .pyc_physical(1'b1) )"
                                              : " #( .pyc_managed(1'b1) )");
        else {
          auto close = parameters->rfind(')');
          if (close == std::string::npos)
            return occurrence->emitOpError()
                   << "malformed RTL primitive parameter list";
          parameters->insert(close, context.isPhysical()
                                        ? ", .pyc_physical(1'b1) "
                                        : ", .pyc_managed(1'b1) ");
        }
      }
      std::string i, count;
      if (collection) {
        auto size = context.shapeSize(
            cast<ac::CollectionOp>(operation).getShape(), occurrence, true);
        if (failed(size))
          return failure();
        count = *size;
        i = "pyc_instance_lane_" + std::to_string(next++);
      }
      if (context.isPhysical() && managedPrimitive &&
          (kind == "dff" || kind == "dffe")) {
        unsigned initialIndex = kind == "dff" ? 3 : 4;
        auto initial =
            physicalInitializer(occurrence->getOperand(initialIndex));
        if (failed(initial))
          return failure();
        std::string selected = *initial;
        if (collection) {
          auto lane = readablePackedElement(selected, i,
              cast<ac::TableType>(occurrence->getOperand(initialIndex).getType()), occurrence);
          if (failed(lane)) return failure();
          selected = *lane;
        }
        auto close = parameters->rfind(')');
        if (close == std::string::npos)
          return occurrence->emitOpError()
                 << "physical primitive requires constant parameters";
        parameters->insert(close, ", .pyc_initial(" + selected + ") ");
      }
      std::string childError, childComplete, childSamplingError;
      if ((context.managesChecks() || context.hasPhysicalChecks())) {
        childError = context.isPhysical() ? "__checks_child_" + rtlIdentifierStem(*name) :
            "pyc_child_error_" + std::to_string(localErrors.size());
        if (collection)
          out << "  wire [(" << count << ")-1:0] " << childError << ";\n";
        else
          out << "  wire " << childError << ";\n";
        localErrors.push_back(collection ? "(|" + childError + ")"
                                         : childError);
        if (kind.empty() && !context.isPhysical()) {
          childComplete = childError + "_complete";
          childSamplingError = childError + "_sampling";
          auto type = collection ? "[(" + count + ")-1:0] " : "";
          out << "  wire " << type << childComplete << ";\n"
              << "  wire " << type << childSamplingError << ";\n";
          localCompletions.push_back(collection ? "(&" + childComplete + ")"
                                                : childComplete);
          localSamplingErrors.push_back(collection
                                            ? "(|" + childSamplingError + ")"
                                            : childSamplingError);
        }
      }
      if (collection)
        out << "  for (genvar " << i << "=0; " << i << " < (" << count
            << "); ++" << i << ") begin : " << "pyc_instances_" << rtlIdentifierStem(*name)
            << "\n";
      auto instanceSpelling = context.isPhysical() ? readableInstanceName(occurrence)
          : FailureOr<std::string>("pyc_instance_" + rtlIdentifierStem(*name));
      if (failed(instanceSpelling)) return failure();
      std::string instanceName = *instanceSpelling;
      readableSections.describe("instance:" + (sectionName ? sectionName.getValue().str() : ""),
          "Instance: " + rtlIdentifierStem(instanceName), 3000);
      readableInstanceNames[occurrence] = instanceName;
      auto partition = planned;
      out << "  " << (partition ? partition->moduleName : kind.empty() ? context.names(callee).rtl : kind.str())
          << *parameters << " " << instanceName << " (";
      bool first = true;
      auto connect = [&](StringRef port, StringRef signal,
                         Type type) -> LogicalResult {
        auto id = context.rtlPortName(callee, port);
        if (failed(id))
          return failure();
        std::string net = signal.str();
        if (collection) {
          auto tableType = ac::TableType::get(occurrence->getContext(),
              cast<ac::CollectionOp>(occurrence).getShape(), type);
          auto dimensions = context.rtlTableDimensions(tableType, occurrence);
          if (failed(dimensions)) return failure();
          if (!dimensions->empty()) {
            net += "[" + i + "]";
          } else {
            auto width = context.payloadWidth(type, occurrence, true, *bindings);
            if (failed(width)) return failure();
            net += "[((" + count + ")-1-" + i + ")*(" + *width + ") +: (" + *width + ")]";
          }
        }
        if (!kind.empty() && port == "rst")
          net = context.rtlReset(net);
        out << (first ? "\n" : ",\n") << "    ." << *id << "(" << net << ")";
        first = false;
        return success();
      };
      auto signature = cast<FunctionType>(
          callee->getAttrOfType<TypeAttr>("function_type").getValue());
      auto inputNames = callee->getAttrOfType<ArrayAttr>("input_names");
      auto outputNames = callee->getAttrOfType<ArrayAttr>("output_names");
      for (auto [index, raw, signal, type] :
           llvm::enumerate(inputNames, inputs, signature.getInputs()))
        if (!(partition && partition->replacedInputs.count(index)) && !context.rtlOmittedInput(callee, index) &&
            failed(connect(cast<StringAttr>(raw).getValue(), signal, type)))
          return failure();
      unsigned outputOrdinal = 0;
      for (auto [raw, signal, type] :
           llvm::zip(outputNames, outputs, signature.getResults())) {
        if (context.rtlForwardedInput(callee, outputOrdinal) || context.rtlOmittedOutput(callee, outputOrdinal)) {
          ++outputOrdinal;
          continue;
        }
        if (readableBypassedResults.contains(occurrence->getResult(outputOrdinal++))) signal.clear();
        if (failed(connect(cast<StringAttr>(raw).getValue(), signal, type)))
          return failure();
      }
      if (partition) {
        auto extra = [&](const RtlOwnershipPort &port) -> LogicalResult {
          auto signal = names.find(port.value);
          if (signal == names.end()) return occurrence->emitOpError() << "unprepared RTL partition connection";
          out << (first ? "\n" : ",\n") << "    ." << port.name << "(" << signal->second << ")";
          first = false;
          return success();
        };
        for (const auto &port : partition->captures)
          if (!port.local && failed(extra(port))) return failure();
        for (const auto &port : partition->exports)
          if (failed(extra(port))) return failure();
      }
      if ((context.managesChecks() || context.hasPhysicalChecks())) {
        auto managedConnection = [&](StringRef port, StringRef signal) {
          auto id = kind.empty() ? context.rtlProtocolName(port) : port.str();
          out << (first ? "\n" : ",\n") << "    ." << id << "(" << signal
              << ")";
          first = false;
        };
        if (!context.isPhysical())
          managedConnection("pyc_phase", "pyc_phase");
        managedConnection("pyc_root_commit_ok", context.rtlProtocolName("pyc_root_commit_ok"));
        if (kind.empty()) {
          managedConnection("pyc_reset_active", context.rtlProtocolName("pyc_reset_active"));
          if (!context.isPhysical())
            managedConnection("pyc_check_complete",
                              collection ? childComplete + "[" + i + "]"
                                         : childComplete);
          if (!context.isPhysical())
            managedConnection("pyc_sampling_error",
                              collection ? childSamplingError + "[" + i + "]"
                                         : childSamplingError);
        }
        managedConnection("pyc_local_error",
                          collection ? childError + "[" + i + "]" : childError);
      }
      out << (first ? ");\n" : "\n  );\n");
      if (collection)
        out << "  end\n";
    }
    return success();
  }

  void emitAggregateError() {
    if (context.isSynthesis() || (context.isPhysical() && !context.hasPhysicalChecks())) return;
    if (context.isPhysical()) {
      if (!readableClock.empty() || !readableErrors.empty()) {
        out << "\n  // Simulation checks and whole-root update permission.\n"
            << "  generate if (1) begin : __checks\n";
        if (!readableClock.empty())
          out << "    function automatic logic allow_update(input logic sampled_clock);\n"
              << "`ifndef SYNTHESIS\n      allow_update = (sampled_clock === 1'b1) && ("
              << context.rtlProtocolName("pyc_root_commit_ok") << " === 1'b1);\n"
              << "`else\n      allow_update = (" << context.rtlProtocolName("pyc_root_commit_ok")
              << " === 1'b1);\n`endif\n    endfunction\n";
        out << "`ifndef SYNTHESIS\n";
        for (const auto &[name, expression] : readableErrors)
          out << "    wire " << name << " = " << expression << ";\n";
        out << "`else\n";
        for (const auto &[name, expression] : readableErrors)
          out << "    wire " << name << " = 1'b0;\n";
        out << "`endif\n  end endgenerate\n";
      }
      out << "  assign " << context.rtlProtocolName("pyc_local_error") << " = "
          << (localErrors.empty() ? "1'b0" : join(localErrors, " | ")) << ";\n";
      return;
    }
    if (!context.managesChecks())
      return;
    out << "  assign pyc_check_complete = "
        << (localCompletions.empty() ? "1'b1" : join(localCompletions, " & "))
        << ";\n"
        << "  assign pyc_sampling_error = "
        << (localSamplingErrors.empty() ? "1'b0"
                                        : join(localSamplingErrors, " | "))
        << ";\n";
    out << "  assign pyc_local_error = ";
    out << "(pyc_check_complete !== 1'b1) | pyc_sampling_error";
    if (!localErrors.empty())
      out << " | " << join(localErrors, " | ");
    out << ";\n";
  }
  void recordSourceNames() {
    uint64_t ordinal = 0;
    llvm::DenseMap<Value, uint64_t> ids;
    auto ordered = readableOrderedValues();
    auto emittedModule = ownership ? ownership->moduleName : context.names(definition).rtl;
    for (auto [index, value] : llvm::enumerate(ordered)) ids.try_emplace(value, index);
    auto record = [&](Value value) {
      uint64_t id = ordinal++;
      auto found = names.find(value);
      if (found == names.end()) return;
      for (const auto &binding : ac::sourceValueNames(value)) {
        std::string site, type;
        llvm::raw_string_ostream siteStream(site), typeStream(type);
        binding.site.print(siteStream);
        value.getType().print(typeStream);
        siteStream.flush();
        typeStream.flush();
        context.rtlSourceNames.push_back({emittedModule,
            binding.name.getValue().str(), binding.scope.getValue().str(),
            site, found->second, type, id});
      }
    };
    for (Value value : ordered) record(value);
    llvm::json::Array values, allocations, controlViews, factProofs, interfaceInputs, interfaceOutputs, nonvalueUses;
    definition.walk([&](Operation *operation) {
      if (operation->getNumResults() ||
          (isa<ac::YieldOp>(operation) && isa<ac::RuleOp>(operation->getParentOp()))) return;
      for (auto [index, input] : llvm::enumerate(operation->getOperands())) {
        auto value = rtlOwnershipSource(input, &context);
        if (ids.count(value)) nonvalueUses.emplace_back(llvm::json::Object{
            {"opcode", operation->getName().getStringRef().str()}, {"operand", index}, {"value", ids.lookup(value)}});
      }
    });
    // Proof IDs are local to this finite control view, with an explicit link
    // to optimized_value when available. Include conservative frontier atoms
    // even when a bounded analysis did not cache them or ownership forwarded
    // them outside the module's ordinary navigation table.
    SmallVector<Value> controlValues;
    llvm::DenseMap<Value, uint64_t> controlIds;
    auto appendControl = [&](Value value) {
      if (value && !controlIds.count(value)) {
        controlIds[value] = controlValues.size();
        controlValues.push_back(value);
      }
    };
    for (Value value : ordered)
      if (readableControlViews.contains(value)) appendControl(value);
    for (const auto &proof : readableFactProofs) {
      appendControl(proof.selector);
      for (auto [value, truth] : proof.facts) appendControl(readableSource(value));
      for (auto [value, truth] : proof.assumptions) appendControl(readableSource(value));
    }
    for (unsigned index = 0; index < controlValues.size(); ++index) {
      Value value = controlValues[index];
      if (auto found = readableControlViews.find(value); found != readableControlViews.end()) appendControl(found->second.value);
      if (auto *operation = value.getDefiningOp()) {
        auto operands = operation->getOperands();
        if (isa<ac::ValueRequireOp>(operation)) operands = operands.drop_front();
        for (Value input : operands)
          if (readableWidth(input) == 1) appendControl(readableSource(input));
      }
    }
    for (Value value : controlValues) {
      auto found = readableControlViews.find(value);
      auto view = found == readableControlViews.end() ? ReadableControlView{value} : found->second;
      auto *operation = value.getDefiningOp();
      std::string opcode = "atom";
      if (found != readableControlViews.end()) {
        if (auto literal = readableLiteral(value)) opcode = "literal:" + *literal;
        else {
          if (auto binary = dyn_cast_or_null<ac::BitsBinaryOp>(operation))
            if (llvm::is_contained(ArrayRef<StringRef>{"and", "or", "xor"}, binary.getOpcode())) opcode = binary.getOpcode().str();
          if (auto unary = dyn_cast_or_null<ac::BitsUnaryOp>(operation))
            if (unary.getOpcode() == "not") opcode = "not";
          if (auto compare = dyn_cast_or_null<ac::BitsCompareOp>(operation)) opcode = "compare:" + compare.getPredicate().str();
          if (isa_and_nonnull<ac::BitsSelectOp>(operation)) opcode = "select";
          if (isa_and_nonnull<ac::ValueRequireOp>(operation)) opcode = "require";
        }
      }
      llvm::json::Array inputs;
      bool complete = true;
      if (operation && opcode != "atom" && !StringRef(opcode).starts_with("literal:")) {
        auto operands = operation->getOperands();
        if (opcode == "require") operands = operands.drop_front();
        for (Value input : operands) {
          auto source = readableSource(input);
          if (!controlIds.count(source)) { complete = false; break; }
          inputs.emplace_back(controlIds.lookup(source));
        }
      }
      controlViews.emplace_back(llvm::json::Object{
          {"value", controlIds.lookup(value)},
          {"optimized_value", ids.count(value) ? llvm::json::Value(ids.lookup(value)) : llvm::json::Value(nullptr)},
          {"domain", view.domain},
          {"uses", readableControlUses.lookup(view.value)},
          {"target", controlIds.count(view.value) ? llvm::json::Value(controlIds.lookup(view.value)) : llvm::json::Value(nullptr)},
          {"literal", view.literal < 4 ? llvm::json::Value(view.literal) : llvm::json::Value(nullptr)},
          {"operation", opcode}, {"complete", complete}, {"inputs", std::move(inputs)}});
    }
    for (const auto &proof : readableFactProofs) {
      auto assignments = [&](const auto &entries) {
        llvm::json::Array result;
        SmallVector<std::pair<uint64_t, bool>> ordered;
        for (auto [value, truth] : entries) ordered.emplace_back(controlIds.lookup(readableSource(value)), truth);
        llvm::sort(ordered);
        for (auto [value, truth] : ordered)
          result.emplace_back(llvm::json::Object{{"value", value}, {"truth", truth}});
        return result;
      };
      factProofs.emplace_back(llvm::json::Object{{"selector", controlIds.lookup(proof.selector)},
          {"domain", proof.domain}, {"facts", assignments(proof.facts)}, {"assumptions", assignments(proof.assumptions)}});
    }
    for (auto [index, raw] : llvm::enumerate(definition.getInputNames())) {
      auto original = cast<StringAttr>(raw).getValue();
      auto spelling = context.rtlPortName(definition, original);
      if (failed(spelling)) continue;
      interfaceInputs.emplace_back(llvm::json::Object{{"ordinal", index}, {"source_port", original.str()},
          {"original_value", context.rtlOriginalValueIds.lookup(definition.getBody().front().getArgument(index))},
          {"rtl_port", *spelling}, {"omitted", context.rtlOmittedInput(definition, index)}});
    }
    for (auto [index, raw] : llvm::enumerate(definition.getOutputNames())) {
      auto original = cast<StringAttr>(raw).getValue();
      auto spelling = context.rtlPortName(definition, original);
      if (failed(spelling)) continue;
      auto projection = context.rtlOutputProjection(definition, index);
      auto canonical = rtlOwnershipSource(cast<ac::YieldOp>(definition.getBody().front().back()).getValues()[index], &context);
      auto forwarded = context.rtlForwardedInput(definition, index);
      llvm::json::Array fields;
      if (projection) for (const auto &field : projection->fields) fields.emplace_back(field);
      interfaceOutputs.emplace_back(llvm::json::Object{{"ordinal", index}, {"source_port", original.str()},
          {"original_canonical", context.rtlOriginalValueIds.lookup(canonical)},
          {"rtl_port", *spelling}, {"omitted", context.rtlOmittedOutput(definition, index)},
          {"canonical_value", ids.count(canonical) ? llvm::json::Value(ids.lookup(canonical)) : llvm::json::Value(nullptr)},
          {"forwarded_input", forwarded ? llvm::json::Value(*forwarded) : llvm::json::Value(nullptr)},
          {"projection_output", projection ? llvm::json::Value(projection->output) : llvm::json::Value(nullptr)},
          {"projection_fields", std::move(fields)}});
    }
    for (Value value : ordered) {
      auto rendered = names.find(value);
      std::string type, location;
      llvm::raw_string_ostream typeOut(type), locOut(location);
      value.getType().print(typeOut);
      ac::sourceIdentityLocation(value.getLoc()).print(locOut);
      auto *producer = value.getDefiningOp();
      llvm::json::Array operands;
      llvm::json::Array originalOperands;
      if (producer)
        for (Value input : producer->getOperands()) originalOperands.emplace_back(context.rtlOriginalValueIds.lookup(input));
      bool foreign = ownership && value.getParentRegion()->getParentOp()->getParentOfType<ac::ModuleOp>() != definition &&
          value.getParentRegion()->getParentOp() != definition;
      if (auto alias = ownershipAliases.find(value); alias != ownershipAliases.end()) {
        if (ids.count(alias->second)) operands.emplace_back(ids.lookup(alias->second));
      } else if (producer && !ownershipOpaque.contains(value))
        for (Value input : producer->getOperands())
          if (auto found = ids.find(foreign ? rtlOwnershipSource(input) : input); found != ids.end()) operands.emplace_back(found->second);
      auto *parent = value.getParentRegion()->getParentOp();
      auto origin = dyn_cast<ac::ModuleOp>(parent);
      if (!origin) origin = parent->getParentOfType<ac::ModuleOp>();
      llvm::json::Array roles;
      for (auto role : ac::sourceRtlRoles(value)) roles.push_back(readableRoleJson(role));
      llvm::json::Array recordFields;
      if (auto create = dyn_cast_or_null<ac::StructCreateOp>(producer)) {
        auto declaration = context.analysis.lookupStruct(cast<ac::StructType>(value.getType()));
        if (declaration)
          for (auto [field, input] : llvm::enumerate(create->getOperands())) {
            auto canonical = rtlOwnershipSource(input, &context);
            if (ids.count(canonical)) recordFields.emplace_back(llvm::json::Object{
                {"name", cast<DictionaryAttr>(declaration.getFields()[field]).getAs<StringAttr>("name").getValue().str()},
                {"value", ids.lookup(canonical)}});
          }
      }
      auto canonical = rtlOwnershipSource(value, &context);
      values.emplace_back(llvm::json::Object{
          {"optimized_value", ids.lookup(value)}, {"rtl_scope", readableLaneScopes.lookup(value)},
          {"original_value", context.rtlOriginalValueIds.lookup(value)},
          {"original_operands", std::move(originalOperands)},
          {"original_canonical", context.rtlOriginalValueIds.lookup(canonical)},
          {"canonical_value", ids.count(canonical) ? llvm::json::Value(ids.lookup(canonical)) : llvm::json::Value(nullptr)},
          {"record_fields", std::move(recordFields)},
          {"field", isa_and_nonnull<ac::StructGetOp>(producer) ? llvm::json::Value(cast<ac::StructGetOp>(producer).getField().str()) : llvm::json::Value(nullptr)},
          {"rtl_expression", rendered == names.end() ? llvm::json::Value(nullptr) : llvm::json::Value(rendered->second)},
          {"opcode", producer ? producer->getName().getStringRef().str() : "input"},
          {"source_module", origin ? origin.getSymName().str() : ""},
          {"source_roles", std::move(roles)},
          {"type", typeOut.str()}, {"location", locOut.str()}, {"operands", std::move(operands)}});
    }
    for (Operation &operation : definition.getBody().front()) {
      if (!isa<ac::InstanceOp, ac::CollectionOp>(operation)) continue;
      auto *callee = isa<ac::InstanceOp>(operation)
          ? context.analysis.resolveCallee(cast<ac::InstanceOp>(operation))
          : context.analysis.resolveCallee(cast<ac::CollectionOp>(operation));
      auto kind = context.analysis.getPrimitiveKind(callee);
      auto raw = operation.getAttrOfType<StringAttr>("instance_name");
      llvm::json::Array inputs, outputs;
      for (Value input : operation.getOperands()) inputs.emplace_back(ids.lookup(input));
      for (Value output : operation.getResults()) outputs.emplace_back(ids.lookup(output));
      auto spelling = readableInstanceNames.find(&operation);
      std::string rendered = spelling == readableInstanceNames.end() ? "" : spelling->second;
      if (isReadableRegister(&operation) && operation.getNumResults())
        rendered = names.lookup(operation.getResult(0));
      allocations.emplace_back(llvm::json::Object{
          {"source_name", raw.getValue().str()}, {"rtl_name", rendered},
          {"rtl_callee", kind.empty() ?
              (isa<ac::InstanceOp>(operation) && context.rtlPartition(cast<ac::InstanceOp>(operation), ownership) ?
                context.rtlPartition(cast<ac::InstanceOp>(operation), ownership)->moduleName : context.names(callee).rtl) : kind.str()},
          {"callee", callee->getAttrOfType<StringAttr>("sym_name").getValue().str()},
          {"primitive", kind.str()}, {"inlined_storage", isReadableRegister(&operation)},
          {"inputs", std::move(inputs)}, {"outputs", std::move(outputs)}});
    }
    llvm::json::Object transport;
    if (ownership) {
      llvm::json::Array captures, exports, aliases, replaced, placements, staticParameters;
      for (const auto &port : ownership->captures)
        captures.emplace_back(llvm::json::Object{{"value", context.rtlOriginalValueIds.lookup(port.value)},
            {"local", port.local ? llvm::json::Value(context.rtlOriginalValueIds.lookup(port.local)) : llvm::json::Value(nullptr)},
            {"port", port.name}});
      for (const auto &port : ownership->exports)
        exports.emplace_back(llvm::json::Object{{"value", context.rtlOriginalValueIds.lookup(port.value)}, {"port", port.name}});
      for (auto *operation : ownership->operations) {
        llvm::json::Array results;
        for (Value value : operation->getResults()) results.emplace_back(context.rtlOriginalValueIds.lookup(value));
        placements.push_back(std::move(results));
      }
      SmallVector<std::pair<uint64_t, uint64_t>> originalAliases;
      for (auto [value, source] : ownership->aliases)
        originalAliases.emplace_back(context.rtlOriginalValueIds.lookup(value), context.rtlOriginalValueIds.lookup(source));
      llvm::sort(originalAliases);
      for (auto [value, source] : originalAliases) aliases.emplace_back(llvm::json::Object{{"value", value}, {"source", source}});
      SmallVector<std::pair<unsigned, uint64_t>> originalInputs;
      for (auto [index, source] : ownership->replacedInputs) originalInputs.emplace_back(index, context.rtlOriginalValueIds.lookup(source));
      llvm::sort(originalInputs);
      for (auto [index, source] : originalInputs) replaced.emplace_back(llvm::json::Object{{"input", index}, {"source", source}});
      for (const auto &parameter : ownership->parameters)
        staticParameters.emplace_back(llvm::json::Object{{"owner", SymbolTable::getSymbolName(parameter.owner).getValue().str()},
            {"name", parameter.name.getValue().str()}, {"alias", parameter.alias}, {"type", parameter.type}});
      transport = llvm::json::Object{{"parent_rtl_module", ownership->parent ? ownership->parent->moduleName : context.names(ownership->caller).rtl},
          {"allocation", ownership->allocation->getAttrOfType<StringAttr>("instance_name").getValue().str()},
          {"captures", std::move(captures)}, {"exports", std::move(exports)}, {"aliases", std::move(aliases)},
          {"replaced_inputs", std::move(replaced)}, {"placements", std::move(placements)}, {"parameters", std::move(staticParameters)}};
    }
    auto rootKind = definition->getAttrOfType<StringAttr>("ac.root_kind");
    auto interfaceLayout = ac::getModulePortLayout(definition);
    context.rtlModules.emplace_back(llvm::json::Object{
        {"source_symbol", definition.getSymName().str()}, {"rtl_module", emittedModule},
        {"partitioned_operations", ownership ? ownership->operations.size() : 0},
        {"ownership_transport", std::move(transport)},
        {"rtl_file", context.names(definition).verilog},
        {"kind", rootKind && rootKind.getValue() == "system" ? "system_harness" : "hardware_module"},
        {"values", std::move(values)}, {"allocations", std::move(allocations)},
        {"control_views", std::move(controlViews)}, {"fact_proofs", std::move(factProofs)},
        {"nonvalue_uses", std::move(nonvalueUses)},
        {"interface", llvm::json::Object{
          {"source_inputs", succeeded(interfaceLayout) ? llvm::json::Value(interfaceLayout->sourceInputCount) : llvm::json::Value(nullptr)},
          {"source_outputs", succeeded(interfaceLayout) ? llvm::json::Value(interfaceLayout->sourceOutputCount) : llvm::json::Value(nullptr)},
          {"inputs", std::move(interfaceInputs)}, {"outputs", std::move(interfaceOutputs)}}}});
  }

private:
  HardwareEmitContext &context;
  ac::ModuleOp definition;
  ReadableRtlSections readableSections;
  raw_ostream &out;
  llvm::DenseMap<Value, std::string> names;
  llvm::DenseMap<Value, std::string> readableLaneScopes;
  llvm::DenseMap<Value, std::string> readableRoleHints;
  llvm::StringSet<> readableAmbiguousBindings;
  llvm::StringSet<> readableAuthoredNames;
  llvm::DenseMap<Value, llvm::StringSet<>> readablePurposes;
  llvm::DenseMap<Value, uint64_t> readableValueOrdinals;
  const RtlOwnershipPartition *ownership;
  llvm::DenseMap<Value, Value> ownershipAliases;
  llvm::DenseSet<Value> ownershipOpaque;
  llvm::DenseMap<Value, std::string> initializers;
  llvm::DenseMap<Value, std::string> readableInlineExpressions;
  llvm::DenseMap<Value, unsigned> readableInlineCosts;
  llvm::StringSet<> readableNames;
  llvm::DenseMap<Operation *, std::string> readableInstanceNames;
  llvm::DenseMap<std::pair<Value, unsigned>, std::string> readableBitNames;
  llvm::DenseMap<Value, ReadableControlView> readableControlViews;
  llvm::DenseMap<Value, unsigned> readableControlUses;
  SmallVector<ReadableFactProof> readableFactProofs;
  llvm::DenseSet<Value> readableEndpointValues;
  SmallVector<ReadableInstanceArray> readableInstanceArrays;
  llvm::DenseMap<Operation *, std::pair<unsigned, unsigned>> readableInstanceArrayLanes;
  SmallVector<std::pair<std::string, std::string>> readableErrors;
  std::string readableClock;
  llvm::DenseSet<Value> readablePending, readableRetained;
  llvm::DenseSet<Value> readableBypassedResults;
  llvm::DenseSet<Operation *> instances;
  llvm::DenseMap<uint64_t, std::string> samplingNames;
  SmallVector<std::string> localErrors;
  SmallVector<std::string> localCompletions;
  SmallVector<std::string> localSamplingErrors;
  unsigned next = 0;
};
} // namespace
LogicalResult emitHardwareVerilogDefinition(HardwareEmitContext &context,
                                            ac::ModuleOp definition,
                                            raw_ostream &out,
                                            const RtlOwnershipPartition *partition) {
  auto previousScope = context.rtlScope;
  context.rtlScope = partition;
  auto restoreScope = llvm::scope_exit([&] { context.rtlScope = previousScope; });
  auto &names = context.names(definition);
  out << "module " << (partition ? partition->moduleName : names.rtl);
  SmallVector<std::string> parameters;
  for (auto raw : definition.getParameters()) {
    auto formal = cast<DictionaryAttr>(raw);
    auto name = formal.getAs<StringAttr>("name");
    auto id = context.rtlFormalName(name.getValue(), definition);
    if (failed(id))
      return failure();
    std::string text = "parameter longint signed " + *id;
    if (auto value = formal.getAs<ac::StaticExprAttr>("default")) {
      auto rendered = context.staticRtlValue(value, definition);
      if (failed(rendered))
        return failure();
      text += " = " + *rendered;
    } else
      text += " = 1";
    parameters.push_back(text);
  }
  for (auto raw : definition.getTypeParameters()) {
    auto id =
        context.rtlFormalName(cast<StringAttr>(raw).getValue(), definition);
    if (failed(id))
      return failure();
    parameters.push_back("parameter type " + *id + " = logic [0:0]");
  }
  if (partition)
    for (const auto &parameter : partition->parameters)
      parameters.push_back(std::string(parameter.type ? "parameter type " : "parameter longint signed ") +
          parameter.alias + (parameter.type ? " = logic [0:0]" : " = 1"));
  if (!parameters.empty())
    out << " #(\n" << join(parameters, ",\n") << "\n)";
  out << " (";
  bool first = true;
  auto emitPort = [&](StringRef direction, Type type,
                      StringRef name) -> LogicalResult {
    auto rendered = context.rtlType(type, definition);
    if (failed(rendered))
      return failure();
    auto id = context.rtlPortName(definition, name);
    if (failed(id))
      return failure();
    out << (first ? "\n" : ",\n") << "  " << direction << " wire " << *rendered
        << " " << *id;
    first = false;
    return success();
  };
  auto signature = definition.getFunctionType();
  for (auto [i, type] : llvm::enumerate(signature.getInputs()))
    if (!(partition && partition->replacedInputs.count(i)) && !context.rtlOmittedInput(definition, i) && failed(emitPort(
            "input", type,
            cast<StringAttr>(definition.getInputNames()[i]).getValue())))
      return failure();
  for (auto [i, type] : llvm::enumerate(signature.getResults()))
    if (!context.rtlForwardedInput(definition, i) && !context.rtlOmittedOutput(definition, i) && failed(emitPort(
            "output", type,
            cast<StringAttr>(definition.getOutputNames()[i]).getValue())))
      return failure();
  if (partition) {
    auto extra = [&](StringRef direction, const RtlOwnershipPort &port) -> LogicalResult {
      auto type = context.rtlType(port.value.getType(), definition);
      if (failed(type)) return failure();
      out << (first ? "\n" : ",\n") << "  " << direction << " wire " << *type << " " << port.name;
      first = false;
      return success();
    };
    for (const auto &port : partition->captures)
      if (!port.local && failed(extra("input", port))) return failure();
    for (const auto &port : partition->exports)
      if (failed(extra("output", port))) return failure();
  }
  if (context.managesChecks()) {
    out << (first ? "\n" : ",\n")
        << "  input wire [2:0] pyc_phase,\n"
           "  input wire pyc_root_commit_ok,\n"
           "  input wire pyc_reset_active,\n"
           "  output wire pyc_check_complete,\n"
           "  output wire pyc_sampling_error,\n"
           "  output wire pyc_local_error";
    first = false;
  }
  if (context.hasPhysicalChecks()) {
    out << (first ? "\n" : ",\n")
        << "  input wire __checks_allow,\n"
           "  input wire __checks_reset,\n"
           "  output wire __checks_error";
    first = false;
  }
  out << (first ? ");\n" : "\n);\n");
  NetEmitter nets(context, definition, out, partition);
  if (failed(nets.initializeOwnership())) return failure();
  auto yield = cast<ac::YieldOp>(definition.getBody().front().back());
  for (auto [i, value] : llvm::enumerate(yield.getValues())) {
    if (context.rtlForwardedInput(definition, i) || context.rtlOmittedOutput(definition, i)) continue;
    auto wire = nets.net(value);
    if (failed(wire))
      return failure();
    auto id = context.rtlPortName(
        definition, cast<StringAttr>(definition.getOutputNames()[i]).getValue());
    if (failed(id))
      return failure();
    nets.emitPortAssignment(*id, *wire);
  }
  if (partition)
    for (const auto &port : partition->exports) {
      auto source = nets.net(port.value);
      if (failed(source)) return failure();
      nets.emitPortAssignment(port.name, *source);
    }
  if (failed(nets.emitSourceChecks()))
    return failure();
  if (failed(nets.emitObservations()))
    return failure();
  if (failed(nets.emitInstances()))
    return failure();
  nets.emitAggregateError();
  nets.recordSourceNames();
  nets.finishReadableLayout();
  out << "endmodule\n";
  return success();
}
} // namespace acir::compiler
