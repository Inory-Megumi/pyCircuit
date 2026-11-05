#include "FinalCppNames.h"
#include "HardwareEmitCommon.h"
#include "RtlPresentationPlan.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSwitch.h"
using namespace mlir;
namespace acir::compiler {
namespace {
class NetEmitter {
public:
  NetEmitter(HardwareEmitContext &context, ac::ModuleOp definition,
             raw_ostream &out)
      : context(context), definition(definition), out(out) {}
  LogicalResult preparePresentation() {
    if (!context.isPhysical()) return success();
    presentation = std::make_unique<RtlPresentationPlan>(context, definition);
    return presentation->prepare();
  }
  void finishPresentation(raw_ostream &target, llvm::json::Array *mapping) {
    if (!presentation) return;
    presentation->emit(target);
    if (mapping) mapping->push_back(presentation->mapping());
  }
  std::string netName(Value value) {
    return presentation ? presentation->get(value).name
                        : "pyc_net_" + std::to_string(next++);
  }
  std::string generated(StringRef role) {
    return context.isPhysical() ? context.rtlGeneratedName(definition, role, role)
                                : "pyc_" + role.str();
  }
  FailureOr<std::string> physicalReset() {
    if (auto domain = definition->getAttrOfType<DictionaryAttr>("ac.domain_inputs")) {
      if (auto ordinal = domain.getAs<IntegerAttr>("reset")) {
        auto signal = context.rtlPortName(definition, false, ordinal.getValue().getZExtValue());
        if (failed(signal)) return failure();
        return context.rtlReset(*signal);
      }
    }
    for (const auto &binding : context.sourceChecks().samplingBindings) {
      if (binding.definition != definition) continue;
      auto signal = net(binding.reset);
      if (failed(signal)) return failure();
      return context.rtlReset(*signal);
    }
    return definition.emitOpError() << "physical source checks require a local verified reset value";
  }
  void declareNet(Value value, StringRef type, StringRef name, bool variable = false) {
    auto rendered = variable ? FailureOr<std::string>(type.str())
                             : context.rtlWireType(value.getType(), definition);
    assert(succeeded(rendered) && "previously rendered RTL type");
    auto text = "  " + *rendered + " " + name.str() + ";\n";
    if (presentation) {
      if (presentation->get(value).local) out << text;
      else presentation->declare(text);
      presentation->record(value, name, "signal");
    } else out << text;
  }
  FailureOr<std::string> physicalInitializer(Value value, StringRef hint = {}, unsigned depth = 0) {
    auto source = value;
    if (presentation) value = presentation->canonical(value);
    auto known = initializers.find(value);
    if (known != initializers.end()) {
      if (presentation) presentation->recordInitializer(source, known->second);
      return known->second;
    }
    auto *op = value.getDefiningOp();
    if (!op || depth > 256)
      return definition.emitOpError()
             << "physical initializer has no bounded constant DAG";
    SmallVector<std::string> operands;
    for (Value operand : op->getOperands()) {
      auto rendered = physicalInitializer(operand, {}, depth + 1);
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
        auto bits = cast<ac::BitsType>(constant.getResult().getType());
        if (context.isClosedStatic(bits.getWidth()) && !value.isNegative()) {
          expression = *width + "'d" + *literal;
        }
        *literal = std::to_string(std::max(1u, value.getActiveBits())) + "'d" +
                   *literal;
      }
      if (expression.empty()) expression = "(" + *width + ")'(" + *literal + ")";
    } else if (auto create = dyn_cast<ac::EnumCreateOp>(op)) {
      auto enumeration =
          context.analysis.resolveEnum(create.getResult().getType(), op);
      if (failed(enumeration))
        return failure();
      for (const auto &member : enumeration->members)
        if (member.name == create.getMemberAttr())
          expression = std::to_string(enumeration->width) + "'d" +
                       member.code.getCanonicalValue().str();
    } else if (isa<ac::StructCreateOp, ac::TableCreateOp>(op)) {
      expression = "{" + join(operands, ", ") + "}";
    } else if (auto splat = dyn_cast<ac::TableSplatOp>(op)) {
      auto count = context.shapeSize(splat.getShape(), op, true);
      if (failed(count))
        return failure();
      expression = "{(" + *count + "){" + operands[0] + "}}";
    } else if (auto get = dyn_cast<ac::StructGetOp>(op)) {
      auto field =
          legalizeIdentifier(get.getField(), [&] { return op->emitOpError(); });
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
      auto inputWidth = context.payloadWidth(extract.getInput().getType(), op, true);
      if (failed(inputWidth)) return failure();
      expression = *low == "0" && *inputWidth == *width ? operands[0]
          : operands[0] + "[(" + *low + ") +: (" + *width + ")]";
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
    auto label = context.rtlIdentifier(hint.empty() ? "initial_" + std::to_string(initializers.size()) : hint.str(), op);
    if (failed(label)) return failure();
    auto name = context.rtlGeneratedName(definition, "initializer:" + std::to_string(initializers.size()), *label);
    out << "  localparam " << *type << " " << name << " = " << expression
        << ";\n";
    initializers.try_emplace(value, name);
    if (presentation) presentation->recordInitializer(source, name);
    return name;
  }
  LogicalResult emitSourceChecks() {
    if (context.isPhysical()) {
      llvm::raw_string_ostream checks(physicalChecks);
      for (auto [ordinal, binding] : llvm::enumerate(context.sourceChecks().bindings)) {
        if (binding.definition != definition)
          continue;
        const auto &plan = presentation->check(ordinal);
        if (!plan.needed()) continue;
        SmallVector<std::string> terms;
        std::string path;
        if (plan.pathUnknown || (plan.conditionUnknown && !plan.pathAlwaysOne)) {
          auto signal = net(plan.path);
          if (failed(signal)) return failure();
          path = *signal;
        }
        if (plan.pathUnknown) terms.push_back("$isunknown(" + path + ")");
        if (plan.conditionUnknown) {
          auto condition = net(plan.condition), reset = physicalReset();
          if (failed(condition) || failed(reset)) return failure();
          terms.push_back("((" + *reset + " === 1'b0) && " +
              (plan.pathAlwaysOne ? "" : "(" + path + " === 1'b1) && ") + "$isunknown(" + *condition + "))");
        }
        auto name = generated("check_error_" + std::to_string(localErrors.size()));
        checks << "    wire " << name << " = " << join(terms, " || ") << ";\n";
        localErrors.push_back(name);
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
  FailureOr<std::string> net(Value value) {
    if (presentation) value = presentation->canonical(value);
    if (auto found = names.find(value); found != names.end()) {
      if (presentation && presentation->get(value).disposition.empty())
        presentation->record(value, found->second, "region-port");
      return found->second;
    }
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      auto *parent = argument.getOwner()->getParentOp();
      if (parent == definition) {
        auto id = context.rtlPortName(definition, false, argument.getArgNumber());
        if (failed(id))
          return failure();
        names.try_emplace(value, *id);
        if (presentation) presentation->record(value, *id, "port");
        return *id;
      }
      if (auto rule = dyn_cast<ac::RuleOp>(parent))
        return net(rule.getCaptures()[argument.getArgNumber()]);
      return definition.emitOpError() << "unexpected RTL block argument";
    }
    auto *op = value.getDefiningOp();
    if (!op)
      return definition.emitOpError() << "RTL wire has no producer";
    if (isa<ac::InstanceOp, ac::CollectionOp>(op)) {
      auto name = netName(value);
      auto type = context.rtlType(value.getType(), op);
      if (failed(type))
        return failure();
      declareNet(value, *type, name);
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
      if (failed(tableOperation(op)))
        return failure();
      return names.lookup(value);
    }
    // Register the complete net before following producers. A legal
    // field-level graph can refer to another field of this same aggregate.
    auto name = netName(value);
    auto type = context.rtlType(value.getType(), op);
    if (failed(type))
      return failure();
    bool combinationalDivRem = false;
    if (auto binary = dyn_cast<ac::BitsBinaryOp>(op))
      combinationalDivRem =
          binary.getOpcode() == "udiv" || binary.getOpcode() == "urem";
    bool inlineValue = presentation && presentation->get(value).inlineValue;
    if (!inlineValue) {
      declareNet(value, *type, name, combinationalDivRem);
      names.try_emplace(value, name);
    }
    auto finish = [&](std::string expression) -> FailureOr<std::string> {
      if (inlineValue) {
        // A removed wire's width and unsignedness remain expression boundaries.
        auto &node = presentation->get(value);
        if (!node.literal && !node.replacement && !isa<ac::BitsCompareOp>(op)) {
          auto width = context.payloadWidth(value.getType(), op, true);
          if (failed(width)) return failure();
          expression = "$unsigned((" + *width + ")'(" + expression + "))";
        }
        names.try_emplace(value, expression);
        presentation->record(value, expression, "inline");
        return expression;
      }
      auto statement = "  " + std::string(combinationalDivRem ? "always_comb " : "assign ") + name
          + " = " + expression + ";\n";
      if (presentation && !presentation->get(value).local) presentation->statement(value, statement);
      else out << statement;
      return name;
    };
    if (presentation) {
      auto &node = presentation->get(value);
      if (node.constant < 4) return finish(std::string("1'b") + "01xz"[node.constant]);
      if (node.replacement) {
        auto rendered = net(node.replacement);
        if (failed(rendered)) return failure();
        return finish(*rendered);
      }
    }
    SmallVector<std::string> operands;
    auto runtimeOperands = op->getOperands();
    if (isa<ac::ValueRequireOp>(op))
      runtimeOperands = runtimeOperands.drop_front();
    if (presentation && isa<ac::DWireOp>(op)) {
      runtimeOperands = runtimeOperands.drop_front(2);
      operands.append({"", ""});
    }
    for (auto input : runtimeOperands) {
      auto item = net(input);
      if (failed(item))
        return failure();
      operands.push_back(*item);
    }
    std::string expression;
    if (isa<ac::ValueRequireOp>(op))
      expression = "(" + operands[1] + " ? " + operands[0] + " : 1'b1)";
    else if (auto create = dyn_cast<ac::EnumCreateOp>(op)) {
      auto definition =
          context.analysis.resolveEnum(create.getResult().getType(), op);
      if (failed(definition))
        return failure();
      for (const auto &member : definition->members)
        if (member.name == create.getMemberAttr())
          expression = std::to_string(definition->width) + "'d" +
                       member.code.getCanonicalValue().str();
      if (expression.empty())
        return op->emitOpError()
               << "unresolved enum member during RTL emission";
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
          auto equal = "(" + operands[0] +
                       " == " + std::to_string(definition->width) + "'d" +
                       member.code.getCanonicalValue().str() + ")";
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
      auto decimal = [](StringRef value) {
        return !value.empty() && llvm::all_of(value, [](char c) { return c >= '0' && c <= '9'; });
      };
      if (presentation && decimal(*width) && decimal(*literal))
        return finish(*width + "'d" + *literal);
      if (context.isClosedStatic(constant.getValue())) {
        llvm::APSInt value(*literal);
        *literal = std::to_string(std::max(1u, value.getActiveBits())) + "'d" +
                   *literal;
      }
      expression = "(" + *width + ")'( " + *literal + " )";
    } else if (auto unary = dyn_cast<ac::BitsUnaryOp>(op)) {
      if (unary.getOpcode() != "not")
        return op->emitOpError() << "unsupported RTL unary op";
      expression = "(~" + operands[0] + ")";
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
      expression = "(" + operands[0] + (presentation ? "\n      ? " : " ? ") + operands[1]
          + (presentation ? "\n      : " : " : ") + operands[2] + ")";
    else if (isa<ac::DWireOp>(op))
      expression = "(" + operands[2] + " ? " + operands[3] + " : " + operands[4] + ")";
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
      expression = operands[0] + "[(" + *low + ") +: " + *width + "]";
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
          legalizeIdentifier(get.getField(), [&] { return op->emitOpError(); });
      if (failed(name))
        return failure();
      expression = operands[0] + "." + *name;
    } else
      return op->emitOpError() << "operation lacks RTL hardware emission";
    return finish(expression);
  }
  LogicalResult tableOperation(Operation *op) {
    for (Value result : op->getResults()) {
      auto type = context.rtlType(result.getType(), op);
      if (failed(type))
        return failure();
      auto name = netName(result);
      declareNet(result, *type, name);
      names.try_emplace(result, name);
    }
    SmallVector<std::string> operands;
    for (Value value : op->getOperands()) {
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
      auto n = count(type), w = width(type.getElementType());
      if (failed(n) || failed(w))
        return failure();
      return value.str() + "[((" + *n + ")-1-(" + ordinal.str() + "))*(" + *w +
             ") +: (" + *w + ")]";
    };
    auto generate = [&](StringRef n, StringRef label) {
      std::string i = generated("index_" + std::to_string(next++));
      out << "  for (genvar " << i << "=0; " << i << " < (" << n << "); ++" << i
          << ") begin : " << label << "\n";
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
      auto i = generate(*n, generated("broadcast_" + resultName()));
      out << "    assign " << resultName() << "[((" << *n << ")-1-" << i
          << ")*(" << *w << ") +: (" << *w << ")] = " << operands[0]
          << ";\n  end\n";
      return success();
    }
    if (auto view = dyn_cast<ac::TableViewOp>(op)) {
      auto srcType = cast<ac::TableType>(view.getInput().getType());
      auto dstType = cast<ac::TableType>(view.getResult().getType());
      auto n = count(dstType);
      if (failed(n))
        return failure();
      auto i = generate(*n, generated("view_" + resultName()));
      auto mapped = context.viewIndex(view, i, true);
      if (failed(mapped))
        return failure();
      auto src = element(operands[0], *mapped, srcType);
      auto dst = element(resultName(), i, dstType);
      if (failed(src) || failed(dst))
        return failure();
      out << "    assign " << *dst << " = " << *src << ";\n  end\n";
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
        auto boundWidth = "$clog2(64'(" + shape[axis] + ") + 64'd1)";
        auto compareWidth = "((" + widths[axis] + ") > (" + boundWidth +
                            ") ? (" + widths[axis] + ") : (" + boundWidth +
                            "))";
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
      auto b = "$clog2(64'(" + *n + ") + 64'd1)";
      auto w = "((" + *k + ") > (" + b + ") ? (" + *k + ") : (" + b + "))";
      auto selected = element(operands[0], "$unsigned(" + operands[1] + ")", type);
      if (failed(selected)) return failure();
      std::string range = "(" + w + ")'($unsigned(" + operands[1] + ")) < (" + w + ")'(" + *n + ")";
      if (isa<ac::TableGetOp>(op)) {
        out << "  assign " << resultName(1) << " = " << range << ";\n";
        range = resultName(1);
      }
      out << "  assign " << resultName() << " = (" << range << ") ? "
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
      auto i = generate(*n, generated("map_" + resultName()));
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
        auto selected = element(operands[j], i, type);
        auto dataType = context.rtlWireType(type.getElementType(), op);
        if (failed(selected) || failed(dataType))
          return failure();
        auto local = generated("lane_" + std::to_string(next++));
        out << "    " << *dataType << " " << local << " = " << *selected
            << ";\n";
        names[block.getArgument(arg++)] = local;
      }
      for (size_t j = tables.size(); j < operands.size(); ++j)
        names[block.getArgument(arg++)] = operands[j];
      auto yielded = cast<ac::YieldOp>(block.back()).getValues();
      for (auto [j, value] : llvm::enumerate(yielded)) {
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
      out << "  end\n";
      return success();
    }
    if (auto choose = dyn_cast<ac::TableChooseOp>(op)) {
      auto type = cast<ac::TableType>(choose.getInput().getType());
      auto n = count(type), w = width(choose.getResults().front().getType());
      if (failed(n) || failed(w))
        return failure();
      auto c = choose.getCount();
      auto prefix = generated("choice_" + resultName());
      auto member = [&](StringRef suffix) {
        auto hint = prefix + "_" + suffix.str();
        return context.isPhysical() ? generated(hint) : hint;
      };
      auto mask = member("mask"), index = member("index"), valid = member("valid");
      out << "  wire [(" << *n << ")-1:0] " << mask << " [0:" << c
          << "];\n"
          << "  wire [(" << *w << ")-1:0] " << index << " [0:" << c - 1
          << "][0:(" << *n << ")];\n"
          << "  wire " << valid << " [0:" << c - 1 << "];\n"
          << "  assign " << mask << "[0] = " << operands[1] << ";\n";
      auto pass = generate(std::to_string(c), member("passes"));
      out << "    assign " << index << "[" << pass << "][0] = '0;\n"
          << "    assign " << valid << "[" << pass << "] = |" << mask << "[" << pass << "];\n";
      auto step = generate(*n, member("scan"));
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
          << "  end\n  end\n";
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
      auto prefix = generated("fold_" + resultName());
      out << "  wire [(" << *n << ")*(" << *w << ")-1:0] " << prefix
          << " [0:$clog2(" << *n << ")];\n"
          << "  assign " << prefix << "[0] = " << operands[0] << ";\n";
      auto level = generate("$clog2(" + *n + ")", (context.isPhysical() ? generated(prefix + "_levels") : prefix + "_levels"));
      auto previousCount = "(((" + *n + ") + ((64'd1 << " + level +
                           ")-1)) / (64'd1 << " + level + "))";
      auto lane = generate("((" + previousCount + "+1)/2)", (context.isPhysical() ? generated(prefix + "_pairs") : prefix + "_pairs"));
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
          << ";\n    end\n  end\n  end\n"
          << "  assign " << resultName() << " = " << prefix << "[$clog2(" << *n
          << ")][((" << *n << ")-1)*(" << *w << ") +: (" << *w << ")];\n";
      return success();
    }
    if (auto merge = dyn_cast<ac::ValueMergeOp>(op)) {
      auto field = [&](StringRef base,
                       ArrayRef<StringAttr> path) -> FailureOr<std::string> {
        std::string text = base.str();
        for (auto item : path) {
          auto id = legalizeIdentifier(item.getValue(),
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
      out << "  assign " << resultName(1) << " = " << enables << ";\n";
      return success();
    }
    return op->emitOpError() << "table operation lacks RTL emission";
  }

  LogicalResult emitPhysicalStorage(Operation *occurrence, StringRef kind,
                                    const ac::HardwareBindings &bindings,
                                    ArrayRef<std::string> inputs,
                                    ArrayRef<std::string> outputs) {
    // The verified physical projection selects this backend for native storage.
    // It implements the physical branch of dff/dffe without importing their
    // managed-simulator ABI. Keep typed startup, reset priority and the common
    // commit barrier, including all four-state control/type checks.
    bool collection = isa<ac::CollectionOp>(occurrence);
    bool enabled = kind == "dffe";
    unsigned dataIndex = enabled ? 3 : 2, initialIndex = dataIndex + 1;
    auto owner = occurrence->getAttrOfType<StringAttr>("instance_name").getValue();
    auto initial = physicalInitializer(occurrence->getOperand(initialIndex), owner.str() + "_init");
    if (failed(initial)) return failure();
    auto label = context.rtlIdentifier("storage_" + owner.str(), occurrence);
    if (failed(label)) return failure();
    auto scope = context.rtlGeneratedName(definition, "storage:" + owner.str(), *label);
    auto error = generated("storage_error_" + std::to_string(localErrors.size()));
    llvm::raw_string_ostream checks(physicalChecks);
    std::string count, lane;
    if (collection) {
      auto size = context.shapeSize(cast<ac::CollectionOp>(occurrence).getShape(), occurrence, true);
      if (failed(size)) return failure();
      count = *size;
      lane = generated("instance_lane_" + std::to_string(next++));
      checks << "    wire [(" << count << ")-1:0] " << error << ";\n";
      localErrors.push_back("(|" + error + ")");
    } else {
      checks << "    wire " << error << ";\n";
      localErrors.push_back(error);
    }
    auto *callee = collection ? context.analysis.resolveCallee(cast<ac::CollectionOp>(occurrence))
                             : context.analysis.resolveCallee(cast<ac::InstanceOp>(occurrence));
    auto signature = cast<FunctionType>(callee->getAttrOfType<TypeAttr>("function_type").getValue());
    auto payload = context.analysis.resolveType(signature.getResult(0), bindings, occurrence);
    if (failed(payload)) return failure();
    auto type = context.rtlType(*payload, occurrence);
    if (failed(type)) return failure();
    auto select = [&](StringRef signal, Type portType) -> FailureOr<std::string> {
      if (!collection) return signal.str();
      auto width = context.payloadWidth(portType, occurrence, true, bindings);
      if (failed(width)) return failure();
      return signal.str() + "[((" + count + ")-1-" + lane + ")*(" + *width + ") +: (" + *width + ")]";
    };
    SmallVector<std::string> pins;
    for (auto [i, signal] : llvm::enumerate(inputs)) {
      auto pin = select(signal, signature.getInput(i));
      if (failed(pin)) return failure();
      pins.push_back(*pin);
    }
    auto q = select(outputs[0], signature.getResult(0));
    auto startup = select(*initial, signature.getInput(initialIndex));
    if (failed(q) || failed(startup)) return failure();
    auto clock = pins[0], reset = context.rtlReset(pins[1]);
    auto enable = enabled ? pins[2] : "1'b1";
    auto fault = context.rtlCheckName(definition, "checks") + "." + error;
    if (collection) fault += "[" + lane + "]";
    // Local storage/check declarations must not shadow incoming functional
    // signals referenced from the generate scope.
    auto local = [&](StringRef role) {
      return context.rtlGeneratedName(definition, "storage-local:" + role.str(), role);
    };
    auto payloadType = local("payload_t"), value = local("value");
    auto probe = local("check_payload"), payloadX = local("payload_x_check"), packedX = local("packed_x_check");
    if (presentation && !collection) {
      // Connect the verified source occurrence to the identifiers actually
      // emitted below. This is metadata only; it adds no functional ports.
      auto packedWidth = context.analysis.getPackedWidth(*payload, bindings, occurrence);
      if (failed(packedWidth)) return failure();
      std::string identity;
      llvm::raw_string_ostream identityStream(identity);
      if (auto key = occurrence->getAttr("occurrence")) key.print(identityStream);
      presentation->recordStorage(llvm::json::Object{
          {"owner", identity}, {"name", owner.str()}, {"kind", kind.str()},
          {"width", *packedWidth}, {"path", llvm::json::Array{scope, value}}});
    }
    if (collection)
      out << "  for (genvar " << lane << "=0; " << lane << " < (" << count
          << "); ++" << lane << ") begin : " << scope << "\n";
    else
      out << "  if (1) begin : " << scope << "\n";
    out << "    typedef " << *type << " " << payloadType << ";\n"
        << "    " << payloadType << " " << value << ";\n"
        << "    initial " << value << " = " << *startup << ";\n"
        << "    assign " << *q << " = " << value << ";\n"
        << "`ifndef SYNTHESIS\n"
        << "    assign " << fault << " = $isunknown(" << reset << ") || (("
        << reset << " === 1'b0) && $isunknown(" << enable << "));\n"
        << "    initial begin : " << probe << "\n"
        << "      " << payloadType << " " << payloadX << ";\n"
        << "      logic [$bits(" << payloadType << ")-1:0] " << packedX << ";\n"
        << "      if ($bits(" << payloadType << ") == 0) $fatal(1, \"" << kind << ": payload must have positive packed width\");\n"
        << "`ifndef VERILATOR\n"
        << "      " << payloadX << " = " << payloadType << "'({$bits(" << payloadType << "){1'bx}});\n"
        << "      " << packedX << " = " << payloadX << ";\n"
        << "      if (" << packedX << " !== {$bits(" << payloadType << "){1'bx}})\n"
        << "        $fatal(1, \"" << kind << ": T must be four-state packed bits or a four-state packed struct\");\n"
        << "`endif\n    end\n"
        << "`endif\n"
        << "    always @(posedge " << clock << ") begin\n"
        << "`ifndef SYNTHESIS\n"
        << "      if ((" << context.rtlCheckRef(definition, "commit_ok") << " === 1'b1) && (" << clock << " === 1'b1)) begin\n"
        << "`endif\n"
        << "        if (" << reset << ") " << value << " <= " << pins[initialIndex] << ";\n"
        << "        else if (" << enable << ") " << value << " <= " << pins[dataIndex] << ";\n"
        << "        else " << value << " <= " << value << ";\n"
        << "`ifndef SYNTHESIS\n      end\n`endif\n    end\n  end\n";
    return success();
  }

  LogicalResult emitInstances() {
    for (auto &operation : definition.getBody().front()) {
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
        auto name = legalizeIdentifier(queue.getInstanceName(),
                                       [&] { return queue.emitOpError(); });
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
        out << ")) pyc_instance_" << *name << " (\n";
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
      bool managedPrimitive = false;
      if ((context.managesChecks() || context.isPhysical()) && !kind.empty())
        managedPrimitive =
            llvm::any_of(context.sourceChecks().commits,
                         [&](const ac::HardwareCheckCommitEndpoint &endpoint) {
                           return endpoint.allocation == occurrence;
                         });
      SmallVector<std::string> inputs, outputs;
      for (auto input : occurrence->getOperands()) {
        auto value = net(input);
        if (failed(value))
          return failure();
        inputs.push_back(*value);
      }
      for (auto output : occurrence->getResults()) {
        auto value = net(output);
        if (failed(value))
          return failure();
        outputs.push_back(*value);
      }
      if (context.isPhysical() && managedPrimitive && (kind == "dff" || kind == "dffe")) {
        if (failed(emitPhysicalStorage(occurrence, kind, *bindings, inputs, outputs)))
          return failure();
        continue;
      }
      auto parameters =
          collection
              ? context.rtlInstanceParameters(cast<ac::CollectionOp>(operation))
              : context.rtlInstanceParameters(cast<ac::InstanceOp>(operation));
      auto name = context.rtlIdentifier(
          occurrence->getAttrOfType<StringAttr>("instance_name").getValue(),
          occurrence);
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
        i = generated("instance_lane_" + std::to_string(next++));
      }
      std::string childError, childComplete, childSamplingError;
      if (context.managesChecks()) {
        childError = generated("child_error_" + std::to_string(localErrors.size()));
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
            << "); ++" << i << ") begin : " << generated("instances_" + *name)
            << "\n";
      out << "  " << (kind.empty() ? context.names(callee).rtl : kind.str())
          << *parameters << " " << generated("instance_" + *name) << " (";
      bool first = true;
      auto connect = [&](bool output, unsigned ordinal, StringRef port, StringRef signal,
                         Type type) -> LogicalResult {
        auto id = context.rtlPortName(callee, output, ordinal);
        if (failed(id))
          return failure();
        std::string net = signal.str();
        if (collection) {
          auto width = context.payloadWidth(type, occurrence, true, *bindings);
          if (failed(width))
            return failure();
          net += "[((" + count + ")-1-" + i + ")*(" + *width + ") +: (" +
                 *width + ")]";
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
      for (auto [index, signal] : llvm::enumerate(inputs))
        if (failed(connect(false, index, cast<StringAttr>(inputNames[index]).getValue(), signal, signature.getInput(index))))
          return failure();
      for (auto [index, signal] : llvm::enumerate(outputs))
        if (failed(connect(true, index, cast<StringAttr>(outputNames[index]).getValue(), signal, signature.getResult(index))))
          return failure();
      if (context.managesChecks()) {
        auto managedConnection = [&](StringRef port, StringRef signal) {
          out << (first ? "\n" : ",\n") << "    ." << port << "(" << signal
              << ")";
          first = false;
        };
        if (!context.isPhysical())
          managedConnection("pyc_phase", "pyc_phase");
        auto control = [&](StringRef role, StringRef signal) {
          managedConnection("pyc_" + role.str(), signal);
        };
        control("root_commit_ok", generated("root_commit_ok"));
        if (kind.empty()) {
          control("reset_active", generated("reset_active"));
          if (!context.isPhysical())
            managedConnection("pyc_check_complete",
                              collection ? childComplete + "[" + i + "]"
                                         : childComplete);
          if (!context.isPhysical())
            managedConnection("pyc_sampling_error",
                              collection ? childSamplingError + "[" + i + "]"
                                         : childSamplingError);
        }
        control("local_error",
                          collection ? childError + "[" + i + "]" : childError);
      }
      out << (first ? ");\n" : "\n  );\n");
      if (context.isPhysical()) {
        auto instance = generated("instance_" + *name);
        auto childScope = context.rtlCheckRef(callee, "commit_ok");
        out << "`ifndef SYNTHESIS\n"
            << "  assign " << instance << "." << childScope << " = "
            << context.rtlCheckRef(definition, "commit_ok") << ";\n`endif\n";
        llvm::raw_string_ostream checks(physicalChecks);
        std::string error = generated("child_error_" + std::to_string(localErrors.size()));
        std::string childPath = instance + "." + context.rtlCheckRef(callee, "error");
        if (collection) {
          auto group = generated("instances_" + *name);
          auto gather = generated("check_children_" + std::to_string(next++));
          checks << "    wire [(" << count << ")-1:0] " << error << ";\n"
                 << "    for (genvar " << i << "=0; " << i << " < (" << count
                 << "); ++" << i << ") begin : " << gather << "\n"
                 << "      assign " << error << "[" << i << "] = " << group << "[" << i
                 << "]." << childPath << ";\n    end\n";
          localErrors.push_back("(|" + error + ")");
        } else {
          checks << "    wire " << error << " = " << childPath << ";\n";
          localErrors.push_back(error);
        }
      }
      if (collection)
        out << "  end\n";
    }
    return success();
  }

  LogicalResult emitAggregateError() {
    if (context.isPhysical()) {
      auto error = context.rtlCheckName(definition, "error");
      auto commit = context.rtlCheckName(definition, "commit_ok");
      out << "\n  // Simulation checks; no functional interface ports.\n"
          << "`ifndef SYNTHESIS\n  if (1) begin : " << context.rtlCheckName(definition, "checks") << "\n"
          << physicalChecks
          << "    wire " << error << " = "
          << (localErrors.empty() ? "1'b0" : join(localErrors, " | ")) << ";\n";
      if (context.sourceChecks().owners.front().definition == definition) {
        const auto &projection = context.physicalProjection();
        auto clock = context.rtlPortName(definition, false, projection.clockInput);
        auto reset = physicalReset();
        if (failed(clock) || failed(reset)) return failure();
        auto fault = context.rtlCheckName(definition, "physical_fault");
        auto physicalError = context.rtlCheckName(definition, "physical_error");
        out << "    bit " << fault << " = 1'b0;\n"
            << "    wire " << physicalError << " = " << error << " | $isunknown(" << *reset << ");\n"
            << "    wire " << commit << " = !" << fault << " && !" << physicalError << ";\n"
            << "    always @(" << *clock << ") begin\n"
            << "      if ($isunknown(" << *clock << ") || ((" << *clock << " === 1'b1) && " << physicalError << ")) begin\n"
            << "        if (!" << fault << ") $display(\"PYCIRCUIT_PHYSICAL_FAULT\");\n"
            << "        " << fault << " = 1'b1;\n"
            << "      end\n    end\n";
      } else {
        // The enclosing generated module supplies this through a private
        // hierarchical connection; synthesis contains neither endpoint.
        out << "    wire " << commit << ";\n";
      }
      out << "  end\n`endif\n";
      return success();
    }
    if (!context.managesChecks())
      return success();
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
    return success();
  }

private:
  HardwareEmitContext &context;
  ac::ModuleOp definition;
  raw_ostream &out;
  std::unique_ptr<RtlPresentationPlan> presentation;
  llvm::DenseMap<Value, std::string> names;
  llvm::DenseMap<Value, std::string> initializers;
  llvm::DenseSet<Operation *> instances;
  llvm::DenseMap<uint64_t, std::string> samplingNames;
  std::string physicalChecks;
  SmallVector<std::string> localErrors;
  SmallVector<std::string> localCompletions;
  SmallVector<std::string> localSamplingErrors;
  unsigned next = 0;
};
} // namespace
LogicalResult emitHardwareVerilogDefinition(HardwareEmitContext &context,
                                            ac::ModuleOp definition,
                                            raw_ostream &out,
                                            llvm::json::Array *presentation) {
  auto &names = context.names(definition);
  out << "module " << names.rtl;
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
  if (!parameters.empty())
    out << " #(\n" << join(parameters, ",\n") << "\n)";
  out << " (";
  bool first = true;
  auto emitPort = [&](StringRef direction, Type type,
                      unsigned ordinal) -> LogicalResult {
    auto rendered = context.rtlWireType(type, definition);
    if (failed(rendered))
      return failure();
    auto id = context.rtlPortName(definition, direction == "output", ordinal);
    if (failed(id))
      return failure();
    out << (first ? "\n" : ",\n") << "  " << direction << " " << *rendered
        << " " << *id;
    first = false;
    return success();
  };
  auto signature = definition.getFunctionType();
  for (auto [i, type] : llvm::enumerate(signature.getInputs()))
    if (failed(emitPort(
            "input", type,
            i)))
      return failure();
  for (auto [i, type] : llvm::enumerate(signature.getResults()))
    if (failed(emitPort(
            "output", type,
            i)))
      return failure();
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
  out << (first ? ");\n" : "\n);\n");
  std::string deferred;
  llvm::raw_string_ostream deferredOut(deferred);
  auto &body = context.isPhysical() ? static_cast<raw_ostream &>(deferredOut) : out;
  NetEmitter nets(context, definition, body);
  if (failed(nets.preparePresentation())) return failure();
  auto yield = cast<ac::YieldOp>(definition.getBody().front().back());
  for (auto [i, value] : llvm::enumerate(yield.getValues())) {
    auto wire = nets.net(value);
    if (failed(wire))
      return failure();
    auto id = context.rtlPortName(definition, true, i);
    if (failed(id))
      return failure();
    body << "  assign " << *id << " = " << *wire << ";\n";
  }
  if (failed(nets.emitSourceChecks()))
    return failure();
  if (failed(nets.emitObservations()))
    return failure();
  if (failed(nets.emitInstances()))
    return failure();
  if (failed(nets.emitAggregateError())) return failure();
  if (context.isPhysical()) {
    nets.finishPresentation(out, presentation);
    out << "\n  // Outputs, checks, structured logic and state/child instances\n" << deferred;
  }
  out << "endmodule\n";
  return success();
}
} // namespace acir::compiler
