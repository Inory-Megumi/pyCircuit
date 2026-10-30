#ifndef PYCIRCUIT_HARDWARE_EMIT_COMMON_H
#define PYCIRCUIT_HARDWARE_EMIT_COMMON_H
#include "pycircuit/Dialect/ACIR/HardwareAnalysis.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/JSON.h"
#include <array>
#include <cstdint>
#include <functional>
#include <optional>
#include <memory>
#include <string>
#include <utility>
#include <vector>
namespace acir::compiler {
struct RtlSourceName {
  std::string module, binding, scope, site, expression, type;
  uint64_t valueOrdinal = 0;
};
struct RtlOwnershipPort {
  mlir::Value value, local;
  std::string name;
};
struct RtlOwnershipParameter {
    ac::ModuleOp owner;
    mlir::StringAttr name;
    std::string alias;
    bool type = false;
};
struct RtlOwnershipPartition {
  ac::ModuleOp caller, definition;
  ac::InstanceOp allocation;
  std::string moduleName;
  llvm::SmallVector<mlir::Operation *> operations;
  llvm::DenseSet<mlir::Operation *> moved;
  llvm::DenseMap<unsigned, mlir::Value> replacedInputs;
  llvm::DenseMap<mlir::Value, mlir::Value> aliases;
  llvm::SmallVector<RtlOwnershipPort> captures, exports;
  RtlOwnershipPartition *parent = nullptr;
  llvm::DenseSet<mlir::Operation *> subtree;
  llvm::SmallVector<RtlOwnershipParameter> parameters;
  bool active = false;
};
struct RtlOutputProjection {
    unsigned output;
    llvm::SmallVector<std::string> fields;
};
struct EmitNames {
  std::string cppQualified;
  std::string cppClass;
  std::string cppNamespace;
  std::string cppFamilyClass;
  std::string cppFamilyQualified;
  std::string rtl;
  std::string header;
  std::string source;
  std::string verilog;
};
class HardwareEmitContext {
public:
  HardwareEmitContext(mlir::ModuleOp package, ac::HardwareAnalysis &analysis,
                      bool physical = false, bool synthesis = false);
  mlir::LogicalResult prepare();
  bool isSystem();
  bool managesChecks();
  bool isPhysical() const { return physical_; }
  bool isSynthesis() const { return synthesis_; }
  bool hasPhysicalChecks() const {
    return physical_ && !synthesis_ && physicalProjection_ && physicalProjection_->hasDomain;
  }
  const ac::HardwarePhysicalProjection &physicalProjection() const {
    return *physicalProjection_;
  }
  // Prepare the verified check lifecycle shared by generated systems and
  // checked module callers; each emitter retains its observation boundary.
  mlir::LogicalResult prepareNativeChecks();
  const ac::HardwareSourceCheckPlan &sourceChecks() const;
  bool resetIfOne() const;
  std::string cppReset(llvm::StringRef expression) const;
  std::string rtlReset(llvm::StringRef expression) const;
  const EmitNames &names(mlir::Operation *definition) const;
  mlir::FailureOr<std::string> cppFormalName(llvm::StringRef name,
                                             mlir::Operation *site) const;
  mlir::FailureOr<std::string> rtlFormalName(llvm::StringRef name,
                                             mlir::Operation *site) const;
  mlir::FailureOr<std::string> rtlParameterName(mlir::FlatSymbolRefAttr owner,
                                               llvm::StringRef name, mlir::Operation *site) const;
  mlir::FailureOr<std::string> rtlPortName(mlir::Operation *definition,
                                          llvm::StringRef name) const;
  std::string rtlProtocolName(llvm::StringRef name) const;
  // Omit compiler-private identity returns whose callers can use the input.
  std::optional<unsigned> rtlForwardedInput(mlir::Operation *definition,
                                            unsigned output) const;
  bool rtlOmittedInput(mlir::Operation *definition, unsigned input) const;
  std::optional<RtlOutputProjection> rtlOutputProjection(mlir::Operation *definition, unsigned output) const;
  bool rtlOmittedOutput(mlir::Operation *definition, unsigned output) const;
  mlir::FailureOr<std::string> cppType(mlir::Type type,
                                       mlir::Operation *site) const;
  mlir::FailureOr<std::string> cppType(mlir::Type type,
                                       const ac::HardwareBindings &bindings,
                                       mlir::Operation *site) const;
  mlir::FailureOr<std::string> staticValue(ac::StaticExprAttr expression,
                                           const ac::HardwareBindings &bindings,
                                           mlir::Operation *site) const;
  mlir::FailureOr<std::string> rtlType(mlir::Type type,
                                       mlir::Operation *site) const;
  mlir::FailureOr<std::string> rtlTableDimensions(mlir::Type type,
                                                  mlir::Operation *site) const;
  mlir::FailureOr<std::string> rtlEnumMember(mlir::Type type,
                                              mlir::StringAttr member,
                                              mlir::Operation *site) const;
  mlir::FailureOr<std::string> staticValue(ac::StaticExprAttr expression,
                                           mlir::Operation *site) const;
  bool isClosedStatic(ac::StaticExprAttr expression,
                      const ac::HardwareBindings &bindings = {}) const;
  mlir::FailureOr<std::string> staticRtlValue(ac::StaticExprAttr expression,
                                              mlir::Operation *site) const;
  mlir::FailureOr<ac::HardwareBindings> rootBindings() const;
  mlir::FailureOr<std::string> rootPortMap(bool rtl = true);
  mlir::FailureOr<std::string> rootCppType() const;
  mlir::FailureOr<std::string> rootRtlParameters() const;
  mlir::FailureOr<std::string> cppInstanceType(ac::InstanceOp instance) const;
  mlir::FailureOr<std::string>
  cppBoundModuleType(mlir::Operation *definition,
                     const ac::HardwareBindings &bindings,
                     mlir::Operation *site, bool kernel = false) const;
  mlir::FailureOr<std::string>
  cppBoundFamilyType(mlir::Operation *definition,
                     const ac::HardwareBindings &bindings,
                     mlir::Operation *site, llvm::StringRef count) const;
  mlir::FailureOr<std::string>
  rtlInstanceParameters(ac::InstanceOp instance) const;
  mlir::FailureOr<std::string>
  rtlInstanceParameters(ac::CollectionOp collection) const;
  mlir::FailureOr<std::string>
  shapeSize(mlir::ArrayAttr shape, mlir::Operation *site, bool rtl = false,
            const ac::HardwareBindings &bindings = {}) const;
  mlir::FailureOr<std::string>
  payloadWidth(mlir::Type type, mlir::Operation *site, bool rtl = false,
               const ac::HardwareBindings &bindings = {}) const;
  mlir::FailureOr<std::string>
  unsignedStaticValue(ac::StaticExprAttr expression, mlir::Operation *site,
                      bool rtl = false,
                      const ac::HardwareBindings &bindings = {}) const;
  mlir::FailureOr<std::string>
  viewIndex(ac::TableViewOp view, llvm::StringRef ordinal, bool rtl = false,
            const ac::HardwareBindings &bindings = {}) const;
  mlir::FailureOr<std::string>
  cppWireExpression(mlir::Value value, const ac::HardwareBindings &bindings,
                    mlir::Operation *site) const;
  mlir::ModuleOp package;
  ac::HardwareAnalysis &analysis;
  std::vector<RtlSourceName> rtlSourceNames;
  llvm::json::Array rtlModules;
  std::vector<std::unique_ptr<RtlOwnershipPartition>> rtlPartitions;
  llvm::json::Array rtlOwnershipNotes;
  llvm::DenseSet<mlir::Operation *> rtlActiveDefinitions;
  llvm::DenseMap<mlir::Value, std::string> rtlRootConstants;
  const RtlOwnershipPartition *rtlPartition(ac::InstanceOp allocation,
                                             const RtlOwnershipPartition *parent = nullptr) const;
  bool rtlChildPartition(const RtlOwnershipPartition *child, ac::ModuleOp caller,
                         const RtlOwnershipPartition *parent) const;
  const RtlOwnershipPartition *rtlScope = nullptr;
  llvm::DenseSet<mlir::Operation *> rtlBaseDefinitions;
  llvm::DenseMap<mlir::Value, uint64_t> rtlOriginalValueIds;
  bool rtlBaseNeeded(ac::ModuleOp definition) const;

private:
  mlir::LogicalResult prepareImpl(bool allowSourceChecks);
  bool physical_ = false;
  bool synthesis_ = false;
  std::optional<ac::HardwarePhysicalProjection> physicalProjection_;
  std::optional<ac::HardwareSourceCheckPlan> sourceChecks_;
  llvm::DenseMap<mlir::Operation *, EmitNames> names_;
  llvm::DenseMap<std::pair<mlir::Type, mlir::StringAttr>, std::string> enumMemberNames_;
  llvm::DenseMap<mlir::StringAttr, std::string> nominalNames_;
  mutable llvm::DenseMap<std::pair<mlir::Operation *, unsigned>, std::optional<RtlOutputProjection>> rtlOutputProjections_;
  mutable llvm::DenseMap<std::pair<mlir::Operation *, unsigned>, bool> rtlOmittedOutputs_;
};
mlir::Value rtlOwnershipSource(mlir::Value value, const HardwareEmitContext *context = nullptr);
mlir::LogicalResult prepareRtlOwnership(HardwareEmitContext &context);
mlir::LogicalResult emitHardwareCppDefinition(HardwareEmitContext &context,
                                              ac::ModuleOp definition,
                                              llvm::raw_ostream &out);
struct ObservationEmissionSite {
  mlir::Operation *op = nullptr;
  unsigned valueIndex = 0;
  bool carriesValue = false;
  bool gauge = false;
  uint64_t registrationKey = 0, siteKey = 0;
};
struct ObservationEmissionChild {
  mlir::Operation *op = nullptr;
  ac::ModuleOp definition;
  uint64_t shape = 1;
};
struct ObservationEmissionOccurrence {
  ObservationEmissionSite site;
  uint64_t ordinal = 0;
  llvm::SmallVector<std::pair<mlir::Operation *, uint64_t>> path;
  llvm::SmallVector<std::pair<mlir::Operation *, uint64_t>> logicalOwnerPath;
};
struct ObservationEmissionPlan {
  llvm::DenseMap<mlir::Operation *, llvm::SmallVector<ObservationEmissionSite>>
      definitions;
  llvm::DenseMap<mlir::Operation *, llvm::SmallVector<ObservationEmissionChild>>
      children;
  llvm::DenseMap<mlir::Operation *, uint64_t> subtreeWidth;
  llvm::DenseMap<mlir::Operation *, llvm::SmallVector<uint64_t>> childBaseUnits;
  llvm::SmallVector<std::array<uint64_t, 5>> table;
  llvm::SmallVector<ObservationEmissionOccurrence> occurrences;
  uint64_t events = 0;
};
mlir::FailureOr<ObservationEmissionPlan>
observationEmissionPlan(HardwareEmitContext &context);
mlir::FailureOr<uint64_t>
observationPayloadWidth(HardwareEmitContext &context,
                        const ObservationEmissionOccurrence &occurrence);
mlir::FailureOr<std::string> emissionMetadataJson(mlir::Attribute value,
                                                  mlir::Operation *site);
mlir::FailureOr<std::string>
observationSiteMetadataJson(ac::SourceObserveOp observe);
mlir::FailureOr<std::string>
cppObservationRunnerMetadata(HardwareEmitContext &context);
mlir::FailureOr<std::string>
cppObservationDescriptorTable(HardwareEmitContext &context);
mlir::FailureOr<std::string>
cppObservationConfigureCall(HardwareEmitContext &context);
mlir::FailureOr<std::string>
cppObservationChildBase(HardwareEmitContext &context, ac::ModuleOp definition,
                        unsigned childIndex);
mlir::FailureOr<uint64_t> cppObservationLaneStride(HardwareEmitContext &context,
                                                   ac::ModuleOp definition);
mlir::FailureOr<uint64_t>
cppObservationSubtreeWidth(HardwareEmitContext &context,
                           ac::ModuleOp definition);
mlir::LogicalResult cppObservationStaging(
    HardwareEmitContext &context, ac::ModuleOp definition,
    const ac::HardwareBindings &bindings, llvm::StringRef object,
    llvm::StringRef count,
    const std::function<mlir::FailureOr<std::string>(mlir::Value)> &value,
    llvm::raw_ostream &out);
mlir::LogicalResult emitHardwareVerilogDefinition(HardwareEmitContext &context,
                                                  ac::ModuleOp definition,
                                                llvm::raw_ostream &out,
                                                const RtlOwnershipPartition *partition = nullptr);
} // namespace acir::compiler
#endif
