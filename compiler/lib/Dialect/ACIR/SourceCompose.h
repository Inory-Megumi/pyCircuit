#ifndef PYCIRCUIT_SOURCE_COMPOSE_H
#define PYCIRCUIT_SOURCE_COMPOSE_H

#include "pycircuit/Dialect/ACIR/ACIROps.h"
#include "pycircuit/Dialect/ACIR/HardwareAnalysis.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "llvm/ADT/StringSet.h"

namespace acir::ac::detail {

// A write view projects a scalar leaf through Struct fields and, optionally,
// one indexed Table. Tables retain their shape; each leaf is a one-bit mask.
inline mlir::FailureOr<mlir::Type> composeWriteViewType(
        mlir::Type type, mlir::ArrayAttr fields, mlir::Type predicate,
        const HardwareAnalysis &analysis) {
    TableType table;
    unsigned field = 0;
    for (unsigned depth = 0; depth < 128; ++depth) {
        if (auto indexed = mlir::dyn_cast<TableType>(type)) {
            if (table || indexed.getShape().size() != 1) return mlir::failure();
            table = indexed;
            type = table.getElementType();
            continue;
        }
        if (auto structure = mlir::dyn_cast<StructType>(type)) {
            if (field == fields.size()) return mlir::failure();
            auto declaration = analysis.lookupStruct(structure);
            mlir::Type next;
            if (declaration) for (auto raw : declaration.getFields()) {
                auto item = mlir::cast<mlir::DictionaryAttr>(raw);
                if (item.getAs<mlir::StringAttr>("name") == fields[field])
                    next = item.getAs<mlir::TypeAttr>("type").getValue();
            }
            if (!next) return mlir::failure();
            type = next;
            ++field;
            continue;
        }
        if (field != fields.size() || !mlir::isa<BitsType, EnumType>(type))
            return mlir::failure();
        return table ? mlir::Type(TableType::get(type.getContext(), table.getShape(), predicate))
                     : predicate;
    }
    return mlir::failure();
}

inline bool composeLiteralTrue(mlir::Value value, const HardwareAnalysis &analysis) {
    auto constant = value.getDefiningOp<BitsConstantOp>();
    if (!constant) return false;
    auto evaluated = analysis.evaluateStatic(constant.getValue(), {}, constant);
    if (mlir::failed(evaluated)) return false;
    auto integer = mlir::dyn_cast<MathIntAttr>(*evaluated);
    return integer && integer.getCanonicalValue() == "1";
}

inline SourceMethodOp stateComposer(SourceStateOp state) {
    auto module = state->getParentOfType<ModuleOp>();
    for (auto method : module.getBody().front().getOps<SourceMethodOp>()) {
        auto contract = method->getAttrOfType<mlir::DictionaryAttr>("ac.compose");
        if (!contract) continue;
        auto targets = contract.getAs<mlir::ArrayAttr>("targets");
        if (targets && llvm::is_contained(targets, state.getInstanceNameAttr())) return method;
    }
    return {};
}

inline mlir::LogicalResult verifySourceCompose(SourceMethodOp method) {
    auto raw = method->getAttr("ac.compose");
    if (!raw) return mlir::success();
    auto contract = mlir::dyn_cast<mlir::DictionaryAttr>(raw);
    auto targets = contract ? contract.getAs<mlir::ArrayAttr>("targets") : mlir::ArrayAttr();
    auto operations = contract ? contract.getAs<mlir::ArrayAttr>("operations") : mlir::ArrayAttr();
    auto writes = contract ? contract.getAs<mlir::ArrayAttr>("writes") : mlir::ArrayAttr();
    if (!contract || contract.size() != (writes ? 3 : 2) ||
        (writes && writes.empty()) || !targets || targets.empty() || !operations || operations.empty() ||
        !method.getCaptures().empty() || method->getAttrOfType<mlir::StringAttr>("sym_visibility") !=
            mlir::StringAttr::get(method.getContext(), "private"))
        return method.emitOpError() << "compose requires a closed private target/operation contract";
    auto module = method->getParentOfType<ModuleOp>();
    HardwareAnalysis analysis(method->getParentOfType<mlir::ModuleOp>());
    auto guard = mlir::dyn_cast<YieldOp>(method.getGuard().front().getTerminator());
    if (!guard || guard.getValues().size() != 1 || !composeLiteralTrue(guard.getValues()[0], analysis))
        return method.emitOpError() << "compose must have an unconditional guard";
    llvm::StringSet<> names;
    llvm::SmallVector<mlir::Type> types;
    for (auto rawTarget : targets) {
        auto name = mlir::dyn_cast<mlir::StringAttr>(rawTarget);
        if (!name || !names.insert(name.getValue()).second)
            return method.emitOpError() << "compose target names must be unique";
        SourceStateOp state;
        for (auto candidate : module.getBody().front().getOps<SourceStateOp>())
            if (candidate.getInstanceNameAttr() == name) state = candidate;
        if (!state || !mlir::isa<BitsType, EnumType, StructType, TableType>(state.getQ().getType()))
            return method.emitOpError() << "compose target must be finite hardware owner state";
        types.push_back(state.getQ().getType());
        for (auto other : module.getBody().front().getOps<SourceMethodOp>()) {
            if (other == method) continue;
            auto otherContract = other->getAttrOfType<mlir::DictionaryAttr>("ac.compose");
            auto otherTargets = otherContract ? otherContract.getAs<mlir::ArrayAttr>("targets") : mlir::ArrayAttr();
            if (otherTargets && llvm::is_contained(otherTargets, name))
                return method.emitOpError() << "state belongs to multiple compose declarations";
        }
    }
    auto signature = method.getFunctionType();
    if (signature.getNumResults() != types.size() ||
        signature.getNumInputs() != types.size() + operations.size() * (1 + types.size()) +
            (writes ? writes.size() : 0))
        return method.emitOpError() << "compose typed signature does not match its target/operation contract";
    for (auto [i, type] : llvm::enumerate(types))
        if (!areEquivalentHardwareTypes(type, signature.getInput(i)) ||
            !areEquivalentHardwareTypes(type, signature.getResult(i)))
            return method.emitOpError() << "compose target type differs from owner state";
    names.clear();
    unsigned cursor = types.size();
    for (auto rawOperation : operations) {
        auto name = mlir::dyn_cast<mlir::StringAttr>(rawOperation);
        auto operation = name ? mlir::dyn_cast_or_null<SourceMethodOp>(
            mlir::SymbolTable::lookupSymbolIn(module, name.getValue())) : SourceMethodOp();
        if (!name || !names.insert(name.getValue()).second || !operation ||
            operation->hasAttr("ac.compose") || operation.getFunctionType().getNumResults())
            return method.emitOpError() << "compose operation must name a distinct action Method";
        if (!areEquivalentHardwareTypes(signature.getInput(cursor++), guard.getValues()[0].getType()))
            return method.emitOpError() << "compose activity must be a predicate";
        for (auto type : types)
            if (!areEquivalentHardwareTypes(type, signature.getInput(cursor++)))
                return method.emitOpError() << "compose operation candidate type differs";
        llvm::StringSet<> written;
        if (!operation.getBody().hasOneBlock())
            return method.emitOpError() << "compose operation requires a single body block";
        auto checked = operation.getBody().walk([&](mlir::Operation *statement) {
            if (auto write = mlir::dyn_cast<SourceStateWriteOp>(statement)) {
                if (!llvm::is_contained(targets, write.getStateAttr()))
                    return mlir::WalkResult::interrupt();
                if (write->hasAttr("ac.compose_hold")) {
                    auto read = write.getValue().getDefiningOp<SourceStateReadOp>();
                    if (!mlir::isa<mlir::UnitAttr>(write->getAttr("ac.compose_hold")) ||
                            !read || read.getStateAttr() != write.getStateAttr() ||
                            !read.getSelectors().empty() || !write.getSelectors().empty() ||
                            !composeLiteralTrue(read.getPath(), analysis) ||
                            !composeLiteralTrue(write.getPath(), analysis) ||
                            write->getBlock() != &operation.getBody().front())
                        return mlir::WalkResult::interrupt();
                }
                written.insert(write.getState());
            } else if (!mlir::isa<SourceStateReadOp, YieldOp, SourceBranchOp>(statement) &&
                       !mlir::isMemoryEffectFree(statement)) {
                return mlir::WalkResult::interrupt();
            }
            return mlir::WalkResult::advance();
        });
        if (checked.wasInterrupted())
            return method.emitOpError() << "compose operation must update only its owner target group";
        if (written.size() != types.size())
            return method.emitOpError() << "compose operation must contribute every target owner";
    }
    llvm::SmallVector<mlir::Attribute> seenViews;
    if (writes) for (auto rawView : writes) {
        auto view = mlir::dyn_cast<mlir::DictionaryAttr>(rawView);
        auto operation = view ? view.getAs<mlir::IntegerAttr>("operation") : mlir::IntegerAttr();
        auto target = view ? view.getAs<mlir::IntegerAttr>("target") : mlir::IntegerAttr();
        auto fields = view ? view.getAs<mlir::ArrayAttr>("fields") : mlir::ArrayAttr();
        if (!view || view.size() != 3 || !operation || !target || !fields ||
                !operation.getType().isSignlessInteger(64) || !target.getType().isSignlessInteger(64) ||
                operation.getInt() < 0 || uint64_t(operation.getInt()) >= operations.size() ||
                target.getInt() < 0 || uint64_t(target.getInt()) >= types.size() ||
                llvm::any_of(fields, [](auto field) { return !mlir::isa<mlir::StringAttr>(field); }) ||
                llvm::is_contained(seenViews, rawView))
            return method.emitOpError() << "compose write view has an invalid operation, target or field path";
        seenViews.push_back(rawView);
        auto type = composeWriteViewType(types[target.getInt()], fields, guard.getValues()[0].getType(), analysis);
        if (mlir::failed(type) || !areEquivalentHardwareTypes(*type, signature.getInput(cursor++)))
            return method.emitOpError() << "compose write view must identify a scalar storage leaf";
    }
    auto pure = method.getBody().walk([&](mlir::Operation *op) {
        if (mlir::isa<YieldOp, SourceBranchOp>(op)) return mlir::WalkResult::advance();
        if (!mlir::isMemoryEffectFree(op)) return mlir::WalkResult::interrupt();
        return mlir::WalkResult::advance();
    });
    if (pure.wasInterrupted()) return method.emitOpError() << "compose body must be a pure next-state calculation";
    return mlir::success();
}
} // namespace acir::ac::detail
#endif
