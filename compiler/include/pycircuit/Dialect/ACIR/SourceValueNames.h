// Non-semantic source bindings. Locations do not add uses or affect operation
// equivalence. In particular, naming must never keep a dead value alive.
#ifndef PYCIRCUIT_DIALECT_ACIR_SOURCEVALUENAMES_H
#define PYCIRCUIT_DIALECT_ACIR_SOURCEVALUENAMES_H

#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/Value.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>

namespace acir::ac {
struct SourceValueName {
    mlir::StringAttr name;
    mlir::StringAttr scope;
    mlir::Location site;
};

// Display roles belong to exact results, separately from authored bindings.
// They must never create uses or become an inlining/CSE/ownership boundary.
inline llvm::SmallVector<mlir::DictionaryAttr> sourceRtlRoles(mlir::Value value) {
    llvm::SmallVector<mlir::DictionaryAttr> result;
    if (!value) return result;
    auto output = mlir::dyn_cast<mlir::OpResult>(value);
    unsigned index = output ? output.getResultNumber() : mlir::cast<mlir::BlockArgument>(value).getArgNumber();
    llvm::SmallVector<mlir::Location> pending{value.getLoc()};
    while (!pending.empty()) {
        auto location = pending.pop_back_val();
        if (auto fused = mlir::dyn_cast<mlir::FusedLoc>(location)) {
            auto data = mlir::dyn_cast_or_null<mlir::DictionaryAttr>(fused.getMetadata());
            auto role = data ? data.getAs<mlir::DictionaryAttr>("ac.rtl_role") : mlir::DictionaryAttr();
            auto slot = data ? data.getAs<mlir::IntegerAttr>("index") : mlir::IntegerAttr();
            auto isResult = data ? data.getAs<mlir::BoolAttr>("result") : mlir::BoolAttr();
            if (role && slot && isResult && slot.getInt() == index && isResult.getValue() == bool(output) &&
                !llvm::is_contained(result, role)) result.push_back(role);
            llvm::append_range(pending, fused.getLocations());
        } else if (auto named = mlir::dyn_cast<mlir::NameLoc>(location)) pending.push_back(named.getChildLoc());
    }
    return result;
}

inline void retainSourceRtlRole(mlir::Value value, mlir::DictionaryAttr role) {
    if (!value || llvm::is_contained(sourceRtlRoles(value), role)) return;
    mlir::Builder builder(value.getContext());
    auto output = mlir::dyn_cast<mlir::OpResult>(value);
    unsigned index = output ? output.getResultNumber() : mlir::cast<mlir::BlockArgument>(value).getArgNumber();
    auto metadata = builder.getDictionaryAttr({
        builder.getNamedAttr("ac.rtl_role", role),
        builder.getNamedAttr("index", builder.getI32IntegerAttr(index)),
        builder.getNamedAttr("result", builder.getBoolAttr(bool(output)))});
    auto location = mlir::FusedLoc::get(value.getContext(), {value.getLoc()}, metadata);
    if (output) output.getOwner()->setLoc(location);
    else mlir::cast<mlir::BlockArgument>(value).setLoc(location);
}

// Presentation provenance is captured from authenticated invocation frames.
// It carries canonical receiver occurrences, never a semantic operand or an
// authority to bypass hardware verification. Shared optimized nodes retain
// every owner and can stay at their common routing ancestor.
inline llvm::SmallVector<mlir::DictionaryAttr> sourceRtlOwners(mlir::Location location) {
    llvm::SmallVector<mlir::DictionaryAttr> result;
    llvm::SmallVector<mlir::Location> pending{location};
    while (!pending.empty()) {
        auto current = pending.pop_back_val();
        if (auto fused = mlir::dyn_cast<mlir::FusedLoc>(current)) {
            auto data = mlir::dyn_cast_or_null<mlir::DictionaryAttr>(fused.getMetadata());
            auto owners = data && data.size() == 1 ? data.getAs<mlir::ArrayAttr>("ac.rtl_owners") : mlir::ArrayAttr();
            if (owners)
                for (auto raw : owners)
                    if (auto owner = mlir::dyn_cast<mlir::DictionaryAttr>(raw))
                        if (!llvm::is_contained(result, owner)) result.push_back(owner);
            llvm::append_range(pending, fused.getLocations());
        } else if (auto named = mlir::dyn_cast<mlir::NameLoc>(current)) pending.push_back(named.getChildLoc());
    }
    return result;
}

inline void retainSourceRtlOwner(mlir::Operation *operation, mlir::DictionaryAttr owner) {
    if (llvm::is_contained(sourceRtlOwners(operation->getLoc()), owner)) return;
    mlir::Builder builder(operation->getContext());
    auto metadata = builder.getDictionaryAttr({builder.getNamedAttr("ac.rtl_owners", builder.getArrayAttr({owner}))});
    operation->setLoc(mlir::FusedLoc::get(operation->getContext(), {operation->getLoc()}, metadata));
}

// A source position is not a value binding. Fresh derived operations use this
// position; clones keep binding metadata, and semantic replacements explicitly
// call retainSourceValueNames. Authentication compares the same original
// position, preserving unrelated diagnostic Location metadata.
inline mlir::Location sourceIdentityLocation(mlir::Location location) {
    if (auto fused = mlir::dyn_cast<mlir::FusedLoc>(location)) {
        auto data = mlir::dyn_cast_or_null<mlir::DictionaryAttr>(fused.getMetadata());
        if (data && data.size() == 1 && data.getAs<mlir::ArrayAttr>("ac.rtl_owners"))
            return sourceIdentityLocation(fused.getLocations().front());
        if (data && data.size() == 3 && data.getAs<mlir::DictionaryAttr>("ac.rtl_role") &&
            data.getAs<mlir::IntegerAttr>("index") && data.getAs<mlir::BoolAttr>("result"))
            return sourceIdentityLocation(fused.getLocations().front());
        if (data && data.size() == 4 &&
            data.getAs<mlir::StringAttr>("ac.source_name") &&
            data.getAs<mlir::StringAttr>("scope") &&
            data.getAs<mlir::IntegerAttr>("index") &&
            data.getAs<mlir::BoolAttr>("result"))
            return sourceIdentityLocation(fused.getLocations().front());
        llvm::SmallVector<mlir::Location> positions;
        bool changed = false;
        for (auto child : fused.getLocations()) {
            auto position = sourceIdentityLocation(child);
            changed |= position != child;
            positions.push_back(position);
        }
        if (changed)
            return mlir::FusedLoc::get(location.getContext(), positions, fused.getMetadata());
    } else if (auto named = mlir::dyn_cast<mlir::NameLoc>(location)) {
        auto child = sourceIdentityLocation(named.getChildLoc());
        if (child != named.getChildLoc())
            return mlir::NameLoc::get(named.getName(), child);
    }
    return location;
}

inline llvm::SmallVector<SourceValueName> sourceValueNames(mlir::Value value) {
    llvm::SmallVector<SourceValueName> result;
    if (!value)
        return result;
    auto operationResult = mlir::dyn_cast<mlir::OpResult>(value);
    unsigned index = operationResult ? operationResult.getResultNumber()
                                    : mlir::cast<mlir::BlockArgument>(value).getArgNumber();
    llvm::SmallVector<mlir::Location> pending{value.getLoc()};
    while (!pending.empty()) {
        auto location = pending.pop_back_val();
        if (auto fused = mlir::dyn_cast<mlir::FusedLoc>(location)) {
            auto data = mlir::dyn_cast_or_null<mlir::DictionaryAttr>(fused.getMetadata());
            auto name = data ? data.getAs<mlir::StringAttr>("ac.source_name") : mlir::StringAttr();
            auto slot = data ? data.getAs<mlir::IntegerAttr>("index") : mlir::IntegerAttr();
            auto isResult = data ? data.getAs<mlir::BoolAttr>("result") : mlir::BoolAttr();
            auto scope = data ? data.getAs<mlir::StringAttr>("scope") : mlir::StringAttr();
            if (name && slot && isResult && scope && slot.getInt() == index &&
                isResult.getValue() == bool(operationResult)) {
                auto site = fused.getLocations().back();
                bool duplicate = llvm::any_of(result, [&](const auto &entry) {
                    return entry.name == name && entry.scope == scope && entry.site == site;
                });
                if (!duplicate)
                    result.push_back({name, scope, site});
            }
            // Visit the original producer before newer aliases. A shared value
            // keeps all its bindings, with one deterministic primary spelling.
            for (auto child : llvm::reverse(fused.getLocations()))
                pending.push_back(child);
        } else if (auto named = mlir::dyn_cast<mlir::NameLoc>(location)) {
            pending.push_back(named.getChildLoc());
        }
    }
    std::reverse(result.begin(), result.end());
    return result;
}

inline void retainSourceValueName(mlir::Value value, llvm::StringRef name,
                                  llvm::StringRef scope, mlir::Location site) {
    if (!value || name.empty())
        return;
    for (const auto &entry : sourceValueNames(value))
        if (entry.name.getValue() == name && entry.scope.getValue() == scope && entry.site == site)
            return;
    mlir::Builder builder(value.getContext());
    auto result = mlir::dyn_cast<mlir::OpResult>(value);
    unsigned index = result ? result.getResultNumber()
                            : mlir::cast<mlir::BlockArgument>(value).getArgNumber();
    auto metadata = builder.getDictionaryAttr({
        builder.getNamedAttr("ac.source_name", builder.getStringAttr(name)),
        builder.getNamedAttr("scope", builder.getStringAttr(scope)),
        builder.getNamedAttr("index", builder.getI32IntegerAttr(index)),
        builder.getNamedAttr("result", builder.getBoolAttr(bool(result)))
    });
    auto location = mlir::FusedLoc::get(value.getContext(), {value.getLoc(), site}, metadata);
    if (result)
        result.getOwner()->setLoc(location);
    else
        mlir::cast<mlir::BlockArgument>(value).setLoc(location);
}

inline void retainSourceValueNames(mlir::Value from, mlir::Value to) {
    if (from == to)
        return;
    for (const auto &entry : sourceValueNames(from))
        retainSourceValueName(to, entry.name.getValue(), entry.scope.getValue(), entry.site);
    for (auto role : sourceRtlRoles(from)) retainSourceRtlRole(to, role);
    if (auto *operation = to.getDefiningOp())
        for (auto owner : sourceRtlOwners(from.getLoc())) retainSourceRtlOwner(operation, owner);
}

inline void retainSourceValueNames(mlir::ValueRange from, mlir::ValueRange to) {
    for (auto [source, replacement] : llvm::zip(from, to))
        retainSourceValueNames(source, replacement);
}
} // namespace acir::ac
#endif
