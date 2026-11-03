#ifndef PYCIRCUIT_SOURCE_FORWARDING_H
#define PYCIRCUIT_SOURCE_FORWARDING_H

#include "pycircuit/Dialect/ACIR/HardwareAnalysis.h"
#include <functional>

namespace acir::ac::detail {
// The initial forwarding profile is a statically selected Bits leaf. Ordinary
// Method/state types retain their existing wider profile.
inline mlir::FailureOr<mlir::Type> forwardLeafType(
    const HardwareAnalysis &analysis, mlir::Type type, mlir::ArrayAttr fields,
    mlir::Operation *site,
    const std::function<mlir::LogicalResult(uint64_t)> &debit = {},
    mlir::DictionaryAttr *leafField = nullptr) {
    if (!fields || fields.size() > 128)
        return site->emitOpError() << "forward requires a bounded static field path";
    for (mlir::Attribute raw : fields) {
        auto name = mlir::dyn_cast<mlir::StringAttr>(raw);
        auto structure = mlir::dyn_cast<StructType>(type);
        auto declaration = structure ? analysis.lookupStruct(structure) : StructOp();
        if (debit && mlir::failed(debit(8 + (declaration ? declaration.getFields().size() : 0))))
            return mlir::failure();
        mlir::Type selected;
        if (name && declaration)
            for (mlir::Attribute rawField : declaration.getFields()) {
                auto field = mlir::cast<mlir::DictionaryAttr>(rawField);
                if (field.getAs<mlir::StringAttr>("name") == name) {
                    selected = field.getAs<mlir::TypeAttr>("type").getValue();
                    if (leafField) *leafField = field;
                }
            }
        if (!selected) return site->emitOpError() << "forward field is not a declared Struct field";
        type = selected;
    }
    if (!mlir::isa<BitsType>(type))
        return site->emitOpError() << "forward currently requires a persistent Bits leaf";
    return type;
}
}

#endif
