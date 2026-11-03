#ifndef PYCIRCUIT_HARDWARE_ACTION_VIEWS_H
#define PYCIRCUIT_HARDWARE_ACTION_VIEWS_H

#include "pycircuit/Dialect/ACIR/HardwareAnalysis.h"
#include "llvm/ADT/DenseSet.h"

namespace acir::ac::detail {
class SourceCheckBudget;
struct ActionViewProof {
    llvm::DenseSet<mlir::OpOperand *> uses;
    llvm::DenseSet<mlir::Operation *> operations;
};
mlir::FailureOr<ActionViewProof> verifyActionView(
    RuleOp rule, const HardwareAnalysis &analysis, SourceCheckBudget &budget);
mlir::LogicalResult verifyActionDomains(RuleOp producer, RuleOp observer,
    const HardwareAnalysis &analysis, SourceCheckBudget &budget);
mlir::LogicalResult verifyForwardOldQ(mlir::Value value, mlir::DictionaryAttr state,
    RuleOp reader, const HardwareAnalysis &analysis, SourceCheckBudget &budget);
}
#endif
