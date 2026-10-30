#ifndef ACIR_LIB_COMPILER_FINALCPPNAMES_H
#define ACIR_LIB_COMPILER_FINALCPPNAMES_H

#include "Dialect/ACIR/ACIRSourceContracts.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"

#include <string>

namespace acir::compiler {

bool isAsciiAlpha(char value);
bool isAsciiDigit(char value);

struct CppOwnerComponents {
  std::string moduleName;
  llvm::SmallVector<std::string> namespaces;
  llvm::SmallVector<std::string> filePath;
};

mlir::FailureOr<CppOwnerComponents>
sourceOwnerComponents(mlir::DictionaryAttr owner,
                      ac::detail::EmitError emitError);
mlir::FailureOr<std::string>
legalizeIdentifier(llvm::StringRef source, ac::detail::EmitError emitError);
// RTL has its own namespace and standard escaped identifiers. C++ mangling
// must not turn an authored ASCII hardware name into a hexadecimal alias.
mlir::FailureOr<std::string>
rtlIdentifier(llvm::StringRef source, ac::detail::EmitError emitError);
std::string rtlIdentifierStem(llvm::StringRef spelling);
mlir::FailureOr<std::string>
rtlQualifiedIdentifier(llvm::StringRef symbol, llvm::StringRef suffix,
                       ac::detail::EmitError emitError);
mlir::FailureOr<std::string>
sourceDefinitionName(mlir::FlatSymbolRefAttr definition,
                     llvm::StringRef moduleName,
                     ac::detail::EmitError emitError);
mlir::FailureOr<std::string>
namespaceCppName(llvm::ArrayRef<std::string> components,
                 ac::detail::EmitError emitError);
mlir::FailureOr<std::string>
sourcePathName(llvm::ArrayRef<std::string> components,
               llvm::StringRef extension, ac::detail::EmitError emitError);
std::string join(llvm::ArrayRef<std::string> parts, llvm::StringRef separator);

} // namespace acir::compiler

#endif // ACIR_LIB_COMPILER_FINALCPPNAMES_H
