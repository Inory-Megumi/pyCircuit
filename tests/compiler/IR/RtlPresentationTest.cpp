#include "Compiler/HardwareEmitCommon.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "pycircuit/Dialect/ACIR/ACIRDialect.h"
#include "gtest/gtest.h"

namespace {
namespace ac = acir::ac;
using namespace mlir;

// Exercise the native symbolic-type boundary. Python currently admits neither
// // nor % in static annotations; this fixture does not change that language.
TEST(RtlPresentation, SymbolicTypesRetainOnlyTheirHelperDependencies) {
    MLIRContext context;
    context.loadDialect<ac::ACIRDialect>();
    const std::string metadata =
        ", origin = {site = {definition = @top, ast_path = []}, expansion = []}, "
        "location = {path = \"helpers.py\", line = 1 : i64, column = 1 : i64, "
        "end_line = 1 : i64, end_column = 2 : i64}";
    for (const std::string opcode : {"floordiv", "mod", "add"}) {
        SCOPED_TRACE(opcode);
        auto expression = [&](const std::string &tree) {
            return "#ac.static_expr<{" + tree + metadata + "}>";
        };
        auto text = "#three = " + expression("kind = \"literal\", value = {kind = \"integer\", value = #ac.math_int<3>}") +
            "\n#parameter = " + expression("kind = \"reference\", ref = {kind = \"parameter\", owner = @top, name = \"W\"}") +
            "\n#width = " + expression("kind = \"binary\", operator = \"" + opcode + "\", lhs = #parameter, rhs = #three") + R"(
!payload = !ac.bits<#width>
module {
    "ac.module"() ({
    ^bb0(%incoming: !payload):
        "ac.yield"(%incoming) : (!payload) -> ()
    }) {sym_name = "top", source_owner = {package = "", path = "helpers.py"},
        parameters = [{name = "W", type = !ac.math_int}], type_parameters = [],
        function_type = (!payload) -> !payload,
        input_names = ["incoming"], output_names = ["result"]} : () -> ()
}
)";
        auto package = parseSourceString<ModuleOp>(text, &context);
        ASSERT_TRUE(package);
        ASSERT_TRUE(succeeded(verify(*package)));
        ac::HardwareAnalysis analysis(*package);
        acir::compiler::HardwareEmitContext renderer(*package, analysis, true);
        auto module = *package->getOps<ac::ModuleOp>().begin();
        auto type = module.getBody().front().getArgument(0).getType();
        auto wire = renderer.rtlWireType(type, module);
        ASSERT_TRUE(succeeded(wire));
        EXPECT_NE(wire->find("parameter_W"), std::string::npos);
        EXPECT_EQ(renderer.usesRtlHelper("floordiv"), opcode == "floordiv");
        EXPECT_EQ(renderer.usesRtlHelper("mod"), opcode == "mod");
        if (opcode != "add")
            EXPECT_NE(wire->find("pycircuit_types::" + opcode + "("), std::string::npos);
    }
}
} // namespace
