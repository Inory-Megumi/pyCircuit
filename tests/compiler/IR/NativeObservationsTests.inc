TEST_F(SourceTransactionCaptureTest, ForwardWriterEnvelopeRejectsDetachedPayloadPermissionAndQ) {
    auto captured = capture("forward_auth.py", R"py(import pycircuit as ac
@ac.module
def Bank(enable: ac.u1) -> ac.u8:
    value: ac.u8 = 10
    @ac.method(kind="action")
    def put(payload: ac.u8) -> None:
        value = payload
    @ac.rule
    def write() -> None:
        put(7)
        ac.guard(enable)
    @ac.rule
    def observe() -> ac.u8:
        return ac.forward(value, source=put)
    return observe
)py");
    ASSERT_TRUE(captured);
    auto headers = compiler::SourceHeaderRegistry::create(&context, {}, error());
    ASSERT_TRUE(succeeded(headers));
    auto unit = compiler::compilePythonSourceUnit(
        *captured, owner("forward_auth.py"), *headers, error());
    ASSERT_TRUE(succeeded(unit)) << diagnostics;
    compiler::SourceLinkStages stages;
    auto linked = compiler::linkSourceUnits(
        {{*unit->body, *unit->interface}}, "forward_auth.Bank", error(),
        compiler::SourceLinkTarget::Hardware, &stages);
    ASSERT_TRUE(succeeded(linked)) << diagnostics;
    std::string finalText;
    llvm::raw_string_ostream stream(finalText);
    (*linked)->print(stream);
    for (bool routed : {true, false}) {
        for (unsigned mutation = 0; mutation < 4; ++mutation) {
            auto reloaded = parseSourceString<ModuleOp>(
                routed ? stages.routedTransactions : finalText, &context);
            ASSERT_TRUE(reloaded);
            auto check = [&] {
                return routed ? ac::verifyRoutedPackage(*reloaded)
                              : ac::verifyHardwarePackage(*reloaded);
            };
            ASSERT_TRUE(succeeded(check())) << diagnostics;
            ac::BitsSelectOp filled;
            for (auto rule : operations<ac::RuleOp>(*reloaded)) {
                auto sampled = rule->getAttrOfType<DictionaryAttr>("ac.sampled_admission");
                auto actions = sampled ? sampled.getAs<ArrayAttr>("actions") : ArrayAttr();
                if (!actions) continue;
                for (Attribute raw : actions) {
                    auto views = cast<DictionaryAttr>(raw).getAs<ArrayAttr>("forwards");
                    if (!views) continue;
                    ASSERT_EQ(views.size(), 1u);
                    auto row = cast<DictionaryAttr>(views[0]);
                    auto index = row.getAs<IntegerAttr>("result").getInt();
                    auto yield = cast<ac::YieldOp>(rule.getBody().front().getTerminator());
                    filled = yield.getOperand(index).getDefiningOp<ac::BitsSelectOp>();
                }
            }
            ASSERT_TRUE(filled);
            if (mutation == 0) {
                // A typed Q wire is not the source's actual writer candidate.
                filled->setOperand(1, filled.getFalseValue());
            } else if (mutation == 1) {
                // A candidate wire is not committed Q, even at the same type.
                filled->setOperand(2, filled.getTrueValue());
            } else if (mutation == 2) {
                // Source-path metadata cannot replace actual writer permission.
                auto mask = filled.getCondition().getDefiningOp<ac::BitsBinaryOp>();
                ASSERT_TRUE(mask);
                mask->setOperand(1, mask.getLhs());
            } else {
                // A legal constant is not a view of the actual candidate D.
                auto type = cast<ac::BitsType>(filled.getResult().getType());
                Builder b(&context);
                auto integer = b.getDictionaryAttr({
                    b.getNamedAttr("kind", b.getStringAttr("integer")),
                    b.getNamedAttr("value", ac::MathIntAttr::get(&context, llvm::APSInt("9")))});
                OpBuilder builder(filled);
                OperationState constant(filled.getLoc(), ac::BitsConstantOp::getOperationName());
                constant.addTypes(type);
                constant.addAttribute("value", ac::StaticExprAttr::get(
                    &context, changed(type.getWidth().getTree(), "value", integer)));
                auto *replacement = builder.create(constant);
                ASSERT_TRUE(succeeded(mlir::verify(replacement))) << diagnostics;
                filled->setOperand(1, replacement->getResult(0));
            }
            diagnostics.clear();
            // The package verifier itself includes the forward-Q envelope;
            // only the replacement operation's ordinary typing must stay valid.
            ASSERT_TRUE(succeeded(mlir::verify(filled))) << diagnostics;
            diagnostics.clear();
            EXPECT_TRUE(failed(check())) << "detached forward witness was admitted";
            EXPECT_FALSE(diagnostics.empty());
        }
    }
}
