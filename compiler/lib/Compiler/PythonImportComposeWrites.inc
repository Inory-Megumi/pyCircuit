        // Infer only referenced views. Field paths are compile-time names;
        // Table indices remain ordinary hardware indexing of the mask Table.
        ac::HardwareAnalysis composeAnalysis(*body);
        auto scanWrites = [&](auto &&self, const AstNode &node) -> LogicalResult {
            if (failed(chargeLoopDescriptorWork(node, "compose write views"))) return failure();
            if (node.kind() == "Attribute") {
                SmallVector<std::string> path;
                auto root = node;
                for (unsigned depth = 0; root.kind() == "Attribute"; ++depth) {
                    if (depth >= 128) return error() << "compose write view exceeds the field depth bound";
                    path.push_back(root.string("attr").str());
                    root = root.child("value");
                }
                std::reverse(path.begin(), path.end());
                if (root.kind() == "Name" && root.string("id") == opsName &&
                        path.size() >= 2 && path[1] == "writes") {
                    auto operation = llvm::find(operationNames, at.getStringAttr(path[0]));
                    if (operation == operationNames.end()) return error() << "compose writes names an unknown operation";
                    unsigned target = 0, offset = 2;
                    if (targets.kind() == "Tuple") {
                        if (path.size() == offset) return error() << "compose writes requires a target name";
                        auto found = llvm::find(targetNames, at.getStringAttr(path[offset++]));
                        if (found == targetNames.end()) return error() << "compose writes names an unknown target";
                        target = found - targetNames.begin();
                    }
                    SmallVector<Attribute> fields;
                    for (auto field : ArrayRef(path).drop_front(offset)) fields.push_back(at.getStringAttr(field));
                    auto type = ac::detail::composeWriteViewType(combined.inputs[target].type,
                        at.getArrayAttr(fields), internalBits(1, statement, decl.symbol), composeAnalysis);
                    if (failed(type)) return error() << "compose writes requires a scalar leaf field; indexed Tables retain their mask shape";
                    auto descriptor = at.getDictionaryAttr({
                        at.getNamedAttr("operation", at.getI64IntegerAttr(operation - operationNames.begin())),
                        at.getNamedAttr("target", at.getI64IntegerAttr(target)),
                        at.getNamedAttr("fields", at.getArrayAttr(fields))});
                    auto found = llvm::find(writeViews, descriptor);
                    unsigned ordinal = found == writeViews.end() ? writeViews.size() : found - writeViews.begin();
                    std::string formal = "__compose_writes_" + std::to_string(ordinal);
                    if (found == writeViews.end()) {
                        writeViews.push_back(descriptor);
                        combined.inputs.push_back({formal, *type, node, {}, true});
                    }
                    std::string name = opsName;
                    for (const auto &field : path) name += "." + field;
                    combined.composeNames[name] = "@" + formal;
                    return success();
                }
            }
            for (auto field : node.fields()) {
                auto key = field.getName().strref();
                if (isa<DictionaryAttr>(field.getValue())) {
                    auto child = node.child(key);
                    if (!child.kind().empty() && failed(self(self, child))) return failure();
                } else if (auto array = dyn_cast<ArrayAttr>(field.getValue())) {
                    for (size_t i = 0; i < array.size(); ++i) if (isa<DictionaryAttr>(array[i])) {
                        auto child = node.item(key, i);
                        if (!child.kind().empty() && failed(self(self, child))) return failure();
                    }
                }
            }
            return success();
        };
        for (size_t i = 0; i < statement.array("body").size(); ++i)
            if (failed(scanWrites(scanWrites, statement.item("body", i)))) return failure();
