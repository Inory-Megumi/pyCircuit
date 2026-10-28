        // Readiness is an unconditional declaration, independent of which
        // collision result is selected. Keep Method bodies as the sole author
        // definition of each operation's ordinary candidate update.
        auto viewPath = [&](const AstNode &node) {
            SmallVector<StringRef> fields;
            auto root = node;
            while (root.kind() == "Attribute") {
                fields.push_back(root.string("attr"));
                root = root.child("value");
            }
            std::string result = root.kind() == "Name" ? root.string("id").str() : "";
            for (auto field : llvm::reverse(fields)) result += "." + field.str();
            return result;
        };
        llvm::StringSet<> readyDeclared;
        bool prefix = true;
        for (size_t i = 0; i < statement.array("body").size(); ++i) {
            auto item = statement.item("body", i);
            if (docstring(item)) continue;
            auto target = item.kind() == "Assign" && item.array("targets").size() == 1
                ? item.item("targets", 0) : AstNode();
            auto member = target.child("value");
            bool ready = target.kind() == "Attribute" && target.string("attr") == "ready" &&
                member.kind() == "Attribute" && member.child("value").kind() == "Name" &&
                member.child("value").string("id") == opsName;
            if (!ready) { prefix = false; continue; }
            auto operationName = member.string("attr");
            if (!prefix || !llvm::is_contained(operationNames, at.getStringAttr(operationName)) ||
                    !readyDeclared.insert(operationName).second)
                return error() << "compose ready requires one unconditional leading assignment per declared operation";
            auto &operation = methods[operationName];
            if (operation.composeReady) return error() << "operation readiness is already defined by another composer";
            operation.composeReady = item.child("value");
            auto collect = [&](auto &&self, const AstNode &node) -> LogicalResult {
                if (failed(chargeLoopDescriptorWork(node, "compose readiness"))) return failure();
                auto path = viewPath(node);
                auto mapped = combined.composeNames.find(path);
                if (mapped != combined.composeNames.end()) {
                    StringRef formal = mapped->second;
                    if (formal.starts_with("@__compose_old_")) {
                        unsigned ordinal = 0;
                        if (formal.drop_front(StringRef("@__compose_old_").size()).getAsInteger(10, ordinal) ||
                                ordinal >= targetNames.size()) return failure();
                        operation.composeReadyStates[path] = cast<StringAttr>(targetNames[ordinal]).getValue().str();
                        return success();
                    }
                    if (formal.starts_with("@__compose_active_")) {
                        unsigned ordinal = 0;
                        if (formal.drop_front(StringRef("@__compose_active_").size()).getAsInteger(10, ordinal) ||
                                ordinal >= operationNames.size()) return failure();
                        auto peer = cast<StringAttr>(operationNames[ordinal]).getValue();
                        if (peer == operationName) return error() << "compose ready cannot depend on its own final activity";
                        operation.composeReadyPeers[path] = peer.str();
                        return success();
                    }
                    return error() << "compose ready may read old state and peer active, not candidate values or write views";
                }
                if (node.kind() == "Name" && node.string("id") == opsName)
                    return error() << "compose ready has an unknown operation view";
                for (auto field : node.fields()) {
                    auto key = field.getName().strref();
                    if (isa<DictionaryAttr>(field.getValue())) {
                        auto child = node.child(key);
                        if (!child.kind().empty() && failed(self(self, child))) return failure();
                    } else if (auto children = dyn_cast<ArrayAttr>(field.getValue())) {
                        for (size_t k = 0; k < children.size(); ++k) if (isa<DictionaryAttr>(children[k])) {
                            auto child = node.item(key, k);
                            if (!child.kind().empty() && failed(self(self, child))) return failure();
                        }
                    }
                }
                return success();
            };
            if (failed(collect(collect, operation.composeReady))) return failure();
            combined.composeReadyStatements.push_back(item);
        }
