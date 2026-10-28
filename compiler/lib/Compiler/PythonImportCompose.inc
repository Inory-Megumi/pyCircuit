// A compose declaration is a pure, private callable. Its flattened typed ABI is
// compiler owned; source uses old and named Method activity/candidate values.
        AstNode targets, operations;
        if (!decorator.array("args").empty())
            return error() << "compose accepts target and operations keywords";
        for (size_t k = 0; k < decorator.array("keywords").size(); ++k) {
            auto keyword = decorator.item("keywords", k);
            if (keyword.string("arg") == "target" && !targets) targets = keyword.child("value");
            else if (keyword.string("arg") == "operations" && !operations) operations = keyword.child("value");
            else return error() << "unsupported or repeated compose keyword";
        }
        auto args = statement.child("args");
        if (!targets || operations.kind() != "Tuple" || operations.array("elts").empty() ||
            args.array("args").size() != 2 || !args.array("posonlyargs").empty() ||
            !args.array("kwonlyargs").empty() || !args.array("defaults").empty() ||
            args.child("vararg") || args.child("kwarg") || statement.child("returns") ||
            args.item("args", 0).child("annotation") || args.item("args", 1).child("annotation"))
            return error() << "compose requires target, a nonempty operations tuple and two inferred parameters";
        SourceCallableDecl combined{statement, {MarkerKind::Method, {}, {}}};
        combined.lexical = false;
        std::string oldName = args.item("args", 0).string("arg").str();
        std::string opsName = args.item("args", 1).string("arg").str();
        if (oldName == opsName || states.contains(oldName) || states.contains(opsName))
            return error() << "compose parameters must be distinct from owner state";
        auto checkLocals = [&](auto &&self, const AstNode &node) -> LogicalResult {
            if (failed(chargeLoopDescriptorWork(node, "compose local assignments"))) return failure();
            if (node.kind() == "Name" && node.child("ctx").kind() == "Store" &&
                (states.contains(node.string("id")) || node.string("id") == oldName || node.string("id") == opsName))
                return error() << "compose cannot assign owner state or rebind its input views";
            for (auto field : node.fields()) {
                auto key = field.getName().strref();
                if (isa<DictionaryAttr>(field.getValue())) {
                    auto child = node.child(key);
                    if (!child.kind().empty() && failed(self(self, child))) return failure();
                } else if (auto array = dyn_cast<ArrayAttr>(field.getValue())) {
                    for (size_t i = 0; i < array.size(); ++i)
                        if (isa<DictionaryAttr>(array[i])) {
                            auto child = node.item(key, i);
                            if (!child.kind().empty() && failed(self(self, child))) return failure();
                        }
                }
            }
            return success();
        };
        for (size_t i = 0; i < statement.array("body").size(); ++i)
            if (failed(checkLocals(checkLocals, statement.item("body", i)))) return failure();
        SmallVector<Attribute> targetNames, operationNames;
        llvm::StringSet<> seen;
        size_t targetCount = targets.kind() == "Tuple" ? targets.array("elts").size() : 1;
        if (!targetCount) return error() << "compose target cannot be empty";
        for (size_t k = 0; k < targetCount; ++k) {
            auto target = targets.kind() == "Tuple" ? targets.item("elts", k) : targets;
            if (target.kind() != "Name" || !states.contains(target.string("id")) ||
                !seen.insert(target.string("id")).second)
                return error() << "compose target requires distinct previously declared owner state names";
            const auto &state = states[target.string("id")];
            if (!isa<ac::BitsType, ac::EnumType, ac::StructType, ac::TableType>(state.type))
                return error() << "compose target requires a finite hardware storage type";
            std::string formal = "__compose_old_" + std::to_string(k);
            combined.inputs.push_back({formal, state.type, target, {}, true});
            combined.resultContracts.push_back({formal, state.type, target, {}, true});
            combined.results.push_back(state.type);
            combined.composeNames[targets.kind() == "Tuple" ? oldName + "." + target.string("id").str() : oldName] = "@" + formal;
            targetNames.push_back(at.getStringAttr(state.name));
        }
        seen.clear();
        for (size_t k = 0; k < operations.array("elts").size(); ++k) {
            auto operation = operations.item("elts", k);
            StringRef operationName = operation.string("id");
            auto found = methods.find(operationName);
            if (operation.kind() != "Name" || found == methods.end() ||
                found->second.syntax.marker != MarkerKind::Method || found->second.composition ||
                !found->second.results.empty() || !seen.insert(operationName).second)
                return error() << "compose operations require distinct action Methods";
            operationNames.push_back(at.getStringAttr(operationName));
            std::string active = "__compose_active_" + std::to_string(k);
            combined.inputs.push_back({active, internalBits(1, statement, decl.symbol), operation, {}, true});
            std::string prefix = opsName + "." + operationName.str();
            combined.composeNames[prefix + ".active"] = "@" + active;
            for (size_t ordinal = 0; ordinal < targetCount; ++ordinal) {
                auto input = combined.inputs[ordinal];
                std::string formal = "__compose_value_" + std::to_string(k) + "_" + std::to_string(ordinal);
                std::string field = prefix + ".value";
                if (targets.kind() == "Tuple")
                    field += "." + cast<StringAttr>(targetNames[ordinal]).getValue().str();
                combined.composeNames[field] = "@" + formal;
                input.name = formal;
                combined.inputs.push_back(input);
            }
        }
        SmallVector<Attribute> writeViews;
#include "PythonImportComposeWrites.inc"
#include "PythonImportComposeReady.inc"
        combined.returnShape = targetCount == 1 ? ReturnShape::Struct : ReturnShape::Tuple;
        SmallVector<Type> types;
        for (const auto &port : combined.inputs) types.push_back(port.type);
        combined.type = FunctionType::get(b.getContext(), types, combined.results);
        SmallVector<NamedAttribute> contract{
            at.getNamedAttr("targets", at.getArrayAttr(targetNames)),
            at.getNamedAttr("operations", at.getArrayAttr(operationNames))};
        if (!writeViews.empty()) contract.push_back(at.getNamedAttr("writes", at.getArrayAttr(writeViews)));
        combined.composition = at.getDictionaryAttr(contract);
        if (!methods.try_emplace(name, std::move(combined)).second)
            return error() << "compose declaration name is already bound";
        methodWork.push_back(name.str());
