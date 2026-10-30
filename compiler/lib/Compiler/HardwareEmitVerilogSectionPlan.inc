ReadableRtlSections::Guard readableSection(Value value) {
    if (!readableSections.isEnabled()) return readableSections.select("", "", 0);
    value = readableSource(value);
    if (readableRoleHints.contains(value))
        return readableSections.select("commit_control", "Atomic update control", 2000);
    unsigned priority = 0;
    llvm::StringSet<> scopes;
    for (auto origin : ac::sourceRtlRoles(readableSource(value))) {
        auto role = origin.getAs<StringAttr>("role"), scope = origin.getAs<StringAttr>("scope");
        if (!role || !scope) continue;
        unsigned rank = llvm::StringSwitch<unsigned>(role.getValue())
            .Case("after", 4).Cases("index_match", "lane_value", 3)
            .Cases("condition", "write_value", 2).Cases("source", "binding", 1).Default(0);
        if (!rank || rank < priority) continue;
        if (rank > priority) { scopes.clear(); priority = rank; }
        scopes.insert(scope.getValue());
    }
    if (scopes.size() > 1) {
        SmallVector<std::string> callers;
        for (const auto &entry : scopes)
            if (readableSections.isRoot(entry.getKey())) callers.push_back(entry.getKey().str());
        if (callers.size() != scopes.size())
            for (auto &caller : callers) scopes.erase(caller);
    }
    if (scopes.size() != 1) return readableSections.select("shared", "Shared wiring", 0);
    auto scope = scopes.begin()->getKey();
    std::string escaped;
    llvm::raw_string_ostream stream(escaped);
    llvm::printEscapedString(scope, stream);
    return readableSections.select("source:" + scope.str(),
        (readableSections.isRoot(scope) ? "Source rule: " : "Source method: ") + escaped,
        readableSections.sourceOrder(scope));
}

void readableDeclaration(StringRef storage, StringRef type, StringRef name,
                         StringRef initializer = {}, bool state = false, unsigned indentation = 2) {
    std::string text;
    llvm::raw_string_ostream declaration(text);
    declaration << std::string(indentation, ' ');
    if (!storage.empty()) declaration << storage << " ";
    if (!type.empty()) declaration << type << " ";
    declaration << name;
    bool split = readableSections.isEnabled() && storage == "wire" && !initializer.empty();
    if (!initializer.empty() && !split) declaration << " = " << initializer;
    declaration << ";\n";
    readableSections.declaration(storage == "localparam" ? 0 : state ? 1 : 2, text);
    if (split) out << std::string(indentation, ' ') << "assign " << name << " = " << initializer << ";\n";
}

void finishReadableGenerate() {
    readableSections.endScope();
    out << "  end\n";
}

void emitPortAssignment(StringRef target, StringRef source) {
    auto section = readableSections.select("outputs", "Output connections", 4000);
    out << "  assign " << target << " = " << source << ";\n";
}

void finishReadableLayout() { readableSections.finish(); }
