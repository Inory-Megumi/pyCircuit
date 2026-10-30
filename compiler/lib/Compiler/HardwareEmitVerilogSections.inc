// Typed emission buffers. Nothing here parses or rewrites emitted RTL.
class ReadableRtlSections final : public llvm::raw_ostream {
    struct Group {
        std::string key, label, text;
        unsigned order = 0;
    };
    struct Scope {
        std::array<std::string, 3> declarations;
        SmallVector<Group> groups;
        llvm::StringMap<unsigned> indices;
        std::string active = "shared";
    };
    raw_ostream &sink;
    bool enabled;
    uint64_t position = 0;
    SmallVector<std::unique_ptr<Scope>> scopes;
    llvm::StringMap<unsigned> methodOrder;
    llvm::StringSet<> roots;

    Group &group(Scope &scope, StringRef key, StringRef label = {}, unsigned order = 0) {
        auto [found, inserted] = scope.indices.try_emplace(key, scope.groups.size());
        if (inserted) scope.groups.push_back({key.str(), label.empty() ? "Shared wiring" : label.str(), {}, order});
        return scope.groups[found->second];
    }
    std::string render(Scope &scope) {
        std::string result;
        llvm::raw_string_ostream out(result);
        const char *labels[] = {"Constants", "State registers", "Signals"};
        for (unsigned i = 0; i != 3; ++i)
            if (!scope.declarations[i].empty())
                out << "\n  // " << labels[i] << "\n" << scope.declarations[i];
        SmallVector<unsigned> order;
        for (auto [index, entry] : llvm::enumerate(scope.groups))
            if (!entry.text.empty()) order.push_back(index);
        llvm::stable_sort(order, [&](unsigned a, unsigned b) { return scope.groups[a].order < scope.groups[b].order; });
        for (unsigned index : order) {
            auto &entry = scope.groups[index];
            out << "\n  // ";
            llvm::printEscapedString(entry.label, out);
            out << ".\n" << entry.text;
        }
        return result;
    }
    void write_impl(const char *data, size_t size) override {
        group(*scopes.back(), scopes.back()->active).text.append(data, size);
        position += size;
    }
    uint64_t current_pos() const override { return position; }

public:
    class Guard {
        Scope *scope = nullptr;
        std::string previous;
    public:
        Guard(ReadableRtlSections &owner, StringRef key, StringRef label, unsigned order) {
            if (!owner.enabled) return;
            scope = owner.scopes.back().get();
            previous = scope->active;
            owner.group(*scope, key, label, order);
            scope->active = key.str();
        }
        Guard(const Guard &) = delete;
        Guard &operator=(const Guard &) = delete;
        ~Guard() { if (scope) scope->active = previous; }
    };

    ReadableRtlSections(raw_ostream &sink, bool enabled)
        : llvm::raw_ostream(true), sink(sink), enabled(enabled) {
        scopes.push_back(std::make_unique<Scope>());
    }
    bool isEnabled() const { return enabled; }
    void describe(StringRef key, StringRef label, unsigned order) {
        if (enabled) { auto &entry = group(*scopes.back(), key, label, order); entry.label = label.str(); }
    }
    Guard select(StringRef key, StringRef label, unsigned order) { return Guard(*this, key, label, order); }
    void noteMethod(StringRef method) { methodOrder.try_emplace(method, methodOrder.size()); }
    void noteRoot(StringRef root) { roots.insert(root); }
    unsigned sourceOrder(StringRef scope) const {
        if (roots.contains(scope)) return 1000;
        auto found = methodOrder.find(scope);
        return found == methodOrder.end() ? 500 : 10 + found->second;
    }
    bool isRoot(StringRef scope) const { return roots.contains(scope); }
    void inherit(const ReadableRtlSections &parent) {
        methodOrder = parent.methodOrder;
        roots = parent.roots;
    }
    void declaration(unsigned category, StringRef text) {
        if (enabled) scopes.back()->declarations[category] += text;
        else sink << text;
    }
    void beginScope() { if (enabled) scopes.push_back(std::make_unique<Scope>()); }
    void endScope() {
        if (!enabled) return;
        auto child = std::move(scopes.back());
        scopes.pop_back();
        auto text = render(*child);
        SmallVector<StringRef> lines;
        StringRef(text).split(lines, '\n');
        for (auto line : lines)
            if (!line.empty()) *this << "  " << line << "\n";
    }
    void finish() { if (enabled) sink << render(*scopes.front()); }
};
