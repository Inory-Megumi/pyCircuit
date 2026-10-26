// Read-only, invocation-local parsing. Standalone API calls remain fresh.
namespace {
uint64_t orderedLookupCost(uint64_t count);

uint64_t sampledViewCopyWork(const SampledAdmissionView &view) {
    uint64_t cost = 1 + SourceCheckBudget::bytes(sizeof(view));
    auto vector = [&](const auto &values) {
        cost = SourceCheckBudget::add(
            cost, SourceCheckBudget::multiply(
                      values.size(), SourceCheckBudget::add(
                                         1, SourceCheckBudget::bytes(sizeof(values.front())))));
    };
    vector(view.controls);
    vector(view.bodyChecks);
    vector(view.observations);
    vector(view.requirements);
    vector(view.resources);
    vector(view.queueProposals);
    vector(view.memoryProposals);
    vector(view.writeDomains);
    for (const auto &observation : view.observations)
        vector(observation.values);
    for (const auto &resource : view.resources)
        if (resource.prospective)
            vector(resource.prospective->priorPops);
    for (const auto &proposal : view.queueProposals)
        vector(proposal.excludedControls);
    for (const auto &proposal : view.memoryProposals) {
        vector(proposal.argumentResults);
        vector(proposal.arguments);
    }
    return cost;
}
} // namespace

struct SampledAdmissionParseScope::Impl {
    struct Entry {
        HardwareBindings bindings;
        SampledAdmissionView view;
        uint64_t copyWork;
    };
    using Bucket = SmallVector<std::unique_ptr<Entry>, 0>;
    using Index = std::map<Operation *, Bucket>;
    Index rules;
};

thread_local SampledAdmissionParseScope *SampledAdmissionParseScope::active = nullptr;

SampledAdmissionParseScope::SampledAdmissionParseScope(
    const HardwareAnalysis &analysis, SourceCheckBudget &budget)
    : previous(active), analysis(analysis), budget(budget) {
    active = this;
}

SampledAdmissionParseScope::~SampledAdmissionParseScope() {
    assert(active == this && "sampled parse scopes must be nested");
    active = previous;
}

FailureOr<SampledAdmissionView> SampledAdmissionParseScope::parse(
    RuleOp rule, const HardwareBindings &bindings) {
    if (!rule)
        return parseSampledAdmissionImpl(rule, analysis, bindings, budget);
    if (!cache) {
        if (failed(charge(budget, rule, 1, sizeof(Impl))))
            return failure();
        cache = std::make_unique<Impl>();
    }
    if (failed(budget.debit(orderedLookupCost(cache->rules.size()), rule)))
        return failure();
    auto position = cache->rules.lower_bound(rule.getOperation());
    bool found = position != cache->rules.end() && position->first == rule.getOperation();
    if (found) {
        for (const auto &entry : position->second) {
            if (failed(budget.debit(SourceCheckBudget::add(
                    1, SourceCheckBudget::add(
                           SourceCheckBudget::bindings(bindings),
                           SourceCheckBudget::bindings(entry->bindings))), rule)))
                return failure();
            if (!sameHardwareBindings(bindings, entry->bindings))
                continue;
            if (failed(budget.debit(entry->copyWork, rule)))
                return failure();
            return entry->view;
        }
    }
    auto parsed = parseSampledAdmissionImpl(rule, analysis, bindings, budget);
    if (failed(parsed))
        return failure();
    uint64_t copySizingWork = SourceCheckBudget::add(
        parsed->observations.size(),
        SourceCheckBudget::add(parsed->resources.size(), SourceCheckBudget::add(
            parsed->queueProposals.size(), parsed->memoryProposals.size())));
    if (failed(budget.debit(copySizingWork, rule)))
        return failure();
    uint64_t copyWork = sampledViewCopyWork(*parsed);
    if (failed(charge(budget, rule, 1, sizeof(Impl::Entry))) ||
        failed(budget.debit(SourceCheckBudget::bindings(bindings), rule)) ||
        failed(budget.debit(SourceCheckBudget::multiply(2, copyWork), rule)))
        return failure();
    if (!found) {
        if (failed(charge(budget, rule, 1,
                          sizeof(Impl::Index::value_type) + 4 * sizeof(void *))))
            return failure();
        position = cache->rules.emplace_hint(position, rule.getOperation(), Impl::Bucket());
    }
    auto &bucket = position->second;
    if (bucket.size() == bucket.capacity()) {
        uint64_t capacity = std::max(
            uint64_t(2), SourceCheckBudget::add(
                             SourceCheckBudget::multiply(bucket.capacity(), 2), 1));
        if (capacity > bucket.max_size()) {
            (void)budget.debit(std::numeric_limits<uint64_t>::max(), rule);
            return failure();
        }
        uint64_t growth = SourceCheckBudget::multiply(
            capacity - bucket.capacity(), sizeof(std::unique_ptr<Impl::Entry>));
        if (failed(budget.debit(SourceCheckBudget::add(
                                   SourceCheckBudget::bytes(growth), bucket.size()), rule)))
            return failure();
        bucket.reserve(capacity);
    }
    bucket.push_back(std::make_unique<Impl::Entry>(
        Impl::Entry{bindings, std::move(*parsed), copyWork}));
    return bucket.back()->view;
}

FailureOr<SampledAdmissionView> parseSampledAdmission(
    RuleOp rule, const HardwareAnalysis &analysis, const HardwareBindings &bindings,
    SourceCheckBudget &budget) {
    auto *scope = SampledAdmissionParseScope::active;
    if (scope && &scope->analysis == &analysis && &scope->budget == &budget)
        return scope->parse(rule, bindings);
    return parseSampledAdmissionImpl(rule, analysis, bindings, budget);
}
