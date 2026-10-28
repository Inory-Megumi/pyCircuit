        auto site = callable.composeReady;
        auto location = site.location(b.getContext(), source.path);
        auto origin = sourceOccurrence(inside, decl.symbol, site);
        auto predicateType = internalBits(1, site, decl.symbol);
        // Readiness belongs to the closed composer scope, not to the Method's
        // parameters or lexical captures. Only declared views enter this map.
        llvm::StringMap<Value> readyValues;
        llvm::StringMap<StateOwner> readyStates;
        llvm::StringMap<Instance *> readyInstances;
        SourceCallableDecl readyCallable;
        readyCallable.lexical = false;
        SourceEffectContext readyContext{&decl, &readyCallable, &readyStates,
                                         &readyInstances, nullptr, true};
        auto previousEffects = activeSourceEffects;
        activeSourceEffects = &readyContext;
        auto restoreEffects = llvm::scope_exit([&] { activeSourceEffects = previousEffects; });
        llvm::StringMap<std::string> readyNames;
        auto previous = activeComposeNames;
        auto restoreReady = llvm::scope_exit([&] { activeComposeNames = previous; });
        unsigned ordinal = 0;
        for (const auto &binding : callable.composeReadyStates) {
            auto found = states.find(binding.second);
            if (found == states.end()) return error() << "compose ready state is unavailable";
            auto path = trueValue(site, inside, decl.symbol);
            if (failed(path)) return failure();
            Value value = createOp(inside, location, ac::SourceStateReadOp::getOperationName(),
                {*path}, {found->second.type},
                {inside.getNamedAttr("state", inside.getStringAttr(found->second.name)),
                 inside.getNamedAttr("selectors", inside.getArrayAttr({})),
                 inside.getNamedAttr("occurrence", origin)})->getResult(0);
            auto name = "@compose.ready.state." + std::to_string(ordinal++);
            readyValues[name] = value;
            readyNames[binding.first()] = name;
            remember(value, std::nullopt);
            if (isa<ac::BitsType>(value.getType())) fixedValues.insert(value);
        }
        for (const auto &binding : callable.composeReadyPeers) {
            auto zero = constant(predicateType, 0, site, inside, decl.symbol);
            if (failed(zero)) return failure();
            Value value = createOp(inside, location, ac::SourceAdmitOp::getOperationName(),
                {*zero}, {predicateType},
                {inside.getNamedAttr("releases", inside.getArrayAttr({inside.getStringAttr(binding.second)})),
                 inside.getNamedAttr("occurrence", origin)})->getResult(0);
            auto name = "@compose.ready.peer." + std::to_string(ordinal++);
            readyValues[name] = value;
            readyNames[binding.first()] = name;
            remember(value, std::nullopt);
            fixedValues.insert(value);
        }
        activeComposeNames = &readyNames;
        auto ready = expression(site, inside, decl.symbol, readyValues, readyInstances);
        if (failed(ready)) return failure();
        auto predicate = predicateView(*ready, site, decl.symbol);
        if (failed(predicate)) return error() << "compose ready must be a pure one-bit predicate";
        yielded[0] = createOp(inside, location, ac::BitsBinaryOp::getOperationName(),
            {yielded[0], predicate->value}, {predicateType},
            {inside.getNamedAttr("opcode", inside.getStringAttr("and"))})->getResult(0);
