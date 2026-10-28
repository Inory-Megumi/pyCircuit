        struct WriteView {
            Type type;
            SmallVector<std::pair<unsigned, unsigned>> uses;
        };
        SmallVector<WriteView> masks;
        if (writeViews) for (auto rawView : writeViews) {
            auto view = dyn_cast<DictionaryAttr>(rawView);
            if (failed(exact(view, {"operation", "target", "fields", "domains"}, rule, "compose write view"))) return failure();
            auto kind = ordinal(view, "operation", operations.size());
            auto target = ordinal(view, "target", count);
            auto fields = view.getAs<ArrayAttr>("fields");
            auto domains = view.getAs<ArrayAttr>("domains");
            if (failed(kind) || failed(target) || !fields || !domains ||
                    llvm::any_of(fields, [](auto field) { return !isa<StringAttr>(field); })) return failure();
            if (failed(charge(budget, rule, 1 + fields.size(), sizeof(WriteView)))) return failure();
            auto type = composeWriteViewType(states[indices[*target]].payload, fields,
                body.getArgument(calls.front().start).getType(), analysis);
            if (failed(type)) return rule.emitOpError() << "composition mask does not identify a scalar leaf";
            WriteView mask{*type, {}};
            SmallVector<std::pair<uint64_t, uint64_t>> seen;
            for (auto rawDomain : domains) {
                auto use = dyn_cast<ArrayAttr>(rawDomain);
                auto callID = use && use.size() == 2 ? dyn_cast<IntegerAttr>(use[0]) : IntegerAttr();
                auto domainID = use && use.size() == 2 ? dyn_cast<IntegerAttr>(use[1]) : IntegerAttr();
                if (!callID || !domainID || !callID.getType().isSignlessInteger(64) ||
                        !domainID.getType().isSignlessInteger(64) || callID.getInt() < 0 || domainID.getInt() < 0 ||
                        uint64_t(callID.getInt()) >= calls.size() || input == rule->getNumOperands()) return failure();
                const auto &call = calls[callID.getInt()];
                auto sampled = writerAdmission(entry, call.writer->rule);
                if (failed(sampled) || uint64_t(domainID.getInt()) >= (*sampled)->writeDomains.size() || call.operation != *kind)
                    return rule.emitOpError() << "composition mask refers to another operation";
                auto key = std::make_pair(uint64_t(callID.getInt()), uint64_t(domainID.getInt()));
                if (failed(charge(budget, rule, 1 + seen.size(), sizeof(key))) || llvm::is_contained(seen, key)) return failure();
                seen.push_back(key);
                const auto &domain = (*sampled)->writeDomains[domainID.getInt()];
                auto slots = cast<DictionaryAttr>(rows[callID.getInt()]).getAs<ArrayAttr>("candidates");
                if (domain.candidate != uint64_t(cast<IntegerAttr>(slots[*target]).getInt()))
                    return rule.emitOpError() << "composition mask belongs to another target";
                unsigned field = 0;
                for (auto rawSelector : domain.selectors) {
                    if (failed(budget.debit(1, rule))) return failure();
                    auto selector = cast<DictionaryAttr>(rawSelector);
                    if (auto name = selector.getAs<StringAttr>("field")) {
                        if (field == fields.size() || fields[field++] != name)
                            return rule.emitOpError() << "composition mask belongs to another field";
                    }
                }
                auto actual = normal(rule->getOperand(input), entry.scope);
                auto expected = normal(call.writer->rule->getResult(domain.maskResult), entry.scope);
                if (failed(actual) || failed(expected) || !sameEndpoint(*actual, *expected) ||
                        (isa<TableType>(actual->resolvedType) && !areEquivalentHardwareTypes(actual->resolvedType, *type)))
                    return rule.emitOpError() << "composition mask capture differs from its actual write domain";
                if (failed(allowUse(entry.scope, rule, input, indices[*target], PrivateRoute::Mask)) ||
                        failed(charge(budget, rule, 1, sizeof(std::pair<unsigned, unsigned>)))) return failure();
                mask.uses.push_back({unsigned(callID.getInt()), input++});
            }
            masks.push_back(std::move(mask));
        }
