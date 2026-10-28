        auto contract = group.composer->getAttrOfType<DictionaryAttr>("ac.compose");
        if (auto views = contract.getAs<ArrayAttr>("writes")) {
            group.expanded = true;
            unsigned base = group.states.size() + contract.getAs<ArrayAttr>("operations").size() * (1 + group.states.size());
            for (auto [ordinal, raw] : llvm::enumerate(views)) {
                if (!prepayAppend(budget, group.composer, group.writes)) return failure();
                detail::ComposeGroup::WriteView view;
                view.descriptor = cast<DictionaryAttr>(raw);
                view.type = group.composer.getFunctionType().getInput(base + ordinal);
                auto fields = view.descriptor.getAs<ArrayAttr>("fields");
                unsigned kind = view.descriptor.getAs<IntegerAttr>("operation").getInt();
                unsigned target = view.descriptor.getAs<IntegerAttr>("target").getInt();
                for (auto [callID, call] : llvm::enumerate(group.contributions)) {
                    if (!charge(budget, group.composer)) return failure();
                    if (call.operation != kind) continue;
                    const auto &transaction = prepared.transactions[call.transaction];
                    for (auto [domainID, domain] : llvm::enumerate(transaction.writeDomains)) {
                        if (!charge(budget, group.composer, 1 + domain.selectors.size())) return failure();
                        const auto &write = transaction.plan->writes[domain.write];
                        if (domain.candidate != call.outputs[target] || write.frame != call.frame) continue;
                        unsigned field = 0;
                        bool matched = true;
                        for (auto rawSelector : domain.selectors) {
                            auto selector = cast<DictionaryAttr>(rawSelector);
                            if (auto name = selector.getAs<StringAttr>("field")) {
                                if (field == fields.size() || fields[field++] != name) { matched = false; break; }
                            }
                        }
                        if (!matched) continue;
                        if (!prepayAppend(budget, group.composer, view.domains)) return failure();
                        view.domains.push_back({callID, domainID});
                    }
                }
                group.writes.push_back(std::move(view));
            }
        }
