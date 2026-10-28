        // The returned author value resolves overlap only. No-call and
        // singleton behavior are derived from the complete Method candidates.
        auto site = callable.declaration;
        auto location = method->getLoc();
        auto targets = callable.composition.getAs<ArrayAttr>("targets");
        auto operations = callable.composition.getAs<ArrayAttr>("operations");
        auto predicateType = internalBits(1, site, decl.symbol);
        auto zero = constant(predicateType, 0, site, inside, decl.symbol);
        if (failed(zero)) return failure();
        auto binary = [&](Value lhs, Value rhs, StringRef opcode) -> Value {
            return createOp(inside, location, ac::BitsBinaryOp::getOperationName(),
                {lhs, rhs}, {predicateType},
                {inside.getNamedAttr("opcode", inside.getStringAttr(opcode))})->getResult(0);
        };
        Value seen = *zero, overlap = *zero;
        for (size_t k = 0; k < operations.size(); ++k) {
            if (failed(chargeLoopDescriptorWork(site, "compose default selection", 8))) return failure();
            auto active = values.lookup("@__compose_active_" + std::to_string(k));
            overlap = binary(overlap, binary(seen, active, "and"), "or");
            seen = binary(seen, active, "or");
        }
        for (size_t k = 0; k < targets.size(); ++k) {
            Value single = values.lookup("@__compose_old_" + std::to_string(k));
            for (size_t j = 0; j < operations.size(); ++j) {
                if (failed(chargeLoopDescriptorWork(site, "compose candidate selection", 8))) return failure();
                auto active = values.lookup("@__compose_active_" + std::to_string(j));
                auto value = values.lookup("@__compose_value_" + std::to_string(j) + "_" + std::to_string(k));
                auto chosen = select(active, value, single, site, inside, decl.symbol);
                if (failed(chosen)) return failure();
                single = *chosen;
            }
            auto chosen = select(overlap, (*yielded)[k], single, site, inside, decl.symbol);
            if (failed(chosen)) return failure();
            (*yielded)[k] = *chosen;
        }
