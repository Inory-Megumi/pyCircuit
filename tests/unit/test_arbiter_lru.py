"""Disabled public LRU admission and retained internal service-order checks."""

import ast
import tempfile
import unittest
from itertools import permutations
from pathlib import Path
from types import SimpleNamespace

from arch_primitives import ArbiterError, elaborate
from arch_primitives.components.arbiter import ArbiterConfiguration, arbiter_definition
from arch_primitives.components.arbiter_lru import constant_select, lru_definition


class Bits(int):
    def __class_getitem__(cls, width):
        return cls

    def __getitem__(self, bounds):
        return Bits(
            (int(self) >> bounds.start) & ((1 << (bounds.stop - bounds.start)) - 1)
        )


class LruTests(unittest.TestCase):
    def test_literal_pair_queries_match_service_order(self):
        config = ArbiterConfiguration(4, "lru", 0)
        pairs = [(left, right) for left in range(4) for right in range(left + 1, 4)]
        for order in permutations(range(4)):
            age = Bits(
                sum(
                    1 << bit
                    for bit, (left, right) in enumerate(pairs)
                    if order.index(left) < order.index(right)
                )
            )
            for mask in range(16):
                if mask.bit_count() > 2:
                    continue
                query = constant_select(config, mask)
                query.decorator_list = []
                namespace = {"ac": SimpleNamespace(bits=Bits), "age_snapshot": age}
                tree = ast.fix_missing_locations(
                    ast.Module(body=[query], type_ignores=[])
                )
                exec(compile(tree, "<literal-pair-query>", "exec"), namespace)
                index = next((index for index in order if mask & (1 << index)), None)
                self.assertEqual(
                    namespace[query.name](), 0 if index is None else 1 << index
                )

    def test_generated_functions_match_all_small_service_lists(self):
        for count in range(1, 5):
            config = ArbiterConfiguration(count, "lru", 0)
            pure = [node for node in lru_definition(config) if not node.decorator_list]
            namespace = {
                "ac": SimpleNamespace(
                    bits=Bits,
                    u1=Bits,
                    concat=lambda *values: sum(
                        int(value) << bit for bit, value in enumerate(reversed(values))
                    ),
                )
            }
            tree = ast.fix_missing_locations(ast.Module(body=pure, type_ignores=[]))
            exec(compile(tree, "<generated-lru>", "exec"), namespace)
            choose = namespace[config.name + "_select"]
            update = namespace.get(config.name + "_served")
            pairs = [
                (left, right)
                for left in range(count)
                for right in range(left + 1, count)
            ]

            def encode(order, pairs=pairs):
                return Bits(
                    sum(
                        1 << bit
                        for bit, (left, right) in enumerate(pairs)
                        if order.index(left) < order.index(right)
                    )
                )

            for order in permutations(range(count)):
                for requests in range(1 << count):
                    age = encode(order)
                    expected = next(
                        (index for index in order if requests & (1 << index)), None
                    )
                    actual = (
                        choose(Bits(requests), age) if pairs else choose(Bits(requests))
                    )
                    self.assertEqual(actual, 0 if expected is None else 1 << expected)
                    if expected is not None and update is not None:
                        successor = [index for index in order if index != expected] + [
                            expected
                        ]
                        self.assertEqual(
                            update(age, Bits(1 << expected)), encode(successor)
                        )

    def test_public_policy_is_disabled_before_method_expansion(self):
        bodies = [
            (f'inputs={count}, policy="lru"', "arb.select(1)\n    arb.grant(1)")
            for count in (1, 2, 3, 4, 32)
        ] + [
            (
                'inputs=4, policy="lru", initial=0',
                "arb.select(15)",
            ),
            ('inputs=4, policy="lru"', "arb.advance(0)"),
            (
                'inputs=4, policy="lru"',
                "arb.grant(15)\n    arb.grant(3)",
            ),
        ]
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "author.py"
            for options, body in bodies:
                source.write_text(
                    "import pycircuit as ac\nfrom arch_primitives import Arbiter\n"
                    "@ac.module\ndef Example():\n"
                    f"    arb = Arbiter({options})\n"
                    "    @ac.rule\n    def issue():\n"
                    f'        {body.replace(chr(10), chr(10) + "    ")}\n'
                )
                with self.subTest(options=options, body=body):
                    with self.assertRaisesRegex(
                        ArbiterError, "lru is temporarily disabled"
                    ):
                        elaborate(source, source.with_name("expanded.py"))
                    self.assertFalse(source.with_name("expanded.py").exists())
                    self.assertFalse(
                        source.with_name("expanded.components.json").exists()
                    )

    def test_definition_entry_also_rejects_disabled_policy(self):
        with self.assertRaisesRegex(ArbiterError, "lru is temporarily disabled"):
            arbiter_definition(ArbiterConfiguration(4, "lru", 0))


if __name__ == "__main__":
    unittest.main()
