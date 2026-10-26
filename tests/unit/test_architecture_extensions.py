"""Public architecture extension entry and packaging boundaries."""

from __future__ import annotations

import ast
import contextlib
import hashlib
import importlib.util
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

from arch_primitives import elaborate
from pycircuit.cli import main

ROOT = Path(__file__).resolve().parents[2]
SOURCE = """import pycircuit as ac
from arch_primitives import Pipe, Table

@ac.module
def ExtensionFixture():
    pipe = Pipe[ac.u8](flow="valid_ready")
    table = Table[ac.u8](depth=2, init=0)

    @ac.rule
    def transfer() -> None:
        pipe.push(7)
        table.write(0, 7)

"""


class ArchitectureExtensionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.source = Path(self.temporary.name) / "author.py"
        self.output = self.source.with_name("expanded.py")
        self.source.write_text(SOURCE, encoding="ascii")

    def call(self, *extra):
        with contextlib.redirect_stderr(io.StringIO()) as errors:
            code = main(["elaborate", str(self.source), "-o", str(self.output), *extra])
        return code, errors.getvalue()

    def test_cli_uses_the_same_expansion_and_manifest_as_the_public_api(self):
        expected = self.output.with_name("api.py")
        expected_manifest = elaborate(self.source, expected)
        self.assertEqual(self.call(), (0, ""))
        self.assertEqual(self.output.read_bytes(), expected.read_bytes())
        actual = json.loads(self.output.with_suffix(".components.json").read_text())
        self.assertEqual(actual, expected_manifest)
        self.assertEqual(
            {item["component"] for item in actual["instances"]}, {"Pipe", "Table"}
        )
        self.assertFalse(actual["compiler_builtin"])
        ast.parse(self.output.read_text())

    def test_existing_source_or_manifest_requires_explicit_replacement(self):
        for path in (self.output, self.output.with_suffix(".components.json")):
            with self.subTest(path=path):
                path.write_text("keep me", encoding="ascii")
                self.assertEqual(self.call()[0], 1)
                self.assertEqual(path.read_text(), "keep me")
                self.assertEqual(self.call("--replace"), (0, ""))

    def test_rejected_extension_never_replaces_existing_outputs(self):
        self.output.write_text("original", encoding="ascii")
        self.source.write_text(SOURCE.replace('flow="valid_ready"', 'flow="invalid"'))
        code, error = self.call("--replace")
        self.assertEqual(code, 1)
        self.assertIn("pycircuit elaborate:", error)
        self.assertNotIn("Traceback", error)
        self.assertEqual(self.output.read_text(), "original")
        self.assertFalse(self.output.with_suffix(".components.json").exists())

    def test_authored_source_is_never_overwritten(self):
        self.output = self.source
        self.assertEqual(self.call("--replace")[0], 1)
        self.assertEqual(self.source.read_text(), SOURCE)

    def test_source_expansion_never_executes_author_code(self):
        marker = self.source.with_name("executed")
        self.source.write_text(
            f'from pathlib import Path\nPath({str(marker)!r}).write_text("executed")\n'
            + SOURCE,
            encoding="ascii",
        )
        self.assertEqual(self.call(), (0, ""))
        self.assertFalse(marker.exists())

    def test_extension_source_preserves_import_identity_and_records_later_updates(self):
        package = ROOT / "python/arch_primitives"
        origin = json.loads((package / "ORIGIN.json").read_text())
        current = dict(origin["source_sha256"])
        current.update(
            {
                relative: update["sha256"]
                for relative, update in origin.get("source_updates", {}).items()
            }
        )
        for relative, expected in current.items():
            with self.subTest(relative=relative):
                self.assertEqual(
                    hashlib.sha256((package / relative).read_bytes()).hexdigest(),
                    expected,
                )

    def test_wheel_stages_extensions_from_the_installed_sdk(self):
        sys.path.insert(0, str(ROOT / "packaging/wheel"))
        self.addCleanup(sys.path.pop, 0)
        spec = importlib.util.spec_from_file_location(
            "architecture_wheel_packager", ROOT / "packaging/wheel/create_wheel.py"
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        prefix = self.source.parent / "sdk"
        python_root = prefix / "share/pycircuit/python"
        for name, files in {
            "pycircuit": {"cli.py": "# installed compiler driver\n"},
            "arch_primitives": {
                "__init__.py": "# installed extension\n",
                "ORIGIN.json": "{}\n",
            },
        }.items():
            for relative, content in files.items():
                target = python_root / name / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(content, encoding="ascii")
        stage = self.source.parent / "wheel"
        module._stage_installed_python(prefix, stage / "pycircuit")
        self.assertEqual((stage / "arch_primitives/ORIGIN.json").read_text(), "{}\n")
        (python_root / "arch_primitives/__init__.py").unlink()
        with self.assertRaisesRegex(SystemExit, "architecture extensions"):
            module._stage_installed_python(prefix, stage / "pycircuit")


if __name__ == "__main__":
    unittest.main()
