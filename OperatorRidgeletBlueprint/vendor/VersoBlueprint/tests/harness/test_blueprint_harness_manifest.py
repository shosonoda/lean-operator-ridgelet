from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from scripts.blueprint_harness_manifest import load_json_object


class BlueprintHarnessManifestTests(unittest.TestCase):
    def test_load_json_object_accepts_top_level_object(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            manifest = Path(tmp) / "manifest.json"
            manifest.write_text('{"version": 1}\n', encoding="utf-8")

            self.assertEqual(load_json_object(manifest), {"version": 1})

    def test_load_json_object_rejects_non_object(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            manifest = Path(tmp) / "manifest.json"
            manifest.write_text("[]\n", encoding="utf-8")

            with self.assertRaisesRegex(ValueError, "expected JSON object"):
                load_json_object(manifest)

    def test_load_json_object_reports_invalid_json(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            manifest = Path(tmp) / "manifest.json"
            manifest.write_text("{\n", encoding="utf-8")

            with self.assertRaisesRegex(ValueError, "invalid JSON"):
                load_json_object(manifest)


if __name__ == "__main__":
    unittest.main()
