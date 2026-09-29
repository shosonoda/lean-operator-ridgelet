#!/usr/bin/env python3
"""Regression checks for destructive manuscript synchronization failure modes."""
import copy
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name("sync-paper-numbers.py")
SPEC = importlib.util.spec_from_file_location("sync_paper_numbers", SCRIPT)
SYNC = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SYNC)


class SyncTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "sections").mkdir()
        self.tex = self.root / "entry.tex"
        self.aux = self.root / "entry.aux"
        self.tex.write_text("% \\input{missing}\n\\input{sections/body}\n")
        (self.root / "sections/body.tex").write_text(
            "\\begin{thm}[Example]\\label{thm:example}Text.\\end{thm}\n")
        self.aux.write_text("\\@input{sections/body.aux}\n")
        (self.root / "sections/body.aux").write_text(
            "\\newlabel{thm:example}{{4.2}{15}{Title}{theorem.4.2}{}}\n")
        self.old = {"manuscript": {"file": "main.tex", "version": "numbered manuscript",
                                    "conventions": "Keep this."},
                    "custom": {"retain": True}, "items": [{"label": "thm:example",
                    "kind": "theorem", "number": "4.2", "title": "Old", "page": "1",
                    "lean": ["OperatorRidgelet.Paper.thm_4_2"], "note": "Scope note.",
                    "revision": "restated", "custom": [1, 2]}]}

    def sync(self, **kwargs):
        return SYNC.synchronize(self.old, self.tex, self.aux, **kwargs)

    def test_recursive_sources_preserve_metadata_and_logical_filename(self):
        before = copy.deepcopy(self.old)
        data = self.sync()
        self.assertEqual(self.old, before)
        self.assertEqual(data["manuscript"]["file"], "main.tex")
        self.assertEqual(data["manuscript"]["conventions"], "Keep this.")
        self.assertEqual(data["custom"], self.old["custom"])
        item = data["items"][0]
        self.assertEqual((item["title"], item["number"], item["page"]), ("Example", "4.2", "15"))
        self.assertEqual(item["blueprint_label"], "thm:4.2")
        for key in ("lean", "note", "revision", "custom"):
            self.assertEqual(item[key], self.old["items"][0][key])

    def test_nested_inputs_resolve_from_entry_directory(self):
        (self.root / "sections/wrapper.tex").write_text("\\input{sections/body}\n")
        self.tex.write_text("\\include{sections/wrapper}\n")
        self.assertEqual(len(self.sync()["items"]), 1)

    def test_empty_inventory_never_erases_index(self):
        self.tex.write_text("No statements.\n")
        with self.assertRaisesRegex(ValueError, "no manuscript items"):
            self.sync(allow_item_changes=True)

    def test_dropped_item_needs_explicit_override(self):
        self.old["items"].append({"label": "thm:other", "kind": "theorem"})
        with self.assertRaisesRegex(ValueError, "inventory changed"):
            self.sync()
        self.assertEqual(len(self.sync(allow_item_changes=True)["items"]), 1)

    def test_missing_auxiliary_number_fails(self):
        self.aux.write_text("")
        with self.assertRaisesRegex(ValueError, "missing or invalid auxiliary number"):
            self.sync()

    def test_duplicate_labels_and_cycles_fail(self):
        self.tex.write_text("\\input{sections/body}\n\\input{sections/body}\n")
        with self.assertRaisesRegex(ValueError, "duplicate manuscript label"):
            self.sync()
        self.tex.write_text("\\input{entry}\n")
        with self.assertRaisesRegex(ValueError, "input cycle"):
            self.sync()

    def test_label_cannot_leak_from_a_later_environment(self):
        self.tex.write_text("\\begin{lem}No label.\\end{lem}\n\\input{sections/body}")
        with self.assertRaisesRegex(ValueError, "unlabelled lem"):
            self.sync()

    def test_dry_run_and_failed_cli_leave_index_untouched(self):
        index = self.root / "paper.json"
        original = json.dumps(self.old)
        index.write_text(original)
        command = [sys.executable, "-B", str(SCRIPT), "--tex", str(self.tex),
                   "--aux", str(self.aux), "--index", str(index)]
        result = subprocess.run([*command, "--dry-run"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(index.read_text(), original)
        self.aux.write_text("")
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(index.read_text(), original)


if __name__ == "__main__":
    unittest.main()
