from __future__ import annotations

from pathlib import Path
import sys
import unittest

from scripts.blueprint_harness_validation import (
    SiteValidationCheck,
    UV_CACHE_DIR,
    browser_test_command,
    panel_regression_command,
    resolve_package_relative_path,
    run_site_validation_checks,
)
from scripts.blueprint_harness_utils import StepFailure
import scripts.blueprint_harness_validation as validation_mod


PACKAGE_ROOT = Path(__file__).resolve().parents[2]


class HarnessValidationCommandTests(unittest.TestCase):
    def test_resolve_package_relative_path_preserves_absolute_paths(self) -> None:
        self.assertEqual(
            resolve_package_relative_path(PACKAGE_ROOT, "/tmp/check.py"),
            Path("/tmp/check.py"),
        )
        self.assertEqual(
            resolve_package_relative_path(PACKAGE_ROOT, "tests/browser"),
            PACKAGE_ROOT / "tests/browser",
        )

    def test_panel_regression_command_targets_site_dir(self) -> None:
        site_dir = Path("/tmp/out/test-blueprints/runtime-showcase/html-multi")

        self.assertEqual(
            panel_regression_command(PACKAGE_ROOT, "tests/harness/runtime/check.py", site_dir),
            [
                sys.executable,
                str(PACKAGE_ROOT / "tests/harness/runtime/check.py"),
                "--site-dir",
                str(site_dir),
            ],
        )

    def test_browser_test_command_uses_python_pytest_without_uv(self) -> None:
        site_dir = Path("/tmp/out/test-blueprints/runtime-showcase/html-multi")
        original_which = validation_mod.shutil.which
        try:
            validation_mod.shutil.which = lambda _name: None

            self.assertEqual(
                browser_test_command(PACKAGE_ROOT, "tests/browser", site_dir, ["-k", "preview"]),
                [
                    sys.executable,
                    "-m",
                    "pytest",
                    str(PACKAGE_ROOT / "tests/browser"),
                    "-q",
                    "--browser",
                    "chromium",
                    "--site-dir",
                    str(site_dir),
                    "-k",
                    "preview",
                ],
            )
        finally:
            validation_mod.shutil.which = original_which

    def test_browser_test_command_uses_uv_project_when_available(self) -> None:
        site_dir = Path("/tmp/out/test-blueprints/runtime-showcase/html-multi")
        original_which = validation_mod.shutil.which
        try:
            validation_mod.shutil.which = lambda _name: "/usr/bin/uv"

            self.assertEqual(
                browser_test_command(PACKAGE_ROOT, "tests/browser", site_dir, []),
                [
                    "env",
                    f"UV_CACHE_DIR={UV_CACHE_DIR}",
                    "uv",
                    "run",
                    "--project",
                    str(PACKAGE_ROOT / "tests/browser"),
                    "--extra",
                    "test",
                    "python",
                    "-m",
                    "pytest",
                    str(PACKAGE_ROOT / "tests/browser"),
                    "-q",
                    "--browser",
                    "chromium",
                    "--site-dir",
                    str(site_dir),
                ],
            )
        finally:
            validation_mod.shutil.which = original_which

    def test_run_site_validation_checks_runs_panel_and_browser_checks(self) -> None:
        check = SiteValidationCheck(
            label="runtime-showcase",
            site_dir=Path("/tmp/out/runtime-showcase/html-multi"),
            panel_regression_script="tests/harness/runtime/check.py",
            browser_tests_path="tests/browser",
        )
        original_run = validation_mod.run_capturing_failure
        calls: list[tuple[str, list[str], Path]] = []
        try:
            validation_mod.run_capturing_failure = (
                lambda step, command, cwd: calls.append((step, command, cwd)) or None
            )

            failures = run_site_validation_checks(PACKAGE_ROOT, [check], ["-k", "preview"])
        finally:
            validation_mod.run_capturing_failure = original_run

        self.assertEqual(failures, [])
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0][0], "runtime-showcase panel regression")
        self.assertIn("tests/harness/runtime/check.py", calls[0][1][1])
        self.assertEqual(calls[1][0], "runtime-showcase browser tests")
        self.assertIn("-k", calls[1][1])
        self.assertIn("preview", calls[1][1])
        self.assertEqual(calls[0][2], PACKAGE_ROOT)
        self.assertEqual(calls[1][2], PACKAGE_ROOT)

    def test_run_site_validation_checks_stops_on_first_failure(self) -> None:
        check = SiteValidationCheck(
            label="runtime-showcase",
            site_dir=Path("/tmp/out/runtime-showcase/html-multi"),
            panel_regression_script="tests/harness/runtime/check.py",
            browser_tests_path="tests/browser",
        )
        original_run = validation_mod.run_capturing_failure
        calls: list[str] = []
        try:
            validation_mod.run_capturing_failure = (
                lambda step, _command, cwd: calls.append(step) or StepFailure(step, "failed")
            )

            failures = run_site_validation_checks(PACKAGE_ROOT, [check], [], stop_on_first_failure=True)
        finally:
            validation_mod.run_capturing_failure = original_run

        self.assertEqual(calls, ["runtime-showcase panel regression"])
        self.assertEqual(failures, [StepFailure("runtime-showcase panel regression", "failed")])


if __name__ == "__main__":
    unittest.main()
