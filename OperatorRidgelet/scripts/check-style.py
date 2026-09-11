#!/usr/bin/env python3
"""Check library line lengths and declaration documentation after `lake build`."""
from pathlib import Path
import subprocess
import sys
import tempfile


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    long_lines = []
    for path in sorted((root / "OperatorRidgelet").rglob("*.lean")):
        for line, text in enumerate(path.read_text().splitlines(), 1):
            if len(text) > 100:
                long_lines.append(f"{path.relative_to(root)}:{line}: {len(text)} characters")
    if long_lines:
        print("\n".join(long_lines), file=sys.stderr)
        return 1
    # Restrict the environment linters to our modules; vendored sources stay unchanged.
    with tempfile.TemporaryDirectory(prefix="operator-ridgelet-style-") as tmp:
        audit = Path(tmp) / "StyleAudit.lean"
        audit.write_text(
            "import OperatorRidgelet\n"
            "import Batteries.Tactic.Lint\n\n"
            "#lint only docBlame docBlameThm in OperatorRidgelet\n"
        )
        return subprocess.run(["lake", "env", "lean", str(audit)], cwd=root).returncode


if __name__ == "__main__":
    sys.exit(main())
