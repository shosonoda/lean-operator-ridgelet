#!/usr/bin/env python3
"""Check that every statement in `OperatorRidgelet/Paper/` has an identical twin in `Challenge/`.

comparator is the authoritative check (it compares kernel-level types); this script is a fast
textual pre-check that runs without building.  Exit status 1 on any mismatch.
"""
from __future__ import annotations
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from leanparse import parse_tree  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    challenge = parse_tree(ROOT / "Challenge", ROOT / "Challenge.lean")
    paper = parse_tree(ROOT / "OperatorRidgelet" / "Paper", ROOT / "OperatorRidgelet" / "Paper.lean")
    challenge = {k: v for k, v in challenge.items() if v.kind in ("theorem", "lemma")}
    paper = {k: v for k, v in paper.items() if v.kind in ("theorem", "lemma")}
    ok = True
    for name, d in sorted(paper.items()):
        c = challenge.get(name)
        if c is None:
            print(f"MISSING in Challenge: {name}  ({d.file.relative_to(ROOT)}:{d.line})"); ok = False
        elif c.statement != d.statement:
            print(f"MISMATCH: {name}\n  Challenge: {c.statement}\n  Paper:     {d.statement}"); ok = False
    for name, c in sorted(challenge.items()):
        if name not in paper:
            print(f"MISSING in Paper: {name}  ({c.file.relative_to(ROOT)}:{c.line})"); ok = False
        if "sorry" not in c.body:
            print(f"WARNING: Challenge proof of {name} is not `sorry`"); ok = False
    print(f"{len(paper)} paper statements, {len(challenge)} challenge statements, {'OK' if ok else 'PROBLEMS FOUND'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
