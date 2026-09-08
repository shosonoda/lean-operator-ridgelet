#!/usr/bin/env python3
"""Update `comparator/paper.json` from the manuscript.

Reads the theorem-like environments (thm, prop, lem, cor, ex, dfn) and their labels from
`main.tex`, and the current numbering from `main.aux`.  Existing `lean` lists and notes are
preserved; items are ordered as in the manuscript.

Usage: scripts/sync-paper-numbers.py --tex PATH/main.tex --aux PATH/main.aux [--commit SHA]
"""
from __future__ import annotations
import argparse, datetime, json, re, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "comparator" / "paper.json"
KINDS = {"thm": "theorem", "prop": "proposition", "lem": "lemma", "cor": "corollary",
         "ex": "example", "dfn": "definition"}
BEGIN_RE = re.compile(r"\\begin\{(thm|prop|lem|cor|ex|dfn)\}(?:\[(?P<title>[^\]]*)\])?")
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
NEWLABEL_RE = re.compile(r"\\newlabel\{([^}@]*)\}\{\{([^}]*)\}\{([^}]*)\}")


def read_items(tex: Path) -> list[dict]:
    text = tex.read_text(encoding="utf-8")
    items = []
    for m in BEGIN_RE.finditer(text):
        tail = text[m.end(): m.end() + 400]
        lab = LABEL_RE.search(tail)
        if not lab:
            continue
        title = (m.group("title") or "").strip()
        title = re.sub(r"\\texorpdfstring\{([^}]*)\}\{[^}]*\}", r"\1", title)
        items.append({"label": lab.group(1), "kind": KINDS[m.group(1)], "title": title})
    return items


def read_numbers(aux: Path) -> dict[str, tuple[str, str]]:
    out = {}
    for m in NEWLABEL_RE.finditer(aux.read_text(encoding="utf-8")):
        out[m.group(1)] = (m.group(2), m.group(3))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tex", required=True, type=Path)
    ap.add_argument("--aux", required=True, type=Path)
    ap.add_argument("--commit", default=None)
    args = ap.parse_args()
    old = json.loads(PAPER.read_text()) if PAPER.exists() else {"items": []}
    keep = {it["label"]: it for it in old.get("items", [])}
    numbers = read_numbers(args.aux)
    items = []
    for it in read_items(args.tex):
        num, page = numbers.get(it["label"], ("?", "?"))
        prev = keep.get(it["label"], {})
        items.append({
            "label": it["label"], "kind": it["kind"], "number": num, "page": page,
            "title": it["title"],
            "lean": prev.get("lean", []),
            "note": prev.get("note", ""),
        })
    commit = args.commit
    if commit is None:
        try:
            commit = subprocess.run(["git", "-C", str(args.tex.parent), "rev-parse", "--short", "HEAD"],
                                    capture_output=True, text=True, check=True).stdout.strip()
        except Exception:
            commit = "unknown"
    data = {
        "manuscript": {"file": args.tex.name, "commit": commit,
                       "synced": datetime.date.today().isoformat()},
        "naming": "OperatorRidgelet.Paper.<kind>_<label>[_<part>] where <label> drops the prefix and uses _ for -",
        "items": items,
    }
    PAPER.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    dropped = set(keep) - {it["label"] for it in items}
    print(f"{len(items)} items written to {PAPER.relative_to(ROOT)}; dropped labels: {sorted(dropped) or 'none'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
