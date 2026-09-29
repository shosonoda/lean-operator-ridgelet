#!/usr/bin/env python3
"""Synchronize manuscript metadata without changing Lean statements or declaration names.

Recursively read literal LaTeX input/include files and auxiliary input files. Refuse missing
numbers, duplicate labels, input cycles, empty inventories, and unapproved inventory changes.
Existing item metadata is preserved, including Lean associations and formalization notes.
Use --dry-run to validate a manuscript before writing the index. Paths supplied on the command
line are not recorded: the public index uses the logical manuscript name main.tex by default.
"""
from __future__ import annotations

import argparse
import datetime
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "comparator" / "paper.json"
KINDS = {"thm": "theorem", "prop": "proposition", "lem": "lemma", "cor": "corollary",
         "ex": "example", "dfn": "definition"}
PREFIXES = {"definition": "def", **{v: k for k, v in KINDS.items() if k != "dfn"}}
BEGIN_RE = re.compile(r"\\begin\{(thm|prop|lem|cor|ex|dfn)\}(?:\[(?P<title>[^\]]*)\])?")
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
NEWLABEL_RE = re.compile(r"\\newlabel\{([^}@]*)\}\{\{([^}]*)\}\{([^}]*)\}")
INPUT_RE = re.compile(r"\\(?:input|include)\s*\{([^{}]+)\}")
AUX_INPUT_RE = re.compile(r"\\@input\s*\{([^{}]+)\}")
NAMING = ("OperatorRidgelet.Paper.<kind>_<number>[_<part>] with dots in manuscript numbers "
          "replaced by underscores; source labels remain stable identifiers")


def strip_comments(text: str) -> str:
    """Remove unescaped TeX comments, preserving line boundaries and escaped percent signs."""
    return re.sub(r"(?<!\\)(?:\\\\)*%[^\n]*", lambda m: m[0].split("%", 1)[0], text)


def expanded_source(path: Path, pattern: re.Pattern = INPUT_RE, suffix: str = ".tex",
                    root: Path | None = None, stack: tuple[Path, ...] = ()) -> str:
    """Expand literal includes in order; resolve paths from the entry document directory."""
    path = path.resolve()
    root = root or path.parent
    if path in stack:
        raise ValueError(f"input cycle at {path.name}")
    text = strip_comments(path.read_text(encoding="utf-8"))

    def expand(match: re.Match) -> str:
        name = match[1].strip()
        if "\\" in name or "#" in name:
            raise ValueError(f"nonliteral input in {path.name}: {name}")
        rel = Path(name)
        if not rel.suffix:
            rel = rel.with_suffix(suffix)
        # TeX normally resolves from its working directory. Relative-to-includer fallback
        # also supports self-contained source trees assembled with that convention.
        candidates = (root / rel, path.parent / rel)
        target = next((p for p in candidates if p.is_file()), None)
        if target is None:
            raise ValueError(f"missing input in {path.name}: {name}")
        return expanded_source(target, pattern, suffix, root, (*stack, path))

    return pattern.sub(expand, text)


def read_items(tex: Path) -> list[dict]:
    text = expanded_source(tex)
    items = []
    labels = set()
    for match in BEGIN_RE.finditer(text):
        end = text.find(r"\end{" + match[1] + "}", match.end())
        if end < 0:
            raise ValueError(f"unclosed {match[1]} environment")
        found = LABEL_RE.search(text, match.end(), end)
        if found is None:
            raise ValueError(f"unlabelled {match[1]} environment")
        label = found[1]
        if label in labels:
            raise ValueError(f"duplicate manuscript label: {label}")
        labels.add(label)
        title = (match["title"] or "").strip()
        title = re.sub(r"\\texorpdfstring\{([^}]*)\}\{[^}]*\}", r"\1", title)
        items.append({"label": label, "kind": KINDS[match[1]], "title": title})
    if not items:
        raise ValueError("no manuscript items found; refusing to erase the index")
    return items


def read_numbers(aux: Path) -> dict[str, tuple[str, str]]:
    out = {}
    for match in NEWLABEL_RE.finditer(expanded_source(aux, AUX_INPUT_RE, ".aux")):
        if match[1] in out:
            raise ValueError(f"duplicate auxiliary label: {match[1]}")
        out[match[1]] = (match[2], match[3])
    return out


def synchronize(old: dict, tex: Path, aux: Path, *, version: str | None = None,
                logical_file: str = "main.tex", allow_item_changes: bool = False) -> dict:
    """Return validated metadata; callers choose whether to persist it."""
    parsed = read_items(tex)
    numbers = read_numbers(aux)
    keep = {it["label"]: it for it in old.get("items", [])}
    if len(keep) != len(old.get("items", [])):
        raise ValueError("duplicate labels in the existing index")
    labels = {it["label"] for it in parsed}
    added, dropped = labels - keep.keys(), keep.keys() - labels
    if (added or dropped) and not allow_item_changes:
        raise ValueError(f"inventory changed: added {sorted(added)}, dropped {sorted(dropped)}; "
                         "review it and use --allow-item-changes explicitly")
    items = []
    node_labels = set()
    for item in parsed:
        label = item["label"]
        number, page = numbers.get(label, ("", ""))
        if not re.fullmatch(r"(?:[A-Z]|[1-9][0-9]*)\.[1-9][0-9]*", number):
            raise ValueError(f"missing or invalid auxiliary number for {label}: {number!r}")
        if not page or page == "?":
            raise ValueError(f"missing auxiliary page for {label}")
        previous = keep.get(label, {})
        if previous and previous["kind"] != item["kind"]:
            raise ValueError(f"kind changed for {label}; review its Lean correspondence first")
        node = f"{PREFIXES[item['kind']]}:{number}"
        if node in node_labels:
            raise ValueError(f"duplicate numbered Blueprint label: {node}")
        node_labels.add(node)
        items.append({**previous, **item, "number": number, "page": page,
                      "blueprint_label": node, "lean": previous.get("lean", []),
                      "note": previous.get("note", "")})
    if Path(logical_file).name != logical_file or "\\" in logical_file:
        raise ValueError("--logical-file must be a filename, not a local path")
    manuscript = old.get("manuscript", {})
    return {**old, "manuscript": {**manuscript, "file": logical_file,
             "version": version or manuscript.get("version", "numbered manuscript"),
             "synced": datetime.date.today().isoformat()}, "naming": NAMING, "items": items}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tex", required=True, type=Path)
    parser.add_argument("--aux", required=True, type=Path)
    parser.add_argument("--index", type=Path, default=PAPER)
    parser.add_argument("--version", help="neutral version description (default: preserve)")
    parser.add_argument("--logical-file", default="main.tex")
    parser.add_argument("--allow-item-changes", action="store_true")
    parser.add_argument("--dry-run", action="store_true", help="validate without writing")
    args = parser.parse_args()
    try:
        old = json.loads(args.index.read_text(encoding="utf-8"))
        data = synchronize(old, args.tex, args.aux, version=args.version,
                           logical_file=args.logical_file,
                           allow_item_changes=args.allow_item_changes)
        if not args.dry_run:
            args.index.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                                  encoding="utf-8")
    except (OSError, ValueError, KeyError) as error:
        print(f"sync aborted: {error}", file=sys.stderr)
        return 1
    action = "validated (dry run)" if args.dry_run else "written"
    print(f"{len(data['items'])} manuscript items {action}; Lean associations preserved")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
