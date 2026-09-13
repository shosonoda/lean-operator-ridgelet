#!/usr/bin/env python3
"""Generate the Blueprint chapter `Chapters/Comparator.lean` (the comparator review).

The chapter lets a reader compare, inside the published Blueprint, the informal statement of every
manuscript item (its Blueprint node) with the Lean statement that comparator checks (the `Challenge`
declaration) and see the comparator status.  Everything is derived from the data of the
`OperatorRidgelet` project, in manuscript order:

- `comparator/paper.json`: the items (label, kind, number, title, Lean names, notes);
- `comparator/config.json`: `theorem_names`, the declarations verified by comparator;
- `Challenge/*.lean`: the statements with proof `sorry` (docstring and statement are copied
  verbatim, the `sorry` line is dropped);
- the library, to recognize the Lean names that are definitions.

The status vocabulary and the summary counts are those of `OperatorRidgelet/scripts/status.py`
(`STATUS.md`); the logic is duplicated here on purpose so that the two never disagree.

Usage: `scripts/gen-comparator-chapter.py` writes the chapter; `--check` exits 1 when the committed
chapter is stale (run by `.github/workflows/badges.yml`).  `scripts/ci-pages.sh` runs the generator
before `lake exe vbp build`.  The output is deterministic.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

BLUEPRINT = Path(__file__).resolve().parent.parent
ROOT = BLUEPRINT.parent
LIB = ROOT / "OperatorRidgelet"
CHAPTERS = BLUEPRINT / "OperatorRidgeletBlueprint" / "Chapters"
OUTPUT = CHAPTERS / "Comparator.lean"
REPOSITORY = "shosonoda/lean-operator-ridgelet"
GITHUB_BLOB = f"https://github.com/{REPOSITORY}/blob/main"

sys.path.insert(0, str(LIB / "scripts"))
from leanparse import parse_tree  # noqa: E402

HEADER_RE = re.compile(
    r"^(?P<kw>theorem|lemma|def|noncomputable def|abbrev|noncomputable abbrev|structure|class|inductive)"
    r"\s+(?P<name>[\w.']+)")
MODIFIER_RE = re.compile(r"^(omit|include|set_option|open|attribute|@\[)")
KIND_TITLES = {
    "definition": "Definition", "lemma": "Lemma", "theorem": "Theorem", "proposition": "Proposition",
    "corollary": "Corollary", "example": "Example",
}

# --------------------------------------------------------------------------------------------
# Verso markup helpers
# --------------------------------------------------------------------------------------------

# Characters that open inline markup in Verso (see `inlineTextChar` in Verso's parser).  `\` escapes
# the next character.  `$` and `!` are escaped everywhere, which is harmless.
VERSO_SPECIAL = "\\*_[]{}`$!"


def esc(text: str) -> str:
    """Escape `text` for a Verso inline context, collapsing whitespace to single spaces."""
    text = re.sub(r"\s+", " ", text)
    return "".join("\\" + c if c in VERSO_SPECIAL else c for c in text)


def code(text: str) -> str:
    """Verso inline code; the fence is longer than any backtick run inside."""
    longest = max((len(m.group(0)) for m in re.finditer(r"`+", text)), default=0)
    fence = "`" * (longest + 1)
    pad = " " if text.startswith("`") or text.endswith("`") else ""
    return f"{fence}{pad}{text}{pad}{fence}"


def note_inline(note: str) -> str:
    """Render a `paper.json` note: backtick spans become inline code, the rest is escaped text."""
    parts = note.split("`")
    if len(parts) % 2 == 0:  # unbalanced backticks: show everything literally
        return esc(note)
    out = []
    for i, part in enumerate(parts):
        out.append(code(part) if i % 2 else esc(part))
    return "".join(out)


def code_block(source: str) -> str:
    """A plain fenced block (`Block.code`, rendered verbatim and never elaborated by Verso)."""
    longest = 0
    for line in source.split("\n"):
        m = re.match(r"\s*(`+)", line)
        if m:
            longest = max(longest, len(m.group(1)))
    fence = "`" * max(3, longest + 1)
    return f"{fence}\n{source}\n{fence}"


# --------------------------------------------------------------------------------------------
# Sources
# --------------------------------------------------------------------------------------------

def challenge_sources(path: Path) -> dict[str, tuple[int, str]]:
    """Map the short name of each declaration of a `Challenge` file to (line, source), where the
    source is the declaration exactly as in the file (preceding `... in` modifiers, docstring,
    statement) without the `sorry` proof line."""
    lines = path.read_text(encoding="utf-8").split("\n")
    out: dict[str, tuple[int, str]] = {}
    for i, line in enumerate(lines):
        m = HEADER_RE.match(line)
        if not m:
            continue
        # End: the `sorry` line, or the next top-level item if there is none.
        j = i + 1
        while j < len(lines):
            s = lines[j]
            if s.strip() == "sorry":
                break
            if s and not s[0].isspace() and (HEADER_RE.match(s) or MODIFIER_RE.match(s)
                                             or s.startswith("/-") or s.startswith("end ")):
                print(f"warning: {path.name}:{i + 1}: `{m.group('name')}` has no `sorry` line",
                      file=sys.stderr)
                break
            j += 1
        end = j
        while end > i and not lines[end - 1].strip():
            end -= 1
        # Start: the docstring, then any `... in` modifiers (possibly spanning several lines).
        start = i
        if start > 0 and lines[start - 1].rstrip().endswith("-/"):
            k = start - 1
            while k > 0 and not lines[k].lstrip().startswith("/--"):
                k -= 1
            if lines[k].lstrip().startswith("/--"):
                start = k
        while start > 0 and lines[start - 1].rstrip().endswith(" in"):
            k = start - 1
            while k > 0 and not MODIFIER_RE.match(lines[k]):
                k -= 1
            start = k
        block = "\n".join(lines[start:end])
        if block.rstrip().endswith(":= sorry"):
            block = block.rstrip()[: -len("sorry")].rstrip()
        short = m.group("name").rsplit(".", 1)[-1]
        if short in out:
            print(f"warning: {path.name}: duplicate declaration `{short}`", file=sys.stderr)
        out[short] = (start + 1, block)
    return out


def library_line(path: Path, short: str) -> int | None:
    """Line of the header of the declaration `short` in the raw file, if found."""
    for i, line in enumerate(path.read_text(encoding="utf-8").split("\n")):
        m = HEADER_RE.match(line)
        if m and m.group("name").rsplit(".", 1)[-1] == short:
            return i + 1
    return None


def blueprint_nodes() -> dict[str, list[str]]:
    """Labels of the Blueprint nodes of the hand-written chapters, with their Lean associations."""
    nodes: dict[str, list[str]] = {}
    for f in sorted(CHAPTERS.glob("*.lean")):
        if f == OUTPUT:
            continue
        text = f.read_text(encoding="utf-8")
        for m in re.finditer(r'^:::(?P<kind>\w+)\s+"(?P<label>[^"]+)"(?P<args>[^\n]*)', text, re.M):
            if m.group("kind") == "proof":
                continue
            lean = re.search(r'\(lean := "([^"]*)"\)', m.group("args"))
            names = [n.strip() for n in lean.group(1).split(",")] if lean else []
            nodes.setdefault(m.group("label"), []).extend(names)
    return nodes


# --------------------------------------------------------------------------------------------
# Generation
# --------------------------------------------------------------------------------------------

INTRO = """\
This chapter is generated by `OperatorRidgeletBlueprint/scripts/gen-comparator-chapter.py` from
`comparator/paper.json`, `comparator/config.json`, and the `Challenge` sources of the
`OperatorRidgelet` project; it is regenerated on every build of the site and is never edited by
hand. It exists so that the formal statements can be reviewed against the manuscript without
leaving the Blueprint: for every manuscript item it shows, in manuscript order, the statement of
each of its Lean declarations exactly as it stands in `Challenge`, a link to the Blueprint node
that carries the informal statement, the modelling note of the manuscript index, and the
comparator status of each declaration.

*The comparator scheme.* Every theorem, proposition, lemma, corollary, and example of the
manuscript is a theorem `OperatorRidgelet.Paper.<kind>_<label>[_<part>]` (multi-part results are
split per part), stated twice with identical text: in the `Challenge` library with proof `sorry`,
and in `OperatorRidgelet.Paper`, imported by `Solution`, with the real proof. `Challenge` imports
only the `sorry`-free definition modules of the library, never `OperatorRidgelet.Paper`, so the
same names can be proved in `Solution`. The file `comparator/config.json` lists under
`theorem_names` the declarations whose proofs are complete, and `scripts/comparator-check.sh`
runs [comparator](https://github.com/leanprover/comparator) on the two libraries. A declaration
in that list is *verified*: comparator has checked that the `Solution` statement is identical to
the `Challenge` statement, that the proof contains no `sorry`, that it depends on no axioms other
than `propext`, `Quot.sound`, and `Classical.choice`, and it has replayed the proof through the
Lean kernel. Definitions are not verified by comparator; they are part of the trusted statement
and are reviewed through the Lean panel of the Blueprint node.

*How to review an item.* Read the informal statement in the Blueprint node (the link at the top
of each item), then the Lean statement in the code block, which is the `Challenge` declaration
with its docstring, copied verbatim with only the `sorry` line removed, and check that the two
say the same thing; the note records how the manuscript's objects are encoded. The Blueprint
node's Lean panel shows the same declaration as elaborated in `OperatorRidgelet.Paper`, with
hover information and the proof status read from the code. A declaration marked *verified by
comparator* is settled; one marked *statement only* is formalized but its proof is pending.
"""

STATUS_LEGEND = """\
The status of an item is that of `STATUS.md`: *verified* when every Lean theorem of the item is
in `theorem_names`; *partial k/n* when `k` of its `n` Lean theorems are; *stated* when all of
its Lean names exist (theorems in `Challenge`, definitions in the library) but none is verified;
*defined* when its Lean names are all definitions in the library, so that there is nothing for
comparator to check; and — when some Lean name is not yet stated. The full table, with the
consistency warnings of the generator, is
[`STATUS.md`]({github}/STATUS.md) in the repository.
"""


def section_heading(number: str) -> str:
    part = number.split(".", 1)[0]
    return f"Appendix {part}" if part.isalpha() else f"Manuscript Section {part}"


def generate() -> str:
    paper = json.loads((LIB / "comparator" / "paper.json").read_text(encoding="utf-8"))
    config = json.loads((LIB / "comparator" / "config.json").read_text(encoding="utf-8"))
    verified = set(config["theorem_names"])
    challenge = parse_tree(LIB / "Challenge", LIB / "Challenge.lean")
    library = parse_tree(LIB / "OperatorRidgelet")
    sources = {f: challenge_sources(f) for f in sorted((LIB / "Challenge").rglob("*.lean"))}
    nodes = blueprint_nodes()

    def is_definition(n: str) -> bool:
        d = library.get(n)
        return d is not None and d.kind not in ("theorem", "lemma")

    def is_stated(n: str) -> bool:
        return n in challenge or is_definition(n)

    # Summary counts, exactly as in status.py.
    rows = []
    n_stated = n_proved = n_partial = n_new = n_restated = 0
    for it in paper["items"]:
        names = it.get("lean", [])
        stated = bool(names) and all(is_stated(n) for n in names)
        thm_names = [n for n in names if not is_definition(n)]
        proved_n = sum(1 for n in thm_names if n in verified)
        if stated:
            n_stated += 1
        if names and stated and proved_n == len(thm_names):
            n_proved += 1
        elif proved_n:
            n_partial += 1
        status = ("defined" if names and stated and not thm_names else
                  "verified" if names and stated and proved_n == len(thm_names) else
                  f"partial {proved_n}/{len(thm_names)}" if proved_n else
                  "stated" if stated else "—")
        revision = it.get("revision")
        if revision == "new":
            n_new += 1
            status = "not formalized" if not names else status
        elif revision == "restated":
            n_restated += 1
            status = f"{status}, manuscript restated"
        rows.append((it, names, thm_names, proved_n, status))
    total = len(paper["items"])
    ms = paper.get("manuscript", {})

    out: list[str] = []
    w = out.append
    w("-- Generated by scripts/gen-comparator-chapter.py; do not edit.  Regenerate with")
    w("--   python3 OperatorRidgeletBlueprint/scripts/gen-comparator-chapter.py")
    w("import Verso")
    w("import VersoManual")
    w("import VersoBlueprint")
    w("")
    w("open Verso.Genre")
    w("open Verso.Genre.Manual")
    w("open Informal")
    w("")
    w('#doc (Manual) "Comparator review of the Challenge statements" =>')
    w("%%%")
    w('file := "comparator"')
    w("%%%")
    w("")
    w(INTRO)
    w("# Summary")
    w("")
    w(f"Manuscript {code(ms.get('file', 'main.tex'))}, version {esc(str(ms.get('version', '?')))} "
      f"(numbers synced {esc(str(ms.get('synced', '?')))}). "
      f"Verified declarations in {code('theorem_names')}: {len(verified)}.")
    w("")
    w(":::table +header")
    w("*")
    w("  * Items")
    w("  * Stated (theorem in `Challenge`, or definition in the library)")
    w("  * Verified by comparator (or pure definition)")
    w("  * Partially verified")
    w("*")
    w(f"  * {total}")
    w(f"  * {n_stated}")
    w(f"  * {n_proved}")
    w(f"  * {n_partial}")
    w(":::")
    w("")
    if n_new or n_restated:
        w(f"Of these, {n_new} item(s) are new in this manuscript revision and not yet formalized, "
          f"and {n_restated} item(s) whose Lean statements are verified were restated in the "
          "manuscript after those statements were written, so their status refers to the earlier "
          "statement.  Both are marked in the status line of the item and explained in its "
          "formalization note.")
        w("")
    conventions = ms.get("conventions")
    if conventions:
        w(f"Conventions. {esc(str(conventions))}")
        w("")
    w(STATUS_LEGEND.format(github=GITHUB_BLOB))

    current_section = None
    for it, names, thm_names, proved_n, status in rows:
        section = section_heading(it["number"])
        if section != current_section:
            current_section = section
            w(f"# {section}")
            w("")
        kind = KIND_TITLES.get(it["kind"], it["kind"].capitalize())
        w(f"## {kind} {esc(it['number'])} — {esc(it['title'])} ({code(it['label'])})")
        w("")
        label = it["label"]
        if label in nodes:
            node_ref = f"Blueprint node: {{bpref \"{label}\"}}[]."
        else:
            node_ref = "Blueprint node: none yet."
        base_status = status.removesuffix(", manuscript restated")
        if status == "not formalized":
            detail = "new in this manuscript revision, no Lean statement yet"
        elif base_status == "verified":
            detail = (f"all {len(thm_names)} Lean theorems verified" if len(thm_names) != 1
                      else "its Lean theorem is verified")
        elif base_status.startswith("partial"):
            detail = f"{proved_n} of {len(thm_names)} Lean theorems verified"
        elif base_status == "stated":
            detail = "formalized, no part verified yet"
        elif base_status == "defined":
            detail = "definitions only, nothing for comparator to check"
        else:
            detail = "not every Lean name is stated yet"
        if status.endswith(", manuscript restated"):
            detail += "; the manuscript statement changed after the Lean statement was written"
        w(f"{node_ref} Status: *{esc(status)}* ({detail}).")
        w("")
        if it.get("note"):
            w(f"Formalization note. {note_inline(it['note'])}")
            w("")
        node_names = nodes.get(label, [])
        for n in names:
            if label in nodes and n not in node_names:
                print(f"warning: `{n}` of {label} is not a Lean association of its Blueprint node",
                      file=sys.stderr)
            if n in challenge:
                d = challenge[n]
                short = n.rsplit(".", 1)[-1]
                line, src = sources[d.file][short]
                rel = d.file.relative_to(ROOT).as_posix()
                w(f"{code(n)}, {esc(d.kind)} in "
                  f"[{code(d.file.relative_to(LIB).as_posix())}]({GITHUB_BLOB}/{rel}#L{line}):")
                w("")
                w(code_block(src))
                w("")
                if n in verified:
                    w("Status: *verified by comparator*.")
                else:
                    w("Status: *statement only (proof pending)*.")
            elif is_definition(n):
                d = library[n]
                short = n.rsplit(".", 1)[-1]
                line = library_line(d.file, short)
                rel = d.file.relative_to(ROOT).as_posix()
                anchor = f"#L{line}" if line else ""
                w(f"{code(n)}: definition in the library ({esc(d.kind)} in "
                  f"[{code(d.file.relative_to(LIB).as_posix())}]({GITHUB_BLOB}/{rel}{anchor})); "
                  f"see the Lean panel of the Blueprint node above.")
            else:
                w(f"{code(n)}: not yet stated.")
            w("")
    return "\n".join(out).rstrip("\n") + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if the committed chapter differs from the generated one")
    args = ap.parse_args()
    text = generate()
    if args.check:
        current = OUTPUT.read_text(encoding="utf-8") if OUTPUT.exists() else None
        if current != text:
            print(f"{OUTPUT.relative_to(ROOT)} is stale; run {Path(__file__).relative_to(ROOT)}",
                  file=sys.stderr)
            return 1
        print(f"{OUTPUT.relative_to(ROOT)} is up to date")
        return 0
    OUTPUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUTPUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
