"""Minimal, regex-level parsing of the Lean files of this project.

Only the shapes used in `Challenge/` and `OperatorRidgelet/Paper/` are supported: top-level
`namespace`/`end`, `theorem NAME <binders> : <type> := <proof>` declarations, docstrings, and
line/block comments.  Fully qualified and namespace-relative names are both resolved.
"""
from __future__ import annotations
import re
from dataclasses import dataclass, field
from pathlib import Path

DECL_RE = re.compile(r"^(?P<kw>theorem|lemma|def|noncomputable def|abbrev|structure)\s+(?P<name>[\w.']+)", re.M)
NS_RE = re.compile(r"^(namespace|end)\s+([\w.']+)\s*$", re.M)


def strip_comments(text: str) -> str:
    """Remove `--` line comments and `/- ... -/` block comments (docstrings included)."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth += 1; j += 2
                elif text.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            out.append(" "); i = j
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


@dataclass
class Decl:
    name: str
    kind: str
    statement: str  # from the keyword to the first top-level `:=`, whitespace-normalized
    body: str       # everything after that `:=` up to the next declaration
    file: Path
    line: int


def split_statement(chunk: str) -> tuple[str, str]:
    """Split a declaration chunk at the first `:=` outside brackets."""
    depth = 0
    for i, c in enumerate(chunk):
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth = max(0, depth - 1)
        elif depth == 0 and chunk.startswith(":=", i):
            return chunk[:i], chunk[i + 2:]
    return chunk, ""


def parse_file(path: Path) -> list[Decl]:
    raw = path.read_text(encoding="utf-8")
    text = strip_comments(raw)
    decls: list[Decl] = []
    # namespace bookkeeping by position
    ns_events = [(m.start(), m.group(1), m.group(2)) for m in NS_RE.finditer(text)]
    matches = list(DECL_RE.finditer(text))
    for k, m in enumerate(matches):
        start = m.start()
        end = matches[k + 1].start() if k + 1 < len(matches) else len(text)
        # cut the chunk at a namespace/end line if one occurs before the next declaration
        for pos, _, _ in ns_events:
            if start < pos < end:
                end = pos
                break
        stack: list[str] = []
        for pos, kw, name in ns_events:
            if pos > start:
                break
            if kw == "namespace":
                stack.append(name)
            elif stack and stack[-1] == name:
                stack.pop()
        chunk = text[start:end]
        stmt, body = split_statement(chunk)
        name = m.group("name")
        if stack and not name.startswith("OperatorRidgelet."):
            name = ".".join(stack) + "." + name
        stmt_norm = " ".join(stmt.split())
        decls.append(Decl(name, m.group("kw"), stmt_norm, body, path, text.count("\n", 0, start) + 1))
    return decls


def parse_tree(root: Path, root_file: Path | None = None) -> dict[str, Decl]:
    files = sorted(root.rglob("*.lean")) if root.is_dir() else []
    if root_file and root_file.exists():
        files.append(root_file)
    out: dict[str, Decl] = {}
    for f in files:
        for d in parse_file(f):
            out[d.name] = d
    return out
