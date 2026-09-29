#!/usr/bin/env python3
"""Check rendered manuscript numbering, kinds, and cross-chapter proof links."""

import json
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "_out/site/html-multi"
INDEX = ROOT.parent / "OperatorRidgelet/comparator/paper.json"


def plain(label):
    return label.removeprefix("«").removesuffix("»")


def check_link(href):
    url = urlsplit(href)
    assert not url.scheme and not url.netloc, href
    path = SITE / unquote(url.path)
    if path.is_dir():
        path /= "index.html"
    assert path.is_file(), f"Missing page: {href}"
    if url.fragment:
        assert f'id="{unquote(url.fragment)}"' in path.read_text(), href


def main():
    items = json.loads(INDEX.read_text())["items"]
    manifest = json.loads((SITE / "-verso-data/blueprint-manifest.json").read_text())
    nodes = manifest["graphs"][0]["nodes"]
    by_label = {plain(node["label"]): node for node in nodes}
    assert len(by_label) == len(nodes), "Duplicate graph labels"
    previews = {
        (plain(entry["label"]), entry["facet"]): entry
        for entry in manifest["previews"] if entry["targetKind"] == "block"
    }
    proof_count = 0
    for item in items:
        label = item["blueprint_label"]
        title = f'{item["kind"].capitalize()} {item["number"]}'
        node = by_label[label]
        assert node["displayLabel"] == title, (label, node["displayLabel"], title)
        assert node["title"] == title, (label, node["title"], title)
        assert node["kind"].removesuffix("_") == item["kind"], (label, node["kind"])
        statement = previews[label, "statement"]
        assert statement["title"] == title, (label, statement["title"])
        check_link(statement["href"])
        proof = previews.get((label, "proof"))
        if proof:
            assert proof["title"] == "Proof for " + title, (label, proof["title"])
            check_link(proof["href"])
            statement_route = urlsplit(statement["href"]).path
            if urlsplit(proof["href"]).path != statement_route:
                page = SITE / statement_route / "index.html"
                assert f'href="{proof["href"]}"' in page.read_text(), (
                    label, "Missing direct link to appendix proof")
            proof_count += 1
        for warning, active in node["warnings"].items():
            assert not active, (label, warning)
    labels = {item["blueprint_label"] for item in items}
    old_labels = {item["label"] for item in items} - labels
    assert not old_labels.intersection(by_label), "Retired manuscript labels in graph"
    for entry in manifest["previews"]:
        if entry["targetKind"] == "block":
            check_link(entry["href"])
    for n in range(1, 4):
        assert (SITE / f"exp{n}.svg").is_file()
    assert not (SITE / "comparator").exists(), "Retired human review remains"
    print(f"Manuscript layout: {len(items)} items, {proof_count} proof links, "
          f"{sum(item['kind'] == 'example' for item in items)} examples verified.")


if __name__ == "__main__":
    main()
