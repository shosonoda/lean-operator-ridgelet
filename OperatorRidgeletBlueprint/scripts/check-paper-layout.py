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
    expected_chapters = {
        "2": "networks", "3": "transform", "4": "reconstruction", "5": "tempered",
        "6": "sampling", "7": "examples",
        **{letter: "appendix-" + letter.lower() for letter in "ABCDEF"},
    }
    retired_labels = {"lem:F.1", "lem:F.2", "lem:F.4", "thm:H.1",
                      "aux:hilbert-schmidt", "aux:operator-neuron",
                      "roadmap:finite-dim-universality"}
    assert not retired_labels.intersection(by_label), "Retired nodes remain in graph"
    assert len(items) == 62, "Unexpected manuscript inventory"
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
        chapter = item["number"].split(".")[0]
        assert statement["href"].split("/")[0] == expected_chapters[chapter], (
            label, "Statement outside its manuscript chapter", statement["href"])
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
    for label in ["ex:3.12", "ex:3.13", "prop:5.8"]:
        assert previews[label, "proof"]["href"].startswith("appendix-g/"), label
    assert "/supplementary-estimates/" in previews["cor:D.7", "statement"]["href"], (
        "New D.7 must not reuse the retired operator-approximation URL")
    assert by_label["prop:F.3"]["href"].startswith("appendix-f/"), "Dilation result misplaced"
    for route in ["numerics/", "discussion/", "appendix-g/", "appendix-h/"]:
        check_link(route)
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
