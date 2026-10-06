#!/usr/bin/env python3
"""Check rendered manuscript numbering, kinds, and cross-chapter proof links."""

import json
import re
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
        **{letter: "appendix-" + letter.lower() for letter in "ABCDE"},
    }
    retired_labels = {"aux:hilbert-schmidt", "aux:operator-neuron",
                      "roadmap:finite-dim-universality", "aux:backprojection", "aux:hermite",
                      "aux:explicit-filters", "aux:gaussian-parameter-networks",
                      "aux:operator-layer", "aux:torus", "aux:dirichlet"}
    assert not retired_labels.intersection(by_label), "Retired nodes remain in graph"
    assert len(items) == 62, "Unexpected manuscript inventory"
    polar = "roadmap:polar-decomposition"
    assert by_label[polar]["href"].startswith("networks/"), "Polar background misplaced"
    edges = {(plain(edge["source"]), plain(edge["target"]))
             for edge in manifest["graphs"][0]["edges"]}
    assert {(polar, "def:2.2"), (polar, "def:6.1")} <= edges, "Polar dependencies missing"
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
                    label, "Missing direct link to proof")
            if chapter.isdigit():
                assert urlsplit(proof["href"]).path == statement_route, (
                    label, "Main proof must immediately follow its statement")
            proof_count += 1
        for warning, active in node["warnings"].items():
            assert not active, (label, warning)
    by_source = {item["label"]: item for item in items}
    dilation = by_source["prop:dilation-obstruction"]["blueprint_label"]
    assert by_label[dilation]["href"].startswith("appendix-d/"), "Dilation result misplaced"
    for route in ["numerics/", "discussion/", "appendix-a/", "appendix-b/",
                  "appendix-c/", "appendix-d/", "appendix-e/"]:
        check_link(route)
    chapter_sources = ROOT / "OperatorRidgeletBlueprint/Chapters"
    main_order = []
    for name in ["Networks", "Transform", "Reconstruction", "Tempered", "Sampling", "Examples"]:
        text = (chapter_sources / (name + ".lean")).read_text()
        authored = re.findall(r'^:::(?!proof)\w+ "([^"\n]+)"', text, re.M)
        main_order.extend(label for label in authored if label in by_label)
    numbered = {item["blueprint_label"]: item for item in items}
    actual = [label for label in main_order if label in numbered]
    expected = sorted((label for label, item in numbered.items()
                       if item["number"].split(".")[0].isdigit()),
                      key=lambda label: tuple(map(int, numbered[label]["number"].split("."))))
    assert actual == expected, "Authored Blueprint order differs from manuscript order"
    positions = {label: i for i, label in enumerate(actual)}
    for name in ["Transform", "Reconstruction", "Tempered", "Sampling", "Examples"]:
        text = (chapter_sources / (name + ".lean")).read_text()
        proof_pattern = r'^:::proof "([^"\n]+)"([^\n]*)\n(.*?)^:::\s*$'
        for proof in re.finditer(proof_pattern, text, re.M | re.S):
            attrs = re.search(r'uses := "([^"\n]*)"', proof[2])
            deps = set(attrs[1].split(", ") if attrs else [])
            deps.update(re.findall(r'\{bpref "([^"\n]+)"', proof[3]))
            for dep in deps:
                if dep in numbered:
                    assert dep in positions and positions[dep] < positions[proof[1]], (
                        proof[1], "Forward main proof dependency", dep)
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
