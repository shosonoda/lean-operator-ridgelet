#!/usr/bin/env python3
"""Preserve historical Blueprint statement/proof URLs after a site build.

Run after `vbp check`. Redirects are HTML navigation helpers and add no Blueprint nodes.
Retired results receive explicit notices linked to their fixed historical source.
Use --self-test to exercise moved proofs, reused numbers, encoded hashes and reruns.
"""

import argparse
import html
import json
import posixpath
from pathlib import Path, PurePosixPath
import re
import subprocess
import tempfile
from urllib.parse import unquote, urlsplit


PROJECT = Path(__file__).resolve().parents[1]
SCRIPT_ID = "blueprint-legacy-redirects"
PAGE_MARKER = '<body data-blueprint-legacy-page="true">'


def label_text(value):
    return value.removeprefix("«").removesuffix("»")


def split_href(href):
    """Accept only safe, site-relative output URLs."""
    parts = urlsplit(href)
    path = unquote(parts.path)
    if (parts.scheme or parts.netloc or parts.query or path.startswith("/")
            or "\\" in path or ".." in PurePosixPath(path).parts):
        raise ValueError(f"Not a site-relative URL: {href}")
    return parts.path, unquote(parts.fragment)


def output_file(site, route):
    path = site / unquote(route)
    return path if route.endswith(".html") else path / "index.html"


def relative_href(target, route):
    path, fragment = urlsplit(target).path, urlsplit(target).fragment
    parent = posixpath.dirname(route) if route.endswith(".html") else route.rstrip("/")
    relative = posixpath.relpath(path or ".", parent or ".")
    if path.endswith("/") and not relative.endswith("/"):
        relative += "/"
    return relative + ("#" + fragment if fragment else "")


def redirect_script(links, fallback):
    payload = json.dumps({"links": links, "fallback": fallback}, ensure_ascii=True)
    payload = payload.replace("<", "\\u003c")
    return f'''<script id="{SCRIPT_ID}">
(() => {{
  const data = {payload};
  const decode = value => {{ try {{ return decodeURIComponent(value); }} catch {{ return value; }} }};
  function redirect() {{
    const hash = decode(location.hash.slice(1));
    const target = Object.prototype.hasOwnProperty.call(data.links, hash)
      ? data.links[hash] : data.fallback;
    if (target === null) return;
    const next = new URL(target, location.href);
    if (decode(next.pathname) === decode(location.pathname)
        && decode(next.hash) === decode(location.hash)) return;
    location.replace(next.href);
  }}
  redirect();
  addEventListener("hashchange", redirect);
}})();
</script>'''


def retired_notice(record):
    """Build a notice without treating a reused theorem number as its identity."""
    label = record["label"]
    slug = re.sub(r"[^a-zA-Z0-9]+", "-", label).strip("-").lower()
    source = record["source"]
    fixed_revision = "525a54cf4c341fdc5c303b7db93a6e21d101a27e"
    prefix = "https://github.com/shosonoda/lean-operator-ridgelet/blob/"
    if not source.startswith(prefix + fixed_revision + "/"):
        raise ValueError("Retired source must use the preserved fixed revision")
    title = html.escape(record.get("title", label))
    page = ('<!doctype html><html lang="en"><head><meta charset="utf-8">'
            '<title>Retired Blueprint result: ' + title + '</title></head><body>'
            '<h1>Result removed from the current exposition</h1><p>' + title
            + ' belongs to the earlier exposition and has been removed from the current '
            'manuscript inventory. A reused number in the current version denotes a '
            'different result.</p><p>The previous statement and proof are preserved in '
            '<a href="' + html.escape(source, quote=True) + '">the fixed source snapshot</a>'
            ' (525a54c; snapshot20260929before-pruning-appendix).</p>'
            '<p><a href="../../index.html">Read the current Blueprint.</a></p></body></html>')
    return "retired/" + slug + "/", page


def install(site, manifest, legacy):
    targets = {}
    for graph in manifest.get("graphs", []):
        for node in graph["nodes"]:
            targets[(label_text(node["label"]), "statement")] = node["href"]
    for preview in manifest.get("previews", []):
        if preview.get("targetKind") == "block":
            label = preview.get("authoredLabel") or label_text(preview["label"])
            targets[(label, preview["facet"])] = preview["href"]

    current_hrefs = {split_href(href) for href in targets.values()}
    notices = {}
    routes = {}
    for entry in legacy:
        route, fragment = split_href(entry["oldhref"])
        if "retired" in entry:
            if (route, fragment) in current_hrefs:
                raise ValueError("Retired URL is reused by a current result: " + entry["oldhref"])
            target, content = retired_notice(entry["retired"])
            if target in notices and notices[target] != content:
                raise ValueError("Conflicting retired notice: " + target)
            notices[target] = content
        elif "targethref" in entry:
            target = entry["targethref"]
        else:
            facet = "proof" if fragment.endswith("--proof") else "statement"
            key = (entry["targetlabel"], facet)
            if key not in targets:
                raise ValueError(f"Missing current {facet} target: {key[0]}")
            target = targets[key]
        new_route, _ = split_href(target)
        if new_route not in notices and not output_file(site, new_route).is_file():
            raise ValueError(f"Missing current target page: {new_route}")
        entries = routes.setdefault(route, {})
        if fragment in entries and entries[fragment] != target:
            raise ValueError(f"Conflicting legacy target: {entry['oldhref']}")
        entries[fragment] = target

    # Resolve every target before changing output files.
    for target, content in notices.items():
        page = output_file(site, target)
        page.parent.mkdir(parents=True, exist_ok=True)
        page.write_text(content)
    for route, entries in routes.items():
        page = output_file(site, route)
        original = page.read_text() if page.is_file() else ""
        legacy_page = not original or PAGE_MARKER in original
        fallback = None
        if legacy_page:
            section = route.split("/", 1)[0] + "/"
            section_file = output_file(site, section)
            if section_file == page or not section_file.is_file():
                section = next(iter(entries.values())).split("/", 1)[0] + "/"
            if output_file(site, section) == page or not output_file(site, section).is_file():
                section = "index.html"
            fallback = relative_href(section, route)
        links = {fragment: relative_href(target, route) for fragment, target in entries.items()}
        script = redirect_script(links, fallback)
        if legacy_page:
            original = ('<!doctype html><html lang="en"><head><meta charset="utf-8">'
                        '<title>Blueprint page moved</title></head>' + PAGE_MARKER
                        + '<p>This Blueprint page has moved. <a href="'
                        + html.escape(fallback, quote=True)
                        + '">Continue to the current section.</a></p></body></html>')
        original = re.sub(r'<script id="' + SCRIPT_ID + r'">.*?</script>\s*',
                          '', original, flags=re.DOTALL)
        if "</head>" not in original:
            raise ValueError(f"Missing HTML head: {page}")
        page.parent.mkdir(parents=True, exist_ok=True)
        page.write_text(original.replace("</head>", script + "\n</head>", 1))
    return len(routes)


def self_test():
    with tempfile.TemporaryDirectory() as directory:
        site = Path(directory)
        for route in ["index.html", "transform/", "transform/current/", "appendix-a/"]:
            path = output_file(site, route)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('<html><head></head><body id="existing">Current</body></html>')
        manifest = {"graphs": [{"nodes": [{"label": "«thm:3.11»",
                    "href": "transform/current/#new--statement"}]}],
                    "previews": [{"targetKind": "block", "authoredLabel": "thm:3.11",
                    "facet": "proof", "href": "appendix-a/#new--proof"}]}
        legacy = [{"oldhref": route + "#old--" + facet, "targetlabel": "thm:3.11"}
                  for route in ["transform/old/", "transform/current/"]
                  for facet in ["statement", "proof"]]
        assert install(site, manifest, legacy) == 2
        previous = output_file(site, "transform/old/").read_text()
        install(site, manifest, legacy)
        assert previous == output_file(site, "transform/old/").read_text()
        assert 'id="existing"' in output_file(site, "transform/current/").read_text()
        js = redirect_script({"old--proof": "../../appendix-a/#new--proof"}, None)
        body = js.split(">", 1)[1].rsplit("</script>", 1)[0]
        harness = '''
const assert = require("node:assert/strict");
function run(href, code) {
  let destination = null;
  const location = new URL(href);
  location.replace = next => { destination = next; };
  const addEventListener = () => {};
  eval(code);
  return destination;
}
const code = CODE;
assert.equal(run("https://example.org/project/transform/old/#old%2D%2Dproof", code),
             "https://example.org/project/appendix-a/#new--proof");
assert.equal(run("https://example.org/project/transform/old/#unknown", code), null);
assert.equal(run("https://example.org/project/transform/old/#old--proof",
             code.replace("../../appendix-a/#new--proof", "#old--proof")), null);
'''.replace("CODE", json.dumps(body))
        subprocess.run(["node", "-e", harness], check=True)
        # The old F.3 is universality; the new F.3 is dilation obstruction.
        # A matching number must never redirect a retired result to the new theorem.
        manifest["graphs"][0]["nodes"].append({"label": "«prop:F.3»",
            "href": "transform/current/#dilation--statement"})
        record = {"label": "prop:F.3", "title": "Proposition F.3 (earlier version)",
            "source": "https://github.com/shosonoda/lean-operator-ridgelet/blob/"
                      "525a54cf4c341fdc5c303b7db93a6e21d101a27e/"
                      "OperatorRidgelet/OperatorRidgelet/Paper/Networks.lean"}
        retired = [{"oldhref": "appendix-f/#universality--statement", "retired": record}]
        install(site, manifest, retired)
        page = output_file(site, "appendix-f/").read_text()
        assert "retired/prop-f-3/" in page and "dilation--statement" not in page
        notice = output_file(site, "retired/prop-f-3/").read_text()
        assert "removed from the current" in notice and "525a54c" in notice
        install(site, manifest, retired)
        assert notice == output_file(site, "retired/prop-f-3/").read_text()
        reused = [{"oldhref": "transform/current/#dilation--statement", "retired": record}]
        try:
            install(site, manifest, reused)
        except ValueError as error:
            assert "reused" in str(error)
        else:
            raise AssertionError("A retired URL hijacked a current result")
        # The D.7/D.8 migration needs the same distinction even when node kinds match.
        d_record = dict(record, label="cor:D.7", title="Corollary D.7 (earlier version)")
        manifest["graphs"][0]["nodes"].append({"label": "«cor:D.7»",
            "href": "appendix-a/#truncation--statement"})
        install(site, manifest, [
            {"oldhref": "appendix-d/old/#old-D7--statement", "retired": d_record},
            {"oldhref": "appendix-d/old/#old-D8--statement", "targetlabel": "cor:D.7"}])
        d_page = output_file(site, "appendix-d/old/").read_text()
        assert "retired/cor-d-7/" in d_page and "truncation--statement" in d_page
        broken = legacy + [{"oldhref": "x/#missing", "targetlabel": "missing"}]
        try:
            install(site, manifest, broken)
        except ValueError:
            pass
        else:
            raise AssertionError("Missing target was accepted")
    print("Legacy redirect tests passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site", type=Path, default=PROJECT / "_out/site/html-multi")
    parser.add_argument("--links", type=Path, default=PROJECT / "data/legacy-links.json")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    manifest = json.loads((args.site / "-verso-data/blueprint-manifest.json").read_text())
    count = install(args.site, manifest, json.loads(args.links.read_text()))
    print(f"Installed legacy Blueprint links on {count} routes")


if __name__ == "__main__":
    main()
