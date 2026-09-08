#!/usr/bin/env bash
# Build the Verso Blueprint, validate it, and assemble the GitHub Pages site in `_site/`.
#
# `.github/workflows/pages.yml` runs this script; it can also be run locally (from any directory)
# after `lake exe cache get` in this project (Python 3 is needed for the generated chapter).  The
# blueprint's own `index.html` is the top page of the site, so the published site is
# `_out/site/html-multi/` plus `.nojekyll`.

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

out=_out/site/html-multi
site=_site

# The comparator review chapter is generated from the data of ../OperatorRidgelet (paper.json,
# config.json, Challenge/); regenerate it so that the site never shows a stale copy.
python3 scripts/gen-comparator-chapter.py

lake exe vbp build
lake exe vbp check

test -f "$out/index.html"
test -f "$out/-verso-data/blueprint-manifest.json"
test -f "$out/-verso-data/blueprint-html-cache.json"

rm -rf "$site"
mkdir -p "$site"
cp -R "$out"/. "$site"/
touch "$site/.nojekyll"

test -f "$site/index.html"
test -d "$site/-verso-data"
echo "Pages site assembled in $PWD/$site"
