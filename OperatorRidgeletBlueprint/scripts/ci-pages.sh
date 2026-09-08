#!/usr/bin/env bash
# Build the Verso Blueprint, validate it, and assemble the GitHub Pages site in `_site/`.
#
# `.github/workflows/pages.yml` runs this script; it can also be run locally (from any directory)
# after `lake exe cache get` in this project.  The blueprint's own `index.html` is the top page of
# the site, so the published site is `_out/site/html-multi/` plus `.nojekyll`.

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

out=_out/site/html-multi
site=_site

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
