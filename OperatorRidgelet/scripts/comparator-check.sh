#!/usr/bin/env bash
# Run leanprover/comparator on the Challenge/Solution pair of this project.
#
# Requires `comparator`, `lean4export`, and `landrun` (all matching lean-toolchain) on PATH, or
# their locations in COMPARATOR_BIN, COMPARATOR_LEAN4EXPORT, and COMPARATOR_LANDRUN.  landrun
# needs Linux; comparator ships `scripts/fake-landrun.sh` for development elsewhere (no sandbox).
set -euo pipefail
cd "$(dirname "$0")/.."
export COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN:-$(command -v landrun || true)}"
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$(command -v lean4export || true)}"
COMPARATOR_BIN="${COMPARATOR_BIN:-$(command -v comparator || true)}"
for v in COMPARATOR_LANDRUN COMPARATOR_LEAN4EXPORT COMPARATOR_BIN; do
  f="${!v}"
  [[ -n "$f" && -x "$f" ]] || { echo "$v: executable not found (set it or put the tool on PATH)" >&2; exit 2; }
done
exec lake env "$COMPARATOR_BIN" comparator/config.json
