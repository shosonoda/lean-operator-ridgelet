#!/usr/bin/env bash
# Run leanprover/comparator on the Challenge/Solution pair of this project.
#
# On Linux, install `landrun` and `lean4export` (both matching lean-toolchain) on PATH.
# On macOS there is no landrun; point COMPARATOR_LANDRUN at comparator's fake shim
# (development only, no sandbox).  Defaults assume the tools were built in ../../lean-tools.
set -euo pipefail
cd "$(dirname "$0")/.."
TOOLS="${LEAN_TOOLS:-$(cd ../.. && pwd)/lean-tools}"
export COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN:-$TOOLS/comparator/scripts/fake-landrun.sh}"
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$TOOLS/lean4export/.lake/build/bin/lean4export}"
COMPARATOR_BIN="${COMPARATOR_BIN:-$TOOLS/comparator/.lake/build/bin/comparator}"
for f in "$COMPARATOR_LANDRUN" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_BIN"; do
  [[ -x "$f" ]] || { echo "missing executable: $f" >&2; exit 2; }
done
exec lake env "$COMPARATOR_BIN" comparator/config.json
