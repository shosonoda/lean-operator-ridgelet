#!/usr/bin/env bash

set -euo pipefail

package_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$package_root"

if [ "${1:-}" = "--help" ]; then
  cat <<'EOF'
usage: ./scripts/generate-review-artifacts.sh [test blueprint slug...]

Build the local review artifact set under the worktree-aware `_out/` root:

- all reference blueprints under `_out/.../reference-blueprints/`
- test blueprints under `_out/.../test-blueprints/`

When no test blueprint slugs are provided, all local test blueprints are
generated. If one or more slugs are provided, only those test blueprints are
generated, while the full reference catalog is still rebuilt.
EOF
  exit 0
fi

./scripts/generate-reference-blueprints.sh
./scripts/generate-test-blueprints.sh "$@"
