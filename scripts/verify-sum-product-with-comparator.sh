#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd -- "$SCRIPT_DIR/.." && pwd)"

usage() {
  cat >&2 <<'EOF'
Usage: scripts/verify-sum-product-with-comparator.sh [COMPARATOR_DIR]

Builds a checked-out leanprover/comparator and runs it on
comparator/sum_product_false.json.  The comparator checkout must use a Lean
version compatible with this project (currently the comparator v4.30.0 tag).

Set COMPARATOR_LANDRUN if landrun is not on PATH.  For local smoke tests only,
you may point COMPARATOR_LANDRUN at comparator's scripts/fake-landrun.sh.
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

COMPARATOR_DIR="${1:-${COMPARATOR_DIR:-}}"
if [[ -z "$COMPARATOR_DIR" ]]; then
  usage
  exit 2
fi

if [[ ! -d "$COMPARATOR_DIR/.git" ]]; then
  echo "error: '$COMPARATOR_DIR' is not a comparator git checkout" >&2
  exit 2
fi

COMPARATOR_DIR="$(cd -- "$COMPARATOR_DIR" && pwd)"
cd "$REPO_ROOT"

CONFIG="${CONFIG:-comparator/sum_product_false.json}"
PROJECT_TOOLCHAIN="$(< lean-toolchain)"
COMPARATOR_TOOLCHAIN="$(< "$COMPARATOR_DIR/lean-toolchain")"

if [[ "$COMPARATOR_TOOLCHAIN" != "$PROJECT_TOOLCHAIN" ]]; then
  cat >&2 <<EOF
error: comparator toolchain '$COMPARATOR_TOOLCHAIN' differs from project toolchain
       '$PROJECT_TOOLCHAIN'.  Use a matching checkout, for example:

  git -C '$COMPARATOR_DIR' fetch --tags
  git -C '$COMPARATOR_DIR' checkout v4.30.0
EOF
  exit 1
fi

if [[ -z "${COMPARATOR_LANDRUN:-}" ]] && ! command -v landrun >/dev/null 2>&1; then
  cat >&2 <<EOF
error: landrun was not found on PATH and COMPARATOR_LANDRUN is unset.
Install landrun, or for a non-sandboxed local smoke test only run:

  COMPARATOR_LANDRUN='$COMPARATOR_DIR/scripts/fake-landrun.sh' \
    scripts/verify-sum-product-with-comparator.sh '$COMPARATOR_DIR'
EOF
  exit 1
fi

(
  cd "$COMPARATOR_DIR"
  lake build lean4export comparator
)

DEFAULT_LEAN4EXPORT="$COMPARATOR_DIR/.lake/packages/lean4export/.lake/build/bin/lean4export"
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$DEFAULT_LEAN4EXPORT}"

exec lake env "$COMPARATOR_DIR/.lake/build/bin/comparator" "$CONFIG"
