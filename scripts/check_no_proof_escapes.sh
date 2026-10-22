#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

matches="$(mktemp /tmp/chemotaxis-bifurcation-proof-escapes.XXXXXX)"
trap 'rm -f "$matches"' EXIT

pattern='(^|[^[:alnum:]_])(sorry|sorryAx|admit|axiom|unsafe|native_decide)([^[:alnum:]_]|$)'

set +e
LC_ALL=C grep -RInE --include='*.lean' "$pattern" -- \
  ChemotaxisBifurcation ChemotaxisBifurcation.lean >"$matches"
scan_rc=$?
set -e

case "$scan_rc" in
  0)
    cat "$matches"
    echo 'Lean proof escape or unsafe declaration found.' >&2
    exit 1
    ;;
  1)
    echo 'PASS: no Lean proof escapes or unsafe declarations.'
    ;;
  *)
    cat "$matches" >&2
    echo "Proof-escape scanner failed with exit code $scan_rc." >&2
    exit "$scan_rc"
    ;;
esac
