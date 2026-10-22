#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scratch_dir="$(mktemp -d /tmp/chemotaxis-bifurcation-proof-escape-test.XXXXXX)"
trap 'rm -rf "$scratch_dir"' EXIT

mkdir -p "$scratch_dir/ChemotaxisBifurcation" "$scratch_dir/scripts"
cp "$repo_dir/scripts/check_no_proof_escapes.sh" "$scratch_dir/scripts/"
cp "$repo_dir/ChemotaxisBifurcation.lean" "$scratch_dir/ChemotaxisBifurcation.lean"
printf '%s\n' \
  'theorem proofEscapeTamper : True := by' \
  '  sorry' \
  > "$scratch_dir/ChemotaxisBifurcation/ProofEscapeTamper.lean"

set +e
(cd "$scratch_dir" && ./scripts/check_no_proof_escapes.sh) \
  >"$scratch_dir/negative-control.log" 2>&1
gate_rc=$?
set -e

if [ "$gate_rc" -ne 1 ]; then
  cat "$scratch_dir/negative-control.log" >&2
  echo "Negative control expected exit code 1, got $gate_rc." >&2
  exit 1
fi

grep -F 'ChemotaxisBifurcation/ProofEscapeTamper.lean:2:' \
  "$scratch_dir/negative-control.log" >/dev/null
grep -F 'sorry' "$scratch_dir/negative-control.log" >/dev/null

echo 'PASS: proof-escape gate rejects an injected sorry.'
