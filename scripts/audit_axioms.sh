#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"
evidence_dir="${1:-$repo_dir/.verification}"
mkdir -p "$evidence_dir"
evidence_dir="$(cd "$evidence_dir" && pwd)"
scratch_dir="$(mktemp -d "${TMPDIR:-/tmp}/chemotaxis-bifurcation-live-audit.XXXXXX")"
trap 'rm -rf "$scratch_dir"' EXIT

rm -f "$evidence_dir/source-before.json" "$evidence_dir/source-after.json" \
  "$evidence_dir/positive.raw.json" "$evidence_dir/negative.raw.json" \
  "$evidence_dir/positive.json" "$evidence_dir/negative.json"
python3 scripts/verification_receipt.py snapshot \
  --output "$evidence_dir/source-before.json"

# Match the tool and revision used by lean-action in the earlier CI receipts.
audit_revision=46024e005996495c65ef609368e11ab39c4222e3
git clone --quiet --depth 1 --branch v0.1.2 \
  https://github.com/leanprover-community/axiom-audit.git "$scratch_dir/tool"
test "$(git -C "$scratch_dir/tool" rev-parse HEAD)" = "$audit_revision"
cp lean-toolchain "$scratch_dir/tool/lean-toolchain"
cp scripts/AuditInventory.lean.txt "$scratch_dir/tool/Main.lean"
(cd "$scratch_dir/tool" && lake build) >"$evidence_dir/audit-tool-build.log" 2>&1
audit_binary="$scratch_dir/tool/.lake/build/bin/axiom-audit"

# Build before loading oleans. The audit determines axiom provenance; the
# preceding build is the kernel elaboration check.
lake build >"$evidence_dir/pre-audit-build.log" 2>&1
lake env "$audit_binary" >"$evidence_dir/positive.raw.json"

# Compile the negative control in a disposable directory. Keep its evidence
# separate from the positive stream, and require the exact offending theorem.
mkdir -p "$scratch_dir/negative/ChemotaxisBifurcation"
printf '%s\n' 'import Lean' 'namespace ChemotaxisBifurcation' \
  'theorem auditTamper : False := by sorry' 'end ChemotaxisBifurcation' \
  >"$scratch_dir/negative/ChemotaxisBifurcation/AuditTamper.lean"
lake env bash -c \
  'cd "$1"; lean -o ChemotaxisBifurcation/AuditTamper.olean ChemotaxisBifurcation/AuditTamper.lean' \
  _ "$scratch_dir/negative" >"$evidence_dir/negative-build.log" 2>&1
project_lean_path="$(lake env printenv LEAN_PATH)"
set +e
lake env env LEAN_PATH="$scratch_dir/negative:$project_lean_path" \
  "$audit_binary" ChemotaxisBifurcation.AuditTamper >"$evidence_dir/negative.raw.json" \
  2>"$evidence_dir/negative-stderr.log"
negative_rc=$?
set -e
test "$negative_rc" -eq 1
python3 scripts/verification_receipt.py snapshot \
  --output "$evidence_dir/source-after.json"
cmp "$evidence_dir/source-before.json" "$evidence_dir/source-after.json"
python3 scripts/verification_receipt.py bind-audit \
  --audit "$evidence_dir/positive.raw.json" \
  --snapshot "$evidence_dir/source-after.json" \
  --output "$evidence_dir/positive.json"
python3 scripts/verification_receipt.py bind-audit \
  --audit "$evidence_dir/negative.raw.json" \
  --snapshot "$evidence_dir/source-after.json" \
  --output "$evidence_dir/negative.json"
echo 'PASS: complete live axiom inventory and compiled negative control.'
