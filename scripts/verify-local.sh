#!/usr/bin/env bash
# Native lean-pkg systemd receipt command: bash scripts/verify-local.sh RAW_LOG
# Rebuild owned modules from a committed source-only clone; reuse pinned dependencies.
# Pass explicit --stdout and --stderr files to receipt systemd: seals are printed
# on stdout, while every verification tool writes to RAW_LOG.
set -euo pipefail
export LC_ALL=C LANG=C PYTHONUTF8=1
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"
unset LANGUAGE
repo="$(git rev-parse --show-toplevel)"
commit="$(git rev-parse HEAD)"
log="${1:?absolute raw log path required}"
[[ "$log" = /* && ! -e "$log" ]] || exit 64
work="$(mktemp -d "$(dirname "$log")/source-replay.XXXXXX")"
stage="$work/src"
trap 'printf "replay-source: %s\n" "$stage"' EXIT
mkdir -p "$stage"
# This source copy has its own Git object store, and no ignored/untracked inputs.
git init -q --template= "$stage"
GIT_ALLOW_PROTOCOL=file git -C "$stage" fetch -q --no-tags --no-recurse-submodules "$repo" "$commit"
git -C "$stage" -c core.hooksPath=/dev/null -c advice.detachedHead=false checkout -q --detach FETCH_HEAD
cd "$stage"
[[ "$(git rev-parse HEAD)" == "$commit" && -z "$(git status --porcelain)" ]]
[[ ! -e .lake ]]
mkdir .lake
ln -s "$repo/.lake/packages" .lake/packages
export LAKE_CACHE_DIR="$work/empty-lake-cache"
export LAKE_ARTIFACT_CACHE=false
mkdir "$LAKE_CACHE_DIR"
[[ ! -e .lake/build && -z "$(ls -A "$LAKE_CACHE_DIR")" ]]
source scripts/local_receipt_helpers.sh
printf 'pre-manifest-sha256 %s\n' "$(sha256sum lake-manifest.json | cut -d' ' -f1)"
{
  printf 'commit: %s\n' "$commit"
  if [[ -n "${SLURM_JOB_ID:-}" ]]; then printf 'job-id: %s\n' "$SLURM_JOB_ID"; fi
  printf 'lean-toolchain: %s\n' "$(cat lean-toolchain)"
  if [[ -n "${LEAN_GATE_CONTAINER_SHA256:-}" ]]; then
    printf 'container-engine: singularity\n'
    printf 'container-image: %s\n' "${LEAN_GATE_CONTAINER_IMAGE:?container image identity required}"
    printf 'container-image-sha256: %s\n' "$LEAN_GATE_CONTAINER_SHA256"
  fi
  printf 'checker: fresh local lake build; complete owned axiom inventory; exact mapped types; compiled negative control\n'
  printf 'fs-file-nr-before: %s\n' "$(cat /proc/sys/fs/file-nr)"
  lean --version
  lake --version
  ./scripts/check_umbrella.sh
  ./scripts/check_no_proof_escapes.sh
  ./scripts/test_proof_escape_gate.sh
  python3 scripts/check_lake_packages.py --root "$PWD" --manifest "$PWD/lake-manifest.json" --output "$work/dependencies-before.json"
} >"$log" 2>&1
printf 'lean-pkg-build: begin\n' >>"$log"
lake build >>"$log" 2>&1
printf 'lean-pkg-build: end\n' >>"$log"
lean_path="$(lake env printenv LEAN_PATH)"
lake_shadow_check "$lean_path" >>"$log" 2>&1
# Only dependencies can be cached: the source-only clone began with no root build/cache.
./scripts/audit_axioms.sh "$work/owned-audit" >>"$log" 2>&1
cat "$work/owned-audit/positive.raw.json" >>"$log"
# Print every indexed public declaration from the actual freshly built environment.
cp scripts/PrintedTypes.lean.txt "$work/PrintedTypes.lean"
lake env lean --root="$work" "$work/PrintedTypes.lean" >"$work/printed-types-and-axioms.txt" 2>&1
cat "$work/printed-types-and-axioms.txt" >>"$log"
claim_axioms_run "$log" "$work/claim-axioms" "$lean_path"
python3 scripts/check_lake_packages.py --root "$PWD" --manifest "$PWD/lake-manifest.json" --output "$work/dependencies-after.json" >>"$log" 2>&1
cmp "$work/dependencies-before.json" "$work/dependencies-after.json"
# Check the full environment, including generated auxiliaries, before reporting the axiom union.
python3 - "$work/owned-audit/positive.raw.json" >>"$log" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]));p=r['report']
assert p['ok'] and not p['violations']
assert p['audited']==len(r['declarations'])
assert set(p['axiomsUsed']) <= {'propext','Classical.choice','Quot.sound'}
print('owned-declarations:',p['audited'])
print('axioms:',','.join(sorted(p['axiomsUsed'])) or 'none')
PY
sorry="$(grep -c -E "declaration uses ['\`]sorry['\`]" "$log" || true)"
[[ "$sorry" == 0 ]]
{
  printf 'sorry-count: %s\n' "$sorry"
  printf 'fs-file-nr-after: %s\n' "$(cat /proc/sys/fs/file-nr)"
  printf 'generated-at: %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
} >>"$log"
printf 'post-manifest-sha256 %s\n' "$(sha256sum lake-manifest.json | cut -d' ' -f1)"
printf 'verify-log-sha256 %s\n' "$(sha256sum "$log" | cut -d' ' -f1)"
