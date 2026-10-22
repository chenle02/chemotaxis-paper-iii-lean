#!/usr/bin/env bash
# Canonical shadow and per-claim axiom probes from lean-pkg 0.18.1 receipt template.
# >>> lean-pkg lake_shadow_check (keep identical in every copy; see lean_pkg/lake_hygiene.py)
lake_root_namespaces() {
  local found
  found=$(
    {
      if [ -f lakefile.toml ]; then
        awk '/^[[:space:]]*\[/ { lib = ($0 ~ /^[[:space:]]*\[\[[[:space:]]*lean_lib[[:space:]]*\]\]/) }
             lib && /^[[:space:]]*(name|roots|globs)[[:space:]]*=/' lakefile.toml | grep -oE '"[^"]+"' | tr -d '"'
      fi
      if [ -f lakefile.lean ]; then
        grep -oE 'lean_lib[[:space:]]+(«[^»]+»|[A-Za-z_][A-Za-z0-9_.]*)' lakefile.lean | awk '{print $2}'
        tr '\n' ' ' < lakefile.lean | grep -oE '(roots|globs)[[:space:]]*:=[[:space:]]*#\[[^]]*\]' \
          | grep -oE '`[^]`[:space:],)]+' | tr -d '`'
      fi
    } 2>/dev/null | sed -e 's/^«\([^»]*\)».*$/\1/' -e 's/[.].*$//' | grep -E '^[A-Za-z_]' | sort -u || true
  )
  if [ -z "$found" ]; then
    found=$(find . -path ./.lake -prune -o -name '*.lean' ! -path ./lakefile.lean -print 2>/dev/null \
      | sed -e 's|^\./||' -e 's|/.*$||' -e 's|\.lean$||' | grep -E '^[A-Za-z_]' | sort -u || true)
  fi
  printf '%s\n' "$found"
}
lake_shadow_check() {
  local own entry r n=0 hits=0 roots
  local -a entries
  own="$(pwd -P)/.lake/build/lib/lean"
  roots=$(lake_root_namespaces)
  IFS=: read -r -a entries <<<"${1:-}"
  for entry in "${entries[@]}"; do
    [ -n "$entry" ] || continue
    n=$((n + 1))
    if [ "$(cd "$entry" 2>/dev/null && pwd -P)" = "$own" ]; then continue; fi
    for r in $roots; do
      if [ -d "$entry/$r" ] || [ -e "$entry/$r.olean" ] || [ -e "$entry/$r.ilean" ]; then
        echo "lean-path-shadow: $entry/$r"
        hits=$((hits + 1))
      fi
    done
  done
  if [ "$hits" -gt 0 ]; then return 1; fi
  echo "lean-path-shadow: none ($n entries, roots $(printf '%s' "$roots" | paste -sd, -))"
}
# <<< lean-pkg lake_shadow_check
# Per-claim axioms read from the built environment (lean-pkg's ClaimAxioms.lean, core Lean only):
# `claim-axioms: NAME AXIOMS` / `claim-missing: NAME` for every claim of claims.yaml, then
# `claim-axioms-done: N`. The receipt refuses a missing or unchecked claim and sorryAx.
claims_decls() {
  awk 'function val(s) {
  sub(/^[A-Za-z_]+:[ \t]*/, "", s); sub(/[ \t]+#.*$/, "", s); sub(/[ \t\r]+$/, "", s)
  if (s ~ /^".*"$/ || s ~ /^'\''.*'\''$/) s = substr(s, 2, length(s) - 2)
  return s
}
function flush() { if (decl != "") print decl "\t" file; decl = ""; file = "" }
BEGIN { item = -1; key = -1 }
/^[ \t]*#/ || /^[ \t\r]*$/ { next }
/^claims:/ { inl = 1; next }
inl && /^[^ \t-]/ { flush(); inl = 0 }
!inl { next }
{
  match($0, /^ */); ind = RLENGTH; rest = substr($0, ind + 1)
  if (rest ~ /^- /) {
    if (item < 0) item = ind
    if (ind == item) { flush(); match(rest, /^- +/); ind = ind + RLENGTH; rest = substr(rest, RLENGTH + 1); key = ind }
  }
  if (ind == key) {
    if (rest ~ /^decl:/) decl = val(rest)
    else if (rest ~ /^file:/) file = val(rest)
  }
}
END { flush() }' "$1"
}
claim_axioms_run() {
  [ -f claims.yaml ] || return 0
  local pairs names mods
  pairs=$(claims_decls claims.yaml)
  if [ -z "$pairs" ]; then echo "claim-axioms-done: 0" >>"$1"; return 0; fi
  names=$(printf '%s\n' "$pairs" | cut -f1)
  mods=$(printf '%s\n' "$pairs" | cut -f2 | grep '\.lean$' | sed -e 's/\.lean$//' -e 's|/|.|g' | sort -u || true)
  mkdir -p "$2"
  cat >"$2/ClaimAxioms.lean" <<'LEAN_PKG_CLAIM_AXIOMS'
/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0
-/
-- lean_pkg.claim_axioms: the Lean half. Read-only probe of a compiled environment.
--
-- Usage: LEAN_PATH=<the package's> lean --run ClaimAxioms.lean MOD [MOD ...] -- NAME [NAME ...]
--
-- Imports MOD... exactly as `import MOD` would (data only: no extension state is loaded and no
-- initializer runs, so Lean walks every constant body itself instead of reading axiom lists cached in
-- the .olean files), then runs core Lean's `collectAxioms` on every NAME and prints one line per name:
--   claim-axioms: NAME AX1,AX2,...   (sorted; `none` when it depends on no axiom)
--   claim-missing: NAME              (no constant of that name in the environment)
-- and a final `claim-axioms-done: N` line (N = the number of names). A run without that line is
-- incomplete; lean_pkg/claim_axioms.py refuses it. Nothing is judged here. Core Lean only.
import Lean

open Lean

/-- The monad `collectAxioms` needs: an environment that can be read. -/
abbrev ClaimAxiomsM := StateM Environment

instance : MonadEnv ClaimAxiomsM where
  getEnv := get
  modifyEnv f := modify f

def main (args : List String) : IO UInt32 := do
  let mods := args.takeWhile (· != "--")
  let names := (args.dropWhile (· != "--")).drop 1
  if mods.isEmpty || names.isEmpty then
    IO.eprintln "usage: lean --run ClaimAxioms.lean MOD [MOD ...] -- NAME [NAME ...]"
    return 2
  initSearchPath (← findSysroot)
  let imports := mods.toArray.map fun m => ({ module := m.toName } : Import)
  let env ← importModules imports {} (loadExts := false)
  let mut n := 0
  for s in names do
    n := n + 1
    let name := s.toName
    if (env.find? name).isNone then
      IO.println s!"claim-missing: {s}"
    else
      let (axs, _) := (collectAxioms name : ClaimAxiomsM (Array Name)).run env
      let sorted := (axs.map toString).qsort (· < ·)
      let shown := if sorted.isEmpty then "none" else ",".intercalate sorted.toList
      IO.println s!"claim-axioms: {s} {shown}"
  IO.println s!"claim-axioms-done: {n}"
  return 0
LEAN_PKG_CLAIM_AXIOMS
  # shellcheck disable=SC2086 # one word per module and per name
  ${RUN:-} env LEAN_PATH="$3" lean --run "$2/ClaimAxioms.lean" $mods -- $names >>"$1" 2>&1
}
