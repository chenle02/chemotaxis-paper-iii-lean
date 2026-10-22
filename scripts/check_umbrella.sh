#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

expected_imports="$(mktemp /tmp/chemotaxis-bifurcation-imports.XXXXXX)"
trap 'rm -f "$expected_imports"' EXIT

# Module-system umbrella: `module`, one `public import` per project module in
# canonical order, then the (empty) exposed public section.
{
  printf 'module\n\n'
  find ChemotaxisBifurcation -type f -name '*.lean' -print \
    | LC_ALL=C sort \
    | sed 's#/#.#g; s#\.lean$##; s#^#public import #'
  printf '\n@[expose] public section\n\nend\n'
} > "$expected_imports"

diff -u "$expected_imports" ChemotaxisBifurcation.lean
echo 'PASS: ChemotaxisBifurcation.lean imports every project module in canonical order.'
