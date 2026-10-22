#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"
./scripts/check_umbrella.sh
./scripts/check_no_proof_escapes.sh
./scripts/test_proof_escape_gate.sh
lake exe cache get
lake build
./scripts/audit_axioms.sh
python3 - <<'PYVERIFY'
import json
from pathlib import Path
p=json.loads(Path('.verification/positive.raw.json').read_text())['report']
assert p['ok'] and not p['violations']
assert set(p['axiomsUsed']) <= {'propext','Classical.choice','Quot.sound'}
n=json.loads(Path('.verification/negative.raw.json').read_text())['report']
assert not n['ok']
print('PASS: full build, complete live owned axiom audit, and rejected admitted negative control.')
PYVERIFY
