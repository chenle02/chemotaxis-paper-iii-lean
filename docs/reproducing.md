# Reproducing the formal checks

Git downloads the source. Elan installs the Lean version named by `lean-toolchain`. Lake is Lean's package/build tool; Mathlib is the pinned mathematical library. Its cache avoids recompiling dependencies, but the scientific project still builds from source.

## One command

From a clean checkout run `./verify.sh`. Git, elan, a C toolchain, Python 3 and network access are required. Start with three Lean threads (`LEAN_NUM_THREADS=3`) and allow several minutes or more depending on hardware and cache downloads.

## Transparent route

```sh
lake exe cache get
lake build
./scripts/check_umbrella.sh
./scripts/check_no_proof_escapes.sh
./scripts/test_proof_escape_gate.sh
./scripts/audit_axioms.sh
```

The audit writes `.verification/positive.raw.json` and a separate negative-control transcript. It audits the complete owned environment, including generated helpers. Success includes `PASS: complete live axiom inventory and compiled negative control.` The negative scratch theorem is expected to fail the audit; it never enters the positive library.

For receipt and comparator verification, install [lean-pkg](https://github.com/lean-pkg/lean-pkg) and follow its receipt-check commands against the committed `.lean-receipts` files. A local source-only gate additionally runs `scripts/verify-local.sh` from a committed fresh source clone and prints every indexed type/axiom query. Comparator Challenge/Solution modules are separate targets; their intentional Challenge admissions are not library proofs.

## Troubleshooting

If `lake` is missing, add elan's `bin` directory to PATH and restart the shell. Network/cache failure is not a mathematical failure: retain the error and rerun the cache fetch. Lower `LEAN_NUM_THREADS` if resources are tight. Never change the pinned toolchain or dependencies to make a check appear green. A complete build proves the Lean statements elaborate; it does not prove their transcription from the manuscript is faithful, construct their hypothesis objects, or certify the entire PDE paper.
