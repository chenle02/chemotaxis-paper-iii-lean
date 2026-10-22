# Chemotaxis III in Lean

A Lean 4 / Mathlib companion formalizing coefficient calculations, stationary estimates, compactness and conditional bifurcation deductions for Chemotaxis III.

![Lean](https://img.shields.io/badge/Lean-4.35.0-blue) ![License](https://img.shields.io/badge/license-Apache--2.0-green)

## What is proved

The library supplies finite coefficient and modal identities, classical stationary mass and regularity estimates, weak limits and spike subsequences under stated inputs, bounded-sensitivity compactness, actual weak-H2 cosine coordinates and complement splitting, and conditional local/global branch deductions. The latest additions also derive the critical modal signal response from an actual elliptic solution family and a supplied population jet, and a quadratic coefficient from conserved mass.

The [scope ledger](data/public-scope-ledger.json) retains **47 verified scopes, 23 conditional scopes, and 3 exclusions** across **73 overlapping manuscript-facing scopes**. These counts are not a percentage of whole-paper correctness. The library has 1,525 indexed declarations, including definitions; compiler-generated auxiliaries are not counted as new mathematical theorems.

> [!IMPORTANT]
> **Not proved here:** whole-paper correctness, actual stationary operator/Fredholm identification, construction/exhaustion of the local PDE branch, a center manifold with dynamical invariance, global bifurcation alternatives and correspondence, or PDE stability. Supplied families, phase-norm jets, chart/exhaustion data, critical-parameter identifications and other named inputs remain explicit where used. A geometric Fourier complement is not identification with an operator's range or stable spectrum.

Read [what is proved](docs/what-is-proved.md), [scope ledger](docs/scope-ledger.md), and the generated [verification page](docs/verification.md).

## Paper and references

Le Chen, Ian Ruau and Wenxian Shen, *Chemotaxis models with signal-dependent sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions*.

- [Public manuscript and source](https://github.com/chenle02/chemotaxis-paper-iii).
- [arXiv:2610.20976v1](https://arxiv.org/abs/2610.20976v1), the published preprint.
- Current formalization input: October 20, 2026 v2 candidate, SHA-256 `545c93f8dc375ca9c57547e1cb6a28b8c47209da9ee6c77e42e60884e44ccaae`. This does not assert an arXiv v2 upload or journal submission.

```bibtex
@misc{chen_ruau_shen_2026_chemotaxis_iii,
  author = {Chen, Le and Ruau, Ian and Shen, Wenxian},
  title = {Chemotaxis models with signal-dependent sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions},
  eprint = {2610.20976},
  archivePrefix = {arXiv},
  primaryClass = {math.AP},
  year = {2026}
}
```

## Build and verify

Install Git and [elan](https://github.com/leanprover/elan), then:

```sh
git clone https://github.com/chenle02/chemotaxis-paper-iii-lean.git
cd chemotaxis-paper-iii-lean
./verify.sh
```

The exact Lean version is in `lean-toolchain`; `lake-manifest.json` pins Mathlib and its transitive dependencies. `./verify.sh` restores the Mathlib cache, builds all scientific modules, audits every owned declaration's axioms and checks that a deliberately admitted scratch theorem is rejected. See [the beginner guide](docs/reproducing.md) for the equivalent commands and troubleshooting.

To use the library from another Lake project:

```toml
[[require]]
name = "chemotaxis-bifurcation-lean"
git = "https://github.com/chenle02/chemotaxis-paper-iii-lean"
rev = "main" # use an immutable release commit for reproducible work
```

## Trust and axioms

Allowed foundational axioms: `propext`, `Quot.sound`, and `Classical.choice`. No `sorryAx`, custom axiom, `unsafe`, or `native_decide` is allowed in the scientific modules. Challenge files contain intentionally admitted comparison statements and are not scientific proof targets. The two comparator configurations cover 108 full-tier and 12 headline slots; they do not compare every library declaration. Exact source receipts and statement comparison are distinct from manuscript-fidelity review.

This is a fresh public source history. [Source correspondence](data/source-correspondence.json) records the single documentation-comment change to the accepted mathematical source. New release receipts bind this public commit; older private receipts are not claimed as receipts for this history. The public scope summary preserves the accepted correspondence judgments and conditions without publishing private review histories.

## Built with lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).

## Authors and AI disclosure

Paper authors: Le Chen, Ian Ruau and Wenxian Shen. Lean formalization and maintenance: Le Chen, with AI assistance in proofs, audit tooling and documentation. AI assistance is not an independent mathematical authority; the checked types, explicit inputs and stated review boundary determine the claims.

## Related reusable libraries

- [neumann-cosine-lean](https://github.com/chenle02/neumann-cosine-lean)
- [scalar-pitchfork-lean](https://github.com/chenle02/scalar-pitchfork-lean)

These standalone packages have their own APIs, receipts and releases. The companion currently retains its existing checked source rather than changing dependency identities during publication.

<!-- lean-pkg:begin -->
<!-- lean-pkg:end -->
