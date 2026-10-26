---
title: Acknowledgments and citation
description: Authors, AI disclosure, tools and compute behind the Chemotaxis III Lean companion, and how to cite it.
---

# Acknowledgments and citation

## Authors and AI disclosure

Paper authors: Le Chen, Ian Ruau and Wenxian Shen. Lean formalization and maintenance: Le Chen, with AI assistance in proofs, audit tooling and documentation. AI assistance is not an independent mathematical authority; the checked types, explicit inputs and stated review boundary determine the claims.

## lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
lean-pkg keeps the build, axiom and comparator receipts and generates the [verification page](verification.html) and [coverage table](coverage.html) from them.

## Auburn University Easley Cluster

This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html).

Easley ran an accepted verification gate (full build, owned-declaration axiom audit, negative `sorry` control and the 108 + 12 comparator slots) during the private development of this companion, on an earlier state of the source. The receipts committed for this public history were produced on a local workstation; see [trust and axioms](trust.html#source-history-and-receipts).

## Lean and Mathlib

Built on [Lean 4](https://lean-lang.org) and [Mathlib](https://github.com/leanprover-community/mathlib4); exact versions are pinned in `lean-toolchain` and `lake-manifest.json`.

## Related reusable libraries

- [neumann-cosine-lean](https://github.com/chenle02/neumann-cosine-lean)
- [scalar-pitchfork-lean](https://github.com/chenle02/scalar-pitchfork-lean)

These standalone packages have their own APIs, receipts and releases. The companion currently retains its existing checked source rather than changing dependency identities during publication.

## How to cite

Cite the software with [CITATION.cff](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/main/CITATION.cff), and the paper:

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

- [Manuscript source and PDF](https://github.com/chenle02/chemotaxis-paper-iii-lean/tree/main/manuscript), in this repository's `manuscript/` folder.
- [arXiv:2610.20976v2](https://arxiv.org/abs/2610.20976v2), October 23, 2026: the version the coverage map and scope ledger target. Its source has SHA-256 `0907a3b4dd79a158374d51caa3aebc9a8ddd3fd12bdcc09af0d53ab4b44d2948`.
- The scopes were first reviewed against the October 20, 2026 source (SHA-256 `545c93f8dc375ca9c57547e1cb6a28b8c47209da9ee6c77e42e60884e44ccaae`), which has the same theorem and equation numbering; see [manuscript versions](manuscript-versions.html).
