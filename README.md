<p align="center">
  <img src="assets/chemotaxis-banner.svg" width="560" alt="Cells drifting up a signal gradient toward a spike-like stationary profile">
</p>

# Chemotaxis III: bifurcation and spike-like solutions

Public manuscript and reproducibility materials for **Chemotaxis models with signal-dependent sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions**, by Le Chen, Ian Ruau, and Wenxian Shen.

[![arXiv](https://img.shields.io/badge/arXiv-2610.20976v2-b31b1b)](https://arxiv.org/abs/2610.20976v2)
[![Manuscript](https://img.shields.io/badge/manuscript-arXiv%20v2%2C%20Oct%2023%2C%202026-2a9d8f)](arXiv-2610.20976v2.pdf)
[![Lean companion](https://img.shields.io/badge/Lean%204-partial%20companion-264653)](https://github.com/chenle02/chemotaxis-paper-iii-lean)
[![Docs](https://img.shields.io/badge/Lean%20docs-GitHub%20Pages-1d4a52)](https://chenle02.github.io/chemotaxis-paper-iii-lean/)

- [Read the manuscript PDF](arXiv-2610.20976v2.pdf) (arXiv v2).
- [Published preprint, arXiv:2610.20976v2](https://arxiv.org/abs/2610.20976v2); the first version is [v1](https://arxiv.org/abs/2610.20976v1).
- [Lean companion and verification boundary](https://github.com/chenle02/chemotaxis-paper-iii-lean), with its [documentation site](https://chenle02.github.io/chemotaxis-paper-iii-lean/).

## Abstract

This is the third part of a series of papers on boundedness, global existence, and asymptotic behavior of positive classical solutions to the following parabolic–elliptic chemotaxis model,

```math
\begin{cases}
  u_t=\Delta u- \chi_0\nabla \cdot\Big(\frac{u^m}{(1+v)^\beta}\nabla v\Big)+au-b u^{1+\alpha}, & x \in \Omega, \\
  0=\Delta v-\mu v+\nu u^\gamma, & x \in \Omega, \\
  \frac{\partial u}{\partial n}=\frac{\partial v}{\partial n}=0, & x \in \partial\Omega,
\end{cases}
\qquad \text{(CM)}
```

where $`\Omega`$ is a bounded smooth domain in $`\mathbb{R}^N`$, and the parameters $`\alpha, \gamma, m, \mu, \nu`$ are positive, $`\chi_0 \in \mathbb{R}`$, and $`a, b, \beta`$ are nonnegative. In the first part of this series, we identified several biologically relevant parameter regimes that guarantee the boundedness and global existence of positive classical solutions. In the second part, we investigated the persistence and stabilization of globally defined bounded positive solutions, with particular emphasis on quantifying the effects of the signal-dependence exponent $`\beta`$ and the sign of the sensitivity coefficient $`\chi_0`$ on the long-time dynamics. In this third part, treating $`\chi_0`$ as the bifurcation parameter, we study bifurcation of positive constant equilibria of (CM) when the space dimension $`N = 1`$. We pay special attention to the effects of $`\beta`$ and the domain size on the bifurcation.

By applying center manifold reduction, we derive a quantity $`\beta_{n_0}`$ at a simple bifurcation mode $`n_0`$ of a positive constant solution $`(u^*,v^*)`$, and show that super-critical (resp. sub-critical) pitchfork bifurcation occurs if $`\beta_{n_0} > 0`$ (resp. $`\beta_{n_0} < 0`$) when $`\chi_0`$ passes through the bifurcation threshold $`\chi^*`$. We find two interesting ways in which $`\beta`$ enters: it shifts the bifurcation *threshold*, namely, larger signal-dependence exponent $`\beta`$ needs proportionately larger $`\chi_0`$ for the constant equilibrium to lose linear stability, and it also selects bifurcation *type*, namely, when $`\beta`$ is small, the bifurcation may be super-critical, but when $`\beta`$ is sufficiently large, the bifurcation is always sub-critical. Biologically, $`\beta`$ thus acts twice in the same direction: it makes patterns harder to trigger, and it makes them more likely to appear abruptly rather than to grow continuously from the constant state. We also find some interesting effects of the domain size. For example, it is found that, in the non-minimal model, the bifurcation mode $`n_0`$ becomes larger and larger when the domain size increases and hence a large domain creates more complicated bifurcation patterns. In addition, under suitable conditions we prove unbounded continuation of the local bifurcation branches and prove that sequences of stationary solutions with large sensitivity develop spike-like solutions. We give some numerical analysis of the continuation of local bifurcation and spike-like solutions. Our numerical time-evolution experiments suggest unbounded continuation of local bifurcation branches and increasingly sharp stationary profiles.

## Manuscript version

This repository holds [arXiv:2610.20976v2](https://arxiv.org/abs/2610.20976v2), submitted on October 23, 2026. The TeX source, bibliography and 16 figures are the files of the arXiv e-print, unchanged, and [`arXiv-2610.20976v2.pdf`](arXiv-2610.20976v2.pdf) is the PDF served by arXiv. Their SHA-256 hashes, and that of the e-print archive, are in [manuscript-manifest.json](manuscript-manifest.json). The earlier October 20 source, which the Lean companion was first checked against, remains in this repository's history at commit [`c8aa57b3`](https://github.com/chenle02/chemotaxis-paper-iii/tree/c8aa57b3afffe683a2c5baa38a0fbaaf1c688ad4). It has the same theorem and equation numbering as v2. This repository does not assert journal submission or acceptance.

## Lean verification

The companion distinguishes **47 verified scopes, 23 conditional scopes, and 3 exclusions** across 73 overlapping manuscript-facing scopes. These are not percentages of whole-paper correctness. The current formal library includes 1,525 indexed public declarations; definitions and compiler-generated helpers are not theorem counts.

The actual weak-H2 cosine complement, critical signal response from a supplied population jet and actual elliptic solution family, and conserved-mean quadratic coefficient are formalized. Actual operator/Fredholm identification, local PDE bifurcation, center-manifold construction and invariance, global bifurcation alternatives/correspondence, and PDE stability remain substantive foundations. **The whole paper is not Lean-certified.** See the companion's scope ledger for each precise boundary.

Browse the formal results [by paper section](https://chenle02.github.io/chemotaxis-paper-iii-lean/results.html), or read [what is proved](https://chenle02.github.io/chemotaxis-paper-iii-lean/what-is-proved.html).

## Build

Install TeX Live with pdfLaTeX, latexmk, BibTeX and amsrefs, then run:

```sh
./build.sh
```

The build writes to `build/`, using pdfLaTeX as arXiv does. Its `.aux` and `.bbl` match the committed copies. The committed PDF is the one arXiv serves; a fresh PDF differs in the arXiv stamp, timestamps, metadata and font encoding. The bibliography and all 16 numerical figures are included, at the top level as in the e-print.

## What is in this repository

| Path | Contents |
|---|---|
| [`arXiv-2610.20976v2.pdf`](arXiv-2610.20976v2.pdf) | The manuscript, as served by arXiv |
| [`Chen-Ruau-Shen-JMB.tex`](Chen-Ruau-Shen-JMB.tex), [`references.bib`](references.bib) | LaTeX source and bibliography, from the arXiv e-print |
| `Chen-Ruau-Shen-JMB.aux`, `.bbl` | Cross-reference data and bibliography from a pdfLaTeX build |
| `minimal_{sub,sup}_fig1-4.jpeg`, `non-minimal_{sub,sup}_fig1-4.jpeg` | The 16 numerical figures, in four regimes (minimal/non-minimal, sub-/supercritical) |
| [`manuscript-manifest.json`](manuscript-manifest.json) | SHA-256 of every manuscript file and of the e-print |
| [`build.sh`](build.sh) | Build script with an unresolved-reference check |
| [`CITATION.cff`](CITATION.cff), [`llms.txt`](llms.txt) | Citation metadata; a short map for coding agents |

## Related reusable libraries

- [neumann-cosine-lean](https://github.com/chenle02/neumann-cosine-lean): cosine modes and Neumann spectral calculations.
- [scalar-pitchfork-lean](https://github.com/chenle02/scalar-pitchfork-lean): scalar pitchfork and branch-topology results under explicit hypotheses.

These standalone libraries have their own versioned theorem scopes and receipts; later companion results do not silently extend their APIs.

## Citation and rights

Cite the authors and arXiv:2610.20976v2. See [CITATION.cff](CITATION.cff). Manuscript and figures remain copyright their authors; this repository grants no additional manuscript license. The Lean repositories specify their own software licenses.

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

## Reproducibility, tools and acknowledgments

The manuscript files are copied from the arXiv e-print without edits. Lean verification was developed and checked with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([concept DOI](https://doi.org/10.5281/zenodo.23272098)). AI assistance was used in formalization, tooling, and documentation; the exact Lean statements and explicit hypotheses govern the formal claims.

An accepted verification gate of the Lean companion ran on the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html), during its private development; see the companion's [acknowledgments](https://chenle02.github.io/chemotaxis-paper-iii-lean/acknowledgments.html) for the scope of that run.

The manuscript's own acknowledgments, funding statement, data and code availability, and AI declaration are at the end of the [PDF](arXiv-2610.20976v2.pdf).
