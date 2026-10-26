# Chemotaxis III manuscript

The source and PDF of **Chemotaxis models with signal-dependent sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions**, by Le Chen, Ian Ruau, and Wenxian Shen: [arXiv:2610.20976v2](https://arxiv.org/abs/2610.20976v2), submitted October 23, 2026. The first version is [v1](https://arxiv.org/abs/2610.20976v1).

- [Read the PDF](arXiv-2610.20976v2.pdf), as served by arXiv.
- The Lean companion is the rest of [this repository](../README.md), with its [documentation site](https://chenle02.github.io/chemotaxis-paper-iii-lean/). It formalizes selected results and conditional deductions; **the whole paper is not Lean-certified**.

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

## Files

The TeX source, bibliography and 16 figures are the files of the arXiv e-print, unchanged. [`manuscript-manifest.json`](manuscript-manifest.json) records the SHA-256 of every file and of the e-print archive.

| Path | Contents |
|---|---|
| [`arXiv-2610.20976v2.pdf`](arXiv-2610.20976v2.pdf) | The manuscript, as served by arXiv |
| [`Chen-Ruau-Shen-JMB.tex`](Chen-Ruau-Shen-JMB.tex), [`references.bib`](references.bib) | LaTeX source and bibliography, from the arXiv e-print |
| `Chen-Ruau-Shen-JMB.aux`, `.bbl` | Cross-reference data and bibliography from a pdfLaTeX build |
| `minimal_{sub,sup}_fig1-4.jpeg`, `non-minimal_{sub,sup}_fig1-4.jpeg` | The 16 numerical figures, in four regimes (minimal/non-minimal, sub-/supercritical) |
| [`manuscript-manifest.json`](manuscript-manifest.json) | SHA-256 of every manuscript file and of the e-print |
| [`build.sh`](build.sh) | Build script with an unresolved-reference check |

## Build

Install TeX Live with pdfLaTeX, latexmk, BibTeX and amsrefs, then run `manuscript/build.sh` from anywhere. The build writes to `manuscript/build/`, using pdfLaTeX as arXiv does; its `.aux` and `.bbl` match the committed copies. A fresh PDF differs from the arXiv one in the arXiv stamp, timestamps, metadata and font encoding.

## History

This folder was the separate repository `chenle02/chemotaxis-paper-iii` until October 26, 2026, and keeps its full history. The October 20, 2026 source, against which the Lean scopes were first reviewed, is at commit [`c8aa57b3`](https://github.com/chenle02/chemotaxis-paper-iii-lean/tree/c8aa57b3afffe683a2c5baa38a0fbaaf1c688ad4); it has the same theorem and equation numbering as v2. See [manuscript versions](https://chenle02.github.io/chemotaxis-paper-iii-lean/manuscript-versions.html).

## Rights and citation

The manuscript and figures remain copyright their authors. The repository's Apache-2.0 license covers the Lean companion and its tooling, not the files in this folder; no additional manuscript license is granted. Cite the authors and arXiv:2610.20976v2; see the repository's [CITATION.cff](../CITATION.cff).

The manuscript's own acknowledgments, funding statement, data and code availability, and AI declaration are at the end of the [PDF](arXiv-2610.20976v2.pdf).
