---
title: Chemotaxis III in Lean
description: Partial Lean 4 formalization of Chemotaxis III, with an explicit verified, conditional and excluded scope ledger.
permalink: /
---

<section class="hero">
<p class="eyebrow">Lean 4 / Mathlib companion · release v0.1.1</p>
<h1>Chemotaxis III in Lean</h1>
<img class="banner" src="{{ '/assets/chemotaxis-banner.svg' | relative_url }}" alt="Cells drifting up a signal gradient toward a spike-like stationary profile">
<p class="lead">A Lean 4 / Mathlib companion formalizing coefficient calculations, stationary estimates, compactness and conditional bifurcation deductions for Chemotaxis III.</p>
<p class="actions"><a class="button" href="{{ '/what-is-proved.html' | relative_url }}">What is proved</a> <a class="button secondary" href="{{ '/verification.html' | relative_url }}">Exact Lean statements</a> <a class="button secondary" href="{{ '/reproducing.html' | relative_url }}">Reproduce</a></p>
</section>

## What is proved

The library supplies finite coefficient and modal identities, classical stationary mass and regularity estimates, weak limits and spike subsequences under stated inputs, bounded-sensitivity compactness, actual weak-H2 cosine coordinates and complement splitting, and conditional local/global branch deductions. The latest additions also derive the critical modal signal response from an actual elliptic solution family and a supplied population jet, and a quadratic coefficient from conserved mass.

The [scope ledger](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/main/data/public-scope-ledger.json) retains **47 verified scopes, 23 conditional scopes, and 3 exclusions** across **73 overlapping manuscript-facing scopes**. These counts are not a percentage of whole-paper correctness. The library has 1,525 indexed declarations, including definitions; compiler-generated auxiliaries are not counted as new mathematical theorems.

<div class="boundary" markdown="1">
**Not proved here:** whole-paper correctness, actual stationary operator/Fredholm identification, construction/exhaustion of the local PDE branch, a center manifold with dynamical invariance, global bifurcation alternatives and correspondence, or PDE stability. Supplied families, phase-norm jets, chart/exhaustion data, critical-parameter identifications and other named inputs remain explicit where used. A geometric Fourier complement is not identification with an operator's range or stable spectrum.
</div>

## Find your way

### Results

<div class="cards">
<div class="card"><h4><a href="{{ '/what-is-proved.html' | relative_url }}">What is proved</a></h4><p>Result families, the sign-off boundary and selected statement cards.</p></div>
<div class="card"><h4><a href="{{ '/results.html' | relative_url }}">Results by paper section</a></h4><p>Every formalized result, grouped under the manuscript section that states it.</p></div>
<div class="card"><h4><a href="{{ '/verification.html' | relative_url }}">All Lean statements</a></h4><p>Generated page: each result's Lean statement, hypotheses and the checks that ran.</p></div>
<div class="card"><h4><a href="{{ '/scope-ledger.html' | relative_url }}">Scope ledger</a></h4><p>All 73 primary scopes with manuscript numbering and pages.</p></div>
</div>

### Trust and reproduction

<div class="cards">
<div class="card"><h4><a href="{{ '/trust.html' | relative_url }}">Trust and axioms</a></h4><p>Allowed axioms, comparator coverage and how the public source relates to the accepted source.</p></div>
<div class="card"><h4><a href="{{ '/reproducing.html' | relative_url }}">Reproduce</a></h4><p>Beginner guide to <code>./verify.sh</code>, the pinned toolchain and troubleshooting.</p></div>
<div class="card"><h4><a href="{{ '/evidence/' | relative_url }}">Release evidence</a></h4><p>Phase-composite manifest, recovery summary and logs.</p></div>
<div class="card"><h4><a href="{{ '/acknowledgments.html' | relative_url }}">Acknowledgments and citation</a></h4><p>Authors and AI disclosure, lean-pkg, the Auburn University Easley Cluster, and how to cite.</p></div>
</div>

## Paper

Le Chen, Ian Ruau and Wenxian Shen, *Chemotaxis models with signal-dependent sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions*.
[Manuscript source and PDF](https://github.com/chenle02/chemotaxis-paper-iii-lean/tree/main/manuscript) ·
[arXiv:2610.20976v2](https://arxiv.org/abs/2610.20976v2), the version the scope ledger maps ([manuscript versions](manuscript-versions.html)).

## Use it

```sh
git clone https://github.com/chenle02/chemotaxis-paper-iii-lean.git
cd chemotaxis-paper-iii-lean
./verify.sh
```

```toml
[[require]]
name = "chemotaxis-bifurcation-lean"
git = "https://github.com/chenle02/chemotaxis-paper-iii-lean"
rev = "v0.1.1"
```

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html); [what ran there](acknowledgments.html#auburn-university-easley-cluster).
Coding agents: start from [llms.txt](https://raw.githubusercontent.com/chenle02/chemotaxis-paper-iii-lean/main/llms.txt).
