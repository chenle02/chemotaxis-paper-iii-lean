---
title: Manuscript versions
description: How arXiv v1, the October 20 source and arXiv v2 of Chemotaxis III relate, and what the move to v2 changed in this companion.
---

# Manuscript versions

The coverage map and the [scope ledger](scope-ledger.html) target [arXiv:2610.20976v2](https://arxiv.org/abs/2610.20976v2), submitted on October 23, 2026. Its source is in the [paper repository](https://github.com/chenle02/chemotaxis-paper-iii) at commit `f9aed465`.

| Version | Date | Source SHA-256 | Where |
|---|---|---|---|
| arXiv v1 | October 14, 2026 | — | [arXiv:2610.20976v1](https://arxiv.org/abs/2610.20976v1) |
| October 20 source | October 20, 2026 | `545c93f8…` | paper repository at [`c8aa57b3`](https://github.com/chenle02/chemotaxis-paper-iii/tree/c8aa57b3afffe683a2c5baa38a0fbaaf1c688ad4) |
| arXiv v2 | October 23, 2026 | `0907a3b4…` | [arXiv:2610.20976v2](https://arxiv.org/abs/2610.20976v2); paper repository at [`f9aed465`](https://github.com/chenle02/chemotaxis-paper-iii/tree/f9aed4653e6312726ed1544d6f135fa14a5c6b29) |

The scopes were first reviewed against the October 20 source. [`data/source-baselines/arXiv-2610.20976v2.json`](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/main/data/source-baselines/arXiv-2610.20976v2.json) records the v2 e-print and shows that its main TeX file is the one the paper repository holds.

## Numbering

All 146 labels carry the same theorem, lemma, proposition, remark, equation, section and table numbers in v1, the October 20 source and v2. This was checked from the `.aux` file of a build of each source. Numbers cited in the Lean files and the Challenge files, which name v1, therefore identify the same results in v2.

Page numbers differ. From the October 20 source to v2, five labels move back one page:

| Label | October 20 | v2 |
|---|---|---|
| Section 3 (`S:direction-change`) | 23 | 22 |
| `E:A-closed-form` | 24 | 23 |
| Section 3.2 (`SS:beta-analysis-1`) | 25 | 24 |
| `E:new-beta-eq1` | 27 | 26 |
| Section 4 (`S:global-Bifurcation`) | 28 | 27 |

Page and TeX-line locators in the coverage map, the scope ledger and the generated pages follow v2.

## What v2 changed

No theorem, lemma, proposition, remark or definition statement changed between the October 20 source and v2. Two covered equations changed in form only. In (2.20) the closing period became a comma. In (2.22) the remainder is written `O_{k,u}(‖u‖_{l^1}^4)` instead of `O_{u,k}(‖u‖_{ℓ^1}^4)`. Both rows quote the v2 text.

The other changes are outside the covered statements:

- The abstract describes the spike result as concerning "sequences of stationary solutions with large sensitivity" instead of "large-sensitivity stationary sequences satisfying a peak-gap hypothesis". Theorem 1.4 is unchanged.
- Remark 1.2(1) rewords its comment on sub-critical bifurcation for large β. No coverage row covers Remark 1.2.
- Several sentences that made remainder terms explicit in the proof of Theorem 1.1 were removed or kept only as TeX comments.
- Figure files were renamed, links and citations are black, and a paragraph in Data and code availability links this companion.

## Scopes with an arXiv v2 note

Three ledger scopes refer to proof sentences that v2 no longer states. Each keeps its status and carries an `arxiv_v2_note` in [`data/public-scope-ledger.json`](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/main/data/public-scope-ledger.json); the same note appears on the [scope ledger](scope-ledger.html) page.

| Scope | Status | What v2 no longer states |
|---|---|---|
| `paper3/T:local-bifurcation/branch-curves` | verified-conditional | The derivative remainder estimate in Step 5 of the proof of Theorem 1.1. The Lean deductions keep it as an explicit input. |
| `paper3/R:local-bifurcation-minimal` | verified-conditional | The sentence in Step 4′ extending that estimate to the minimal case. It remains an explicit input. |
| `paper3/E:ode-eq0/projected-remainder` | verified | The source/flux decomposition `R_u = R_u^(0) + ∂_x R_u^(1)` of the remainder in (2.21); v2 keeps it as a TeX comment. The Lean result applies with the remainder read in that form. |

## What did not change

The Lean sources, `claims.yaml` and the release receipts are unchanged. This update changes documentation and metadata only, so the accepted gate receipt at `c749b53b` still binds the published source. `formalization.yaml` still names arXiv v1 as its source, because changing that key needs a new gate receipt. The [Palomar submission](https://github.com/chenle02/chemotaxis-paper-iii-lean/tree/main/palomar) was prepared against v1.
