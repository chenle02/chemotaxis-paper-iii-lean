---
title: Where the Lean differs from the paper
description: One numbered list of weaker conclusions, special cases, supplied inputs and definitional choices, against arXiv v2.
---

# Where the Lean differs from the paper

This page lists, in one numbered list, every place where the Lean companion proves less than, or something
different from, the numbered results of the paper: Le Chen, Ian Ruau and Wenxian Shen, *Chemotaxis models with
signal-dependent sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions*,
[arXiv:2610.20976v2](https://arxiv.org/abs/2610.20976v2) (source in [`manuscript/`](https://github.com/chenle02/chemotaxis-paper-iii-lean/tree/main/manuscript)). Result
numbers are those of v2; v1 uses the same numbers.

Words used below:

- **Supplied input:** a hypothesis of a Lean theorem that stands in for a step the Lean does not prove, such as a
  result the paper cites or a computation it carries out elsewhere. Lean checks the deduction *from* the input,
  not the input.
- **Comparator:** a separate checker that confirms a proof proves exactly a given statement, using only Lean's
  three standard axioms.
- **Challenge:** a file that restates chosen theorems using only Mathlib, with the proofs left out, so that a
  reader can compare them with the mathematics without reading the proof library.

The entries are derived from the coverage map ([`coverage.yaml`](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/main/coverage.yaml): each row's class, inputs and
note), the [scope ledger](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/main/data/public-scope-ledger.json) and the Lean statements shown on the
[verification page](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/main/docs/verification.md). Where a Lean name is given, its full statement is on that page.

## Weaker conclusions: only part of a result is proved

1. **Proposition 1.1 (linear stability and instability).** The paper states that $(u^{\ast},v^{\ast})$ is linearly
   exponentially stable for $\chi_0<\chi^{\ast}(u^{\ast})$ and linearly unstable for $\chi_0>\chi^{\ast}(u^{\ast})$. Lean proves only
   the sign algebra of the linear growth rates, one Fourier mode at a time: for an eigenvalue $\lambda>0$, the
   growth rate is negative, zero or positive exactly when $\chi_0$ is below, at or above that mode's threshold;
   the minimizing mode does not depend on $\beta$; and at the critical value every other positive mode decays.
   The semigroup estimates and the stability conclusions for the PDE are not formalized. The generated card for
   this result says "Verified" and "the Lean statement assumes nothing the paper does not": both are true of the
   Lean statements, which concern the growth rates only. Lean: `PhysicalLinearRegime.physicalGrowth_neg_iff`,
   `physicalGrowth_pos_iff`, `physicalGrowth_zero_iff`, `minimizingMode_beta_iff`,
   `strictCriticalMode_other_growth_neg`, `criticalSensitivity_eq_chiStar`.
2. **Theorem 1.1 (local pitchfork bifurcation).** Lean treats only the scalar reduced equation
   $\dot s=\alpha\eta s-\beta s^3+R(\eta,s)$, with $\eta=\chi_0-\chi^{\ast}$, and takes the bounds on $R$ and on its
   $s$-derivative as supplied inputs (entry 10). From these it proves that for small $\eta$ on the side given by
   the sign of $\beta$ there is exactly one small root of each sign, within $O(\eta)$ of
   $\pm\sqrt{\alpha\eta/\beta}$, that the roots depend continuously on $\eta$ (given, in addition, that $R$ is
   continuous in $\eta$), and that the derivative of the field at the root has the sign of $-\beta$. Not
   formalized: the centre-manifold reduction from the PDE to this equation, the curves $\Gamma^\pm_{n_0}$ of
   stationary solutions in $C^2\times C^2$, the expansions of $u^\pm$ and $v^\pm$, and the linear stability of
   the bifurcating solutions. Lean: `MixedRemainder.mixed_branch_eventually`,
   `BranchCurves.branchRoot_existsUnique_eventually`, `BranchCurves.branch_curves`.
3. **Theorem 1.2(2), minimal model.** For the minimal model Lean proves the rational form
   $\beta_{n_0}=P(\lambda_{n_0})/(24(u^{\ast})^2(\mu+\lambda_{n_0})^2)$ with $\deg P\le 3$ and a positive denominator
   (`MinimalRational.fixedMassBetaCoefficient_eq_cubic_ratio`). The limits as $L\to0$ and $L\to\infty$ and the
   count "the bifurcation type changes at most three times" are proved only for the non-minimal model
   (`CoefficientLimits`, `ModeRootCounts.actual_zero_lengths_card_le_five`); no Lean statement covers them for
   the minimal model.
4. **Theorem 1.2, "bifurcation type".** Lean proves the statements about the number $\beta_{n_0}$: its sign, its
   quadratic dependence on $\beta$, its rational dependence on $\lambda_{n_0}$, its zeros and limits. The paper
   reads a positive (negative) $\beta_{n_0}$ as a super-critical (sub-critical) bifurcation; that reading is
   Theorem 1.1, which is not formalized for the PDE (entry 2).
5. **Theorem 1.3(1) (global alternatives).** Lean proves that the selected components
   $\mathcal{C}^\pm_{n_0}$ are relatively closed and contain $(\chi^{\ast},u^{\ast})$, from supplied topological inputs
   (entry 12). The three alternatives (non-compact; returns to the constant branch; meets $u^{\ast}+W$) are not proved:
   they are the global bifurcation theorem of Shi and Wang, which the paper applies and the Lean takes as an
   input. Lean: `selectedComponent_isClosed`, `base_mem_selectedComponent`.
6. **Theorem 1.3(3) (minimal model, first mode).** Proved in full: for any sequence of positive stationary
   solutions of the minimal model with prescribed mass $Lu^{\ast}$, strictly decreasing (increasing) on $[0,L]$, with
   $\chi_j\to\infty$, $1\le m$, $\beta\ge0$ and $0<\gamma\le1$, one has $\int_0^L f(x)u_j(x)dx\to Lu^{\ast}f(0)$ (resp.
   $Lu^{\ast}f(L)$) for every continuous $f$, the measures $u_j(x)dx$ converge to $Lu^{\ast}$ times the Dirac mass at that
   endpoint, and $u_j(0)\to\infty$ (resp. $u_j(L)\to\infty$). Lean:
   `PhysicalEndpointConcentration.decreasing_actual_concentration`, `increasing_actual_concentration`. Proved only
   from supplied inputs: that alternatives (ii) and (iii) fail and that the components are non-compact and
   unbounded in $\chi_0$ (`GlobalBranch.part3_global`, which takes the global alternatives and the monotonicity
   of the solutions on the component as hypotheses); and that every nonconstant solution on
   $\mathcal{C}^\pm_1$ is strictly monotone (`MonotoneLocusGeneral.part3_strictAnti_of_ode`, from supplied
   local-branch inputs, entry 13).

## Special cases

7. **Theorem 1.4 in the minimal model.** The Lean statement does not assume that the solutions are
   nonconstant, so it is slightly more general than the paper's. The paper's hypothesis
   $\liminf_n\max_{[0,L]}u_n>u^{\ast}$ appears in Lean in the equivalent form "there is $\ell_0>u^{\ast}$ with
   $\max_{[0,L]}u_n\ge\ell_0$ for all large $n$".
8. **Proof steps proved for one case.** None of the six main results is proved only for a special case of the
   paper's parameters. Several supporting rows of the coverage map cover one case of a proof step and say so in
   their titles, for example the case $m=1$ in the proof of Lemma 4.2(2) and the route through Eq. (4.11) for
   $1\le m<(\alpha+2)/2$ in Lemma 4.1(2). Some Lean statements cover a wider range than the paper: the
   concentration statement of Theorem 1.3(3) holds for all $m\ge1$, which contains the paper's $1\le m\le2$.

## Supplied inputs

9. **Theorem 1.2 (both parts).** Lean proves its statements about the explicit formula for $\beta_{n_0}$,
   Eq. (2.45) (Eq. (2.49) in the minimal model). Supplied input: that this formula is the cubic coefficient of the
   reduced equation, that is, the centre-manifold computation of Section 2 (the quadratic centre-graph
   coefficients (2.33) and (2.36b) and the cubic projection (2.41)). Lean checks the algebra of that computation
   too, but only from further supplied inputs: the invariance equations of the centre graph, integrability of the
   projected terms, and a zero critical projection of the cubic graph term (coverage rows for Eqs. (2.33),
   (2.36b), (2.41), (2.45)).
10. **Theorem 1.1 and Remark 1.1(1).** Supplied inputs: the identification of $\eta=\chi_0-\chi^{\ast}$ and
    $s=u_{n_0}$ with the reduced scalar equation (the centre-manifold reduction, which the paper takes from
    centre-manifold theory); $\alpha>0$, $\beta\ne0$; the bound
    $|R(\eta,s)|\le C(|s|\eta^2+|s|^3|\eta|+s^4)$ on a box; differentiability of $R$ in $s$; and the bound
    $|R_s(\eta,s)|\le C(\eta^2+s^2|\eta|+|s|^3)$. The proof of Theorem 1.1 in v2 no longer states this derivative
    bound (the October 20 source did); Lean keeps it as an explicit input. For the minimal model (Remark 1.1(1))
    the fixed-mass reduction is also supplied.
11. **Proposition 1.1.** The paper quotes it from the authors' Part II (Chen, Ruau and Shen,
    [arXiv:2604.02599](https://arxiv.org/abs/2604.02599v1)). Only the modewise algebra is in Lean (entry 1).
12. **Theorem 1.3(1) and (2).** Supplied inputs: the unilateral global bifurcation alternatives of Shi and Wang
    (J. Shi and X. Wang, *On global bifurcation for quasilinear elliptic systems on bounded domains*, J.
    Differential Equations 246 (2009) 2788–2812, Theorem 4.4) for the selected branches; the admissible set and
    its topology; the identification of the paper's stationary solution set with the sets Lean uses; relative
    closedness of the component and its inclusion in the admissible set and in $\overline{\mathcal{S}}$; the
    inclusion $\overline{\mathcal{S}}\subset(0,\infty)\times\mathcal{A}$; and compactness of every slice of
    solutions with bounded sensitivity, which the paper obtains from PDE a priori estimates and a compact
    embedding. From these, Lean proves part (2): a non-compact component reaches arbitrarily large $\chi_0$
    (`GlobalBranch.part2_sSup_eq_top`). Lean separately proves closure and compactness facts for classical
    stationary solutions (`AmbientClosure`, `BoundedSolutionSlices`), but their identification with the paper's
    weak $H^2$ sets remains an input.
13. **Theorem 1.3(3).** Supplied inputs, besides those of entry 12: the global alternatives for $\mathcal{C}^\pm_1$;
    the monotonicity of the solutions on the component, or, in the monotone-locus argument, the local
    representation of the branch near the constant solution and its half-branch parametrization (named `hConst`
    and `hStar` in the Lean); the orthogonality of $W$ to the first cosine mode.
14. **Equation (2.16), the centre manifold as a graph over the critical mode.** Not formalized; it is used only as
    an input to the finite-order computations of entry 9.

## Definitional choices that could matter

15. **Stationary solutions.** A classical stationary solution is a Lean record (`ClassicalProfile`, `SignalData`)
    that lists $u$, $v$ and their derivatives, continuity on $[0,L]$, the two equations on $(0,L)$ and the
    Neumann conditions at both ends. Positivity is a separate hypothesis of each theorem.
16. **Weak convergence (Theorem 1.4).** Weak convergence in $L^q$ and in $W^{2,q}$ is stated as convergence of
    $\int u^\gamma g$, $\int v g$, $\int v_x g$ and $\int v_{xx} g$ for every $g$ in the dual space $L^{q'}$ on
    $[0,L]$, not through a Sobolev-space object. Convergence of $v$ in $C^1$ is uniform convergence of $v$ and of
    $v_x$.
17. **Thresholds.** In Lean, `chiStar x beta` is the threshold of the single mode with eigenvalue $x$ (the
    paper's $\chi_n$, Eq. (1.9)); the paper's $\chi^{\ast}$, the infimum over modes, is `continuumCritical`.
18. **Division.** Lean divides by zero without error (the result is $0$), so formulas such as the thresholds are
    defined for all inputs. The theorems carry the hypotheses that make denominators positive or nonzero, and
    those hypotheses are part of the statements shown.
19. **The complement $W$.** Lean constructs the complement of the critical cosine mode as the closed kernel of
    its Fourier coefficient in the weak $H^2$ Neumann phase space. This is a geometric complement; it is not
    identified with the range of the linearized operator or with its stable spectral subspace.
20. **Equation (2.22).** The Lean result reads the remainder in the source-and-flux form
    $R_u=R_u^{(0)}+\partial_x R_u^{(1)}$, which v2 keeps only as a TeX comment.
21. **Two v1 misprints.** Lean follows the corrected statements, which v2 now prints: Theorem 1.2(1)(iii) with
    "$\beta\ge0$, $\beta\ne\beta_0$", and Eq. (1.24) as the eigenvalues of $-\Delta_h$.

## The Challenge

22. **`HeadlineChallenge.lean` states twelve ingredient lemmas, not the paper's main theorems.** They are a
    product formula for cosine series (Lemma 2.1), the scalar branch roots and their uniqueness (Theorem 1.1, Step
    5, at the level of the reduced equation), an asymptotic of $\beta_{n_0}$ (Eq. (3.7)), bounds for stationary
    solutions (Lemma 4.1(1)), the flux identity and exponential representation of the minimal model (proof of
    Lemma 4.2(2)), small local mass (Remark 1.3(2)), Dirac convergence of measures with vanishing tails
    (Theorem 1.3(3)), a first-mode lemma (proof of Theorem 1.3(3)), and two limit lemmas (Lemma 5.1, Theorem 1.4).
    Its comments cite arXiv v1; the numbers are the same in v2. The comparator checked these twelve statements
    and 108 others in `Challenge.lean` at commit `c749b53b0221`. Re-anchoring the Challenge to v2, or stating
    Theorems 1.1, 1.3 and 1.4 themselves, needs a new comparator run: any edit to `HeadlineChallenge.lean`, even
    to a comment, changes a file the build reads, and the recorded evidence then no longer certifies the new
    commit. It is therefore left unchanged here.
