# Palomar submission candidate: twelve analytic and scalar bifurcation results

Status: prepared for review; not submitted or registered.

This submission selects **only the twelve declarations in
[`comparator.headline.json`](../comparator.headline.json)**. The formal statement
is [`HeadlineChallenge.lean`](../HeadlineChallenge.lean), which imports Mathlib
alone; the proofs are in [`HeadlineSolution.lean`](../HeadlineSolution.lean).
Use [`palomar/formalization.yaml`](formalization.yaml) as the submission metadata,
with the repository root as the project directory. Do not select the larger
`comparator.json`: its Challenge is an internal audit surface exceeding Palomar's
1,000-line limit.

The research audience is analysts studying stationary chemotaxis, scalar
bifurcation reductions, concentration and singular limits. The results separate
reusable analytic deductions from the PDE constructions needed to apply them.
They support the paper by Le Chen, Ian Ruau and Wenxian Shen,
[Chemotaxis III, arXiv:2610.20976v1](https://arxiv.org/abs/2610.20976v1).
The repository's current manuscript mapping also uses the October 20 candidate;
that candidate is not asserted to be an uploaded arXiv v2. Numerical paper
locators already in the Challenge refer to v1 and have not been independently
rechecked as part of this submission preparation. The formal types govern scope.

## Mathematical account of every selected result

Every hypothesis below is part of the statement being registered. The exact
quantifiers, constants and bounds are written in the linked Challenge.

| Declaration suffix | Mathematical content and supplied inputs |
| --- | --- |
| `TrigIntegrals.cos_cos_cos_cos_lp` | For a positive interval length and three absolutely summable cosine coefficient sequences, integrates their product against a fourth cosine. The answer is a sum over seven signed frequency constraints, with the separate constant-mode correction. No bifurcation theorem is asserted. |
| `MixedRemainder.center_ODE_final_branch_eventually` | For a scalar cubic field with positive linear coefficient and nonzero cubic coefficient, explicit value and derivative remainder bounds imply a small root of each sign on the bifurcating side, an explicit error bound from the square-root leading term, and a derivative sign at those roots. The remainder bounds are hypotheses; no PDE reduction or center manifold is constructed. |
| `NormalizedAsymptotic.coefficient_sub_linear_isBigO` | The explicit rational coefficient printed in the Challenge differs from its stated linear function by a bounded term as the mode parameter tends to positive infinity. This verifies the displayed algebraic expression, without independently identifying it with the PDE coefficient. |
| `IntervalMoments.logistic_interval_bounds` | A continuous, positive, nonconstant density satisfying the logistic integral identity has minimum below and maximum above the positive equilibrium, and strict bounds on its mass and higher moment. Positivity of the coefficients, exponent and interval length, nonconstancy and the integral identity are supplied. |
| `MinimalFlux.minimal_flux_identity` | Continuous flux and derivative data satisfying the interior stationary derivative equation and zero boundary derivative/flux imply equality of the two flux terms throughout the interval. The functions named as derivative data have exactly the derivative relations shown in the Challenge; an identification of every datum with a PDE derivative is not added implicitly. |
| `MinimalFlux.minimal_exp_representation` | A positive continuous density with its stated interior derivative and first-order flux identity equals its value at any basepoint times the exponential of the integrated logarithmic derivative. Continuity of the integrand and the flux identity are hypotheses. |
| `NoDiracMass.window_mass_tendstoUniformly` | A family of positive, continuous, nonconstant densities satisfying the same logistic identity has mass in shrinking windows tending uniformly to zero, simultaneously over the family and window centers. The result uses fixed positive logistic parameters and interval length. It does not exclude concentration for arbitrary chemotaxis regimes. |
| `EndpointConcentration.tendsto_mass_smul_dirac_of_vanishing_tails` | Finite measures of fixed positive mass converge weakly to a Dirac measure at a designated point if mass outside every open neighborhood of that point tends to zero. The topological and measurability assumptions and tail property are supplied. Deriving the tail property from a PDE is outside this statement. |
| `GlobalBranch.mode_eq_one_of_monotone_limit` | A monotone or antitone small-amplitude cosine expansion with nonzero amplitudes and uniform remainder negligible relative to amplitude must have first mode. The expansion and its uniform bound are hypotheses. This is a mode-selection argument, not global branch existence. |
| `SpikeLimit.limit_eq_const` | Nonnegative continuously differentiable signal data, an integrable population limit, an integrated elliptic relation, the endpoint derivative condition, and almost-everywhere vanishing of population times signal derivative force a constant signal and an almost-everywhere constant population. Constructing the limit and proving these relations are outside this statement. |
| `SpikeLimit.spike_limit_constant_le` | Nonnegative continuous densities with a bounded higher moment and convergence of a lower moment give a nonnegative limiting constant bounded by the corresponding equilibrium power. The exponent range, moment bound and convergence are explicit hypotheses. |
| `BranchCurves.branchRoot_existsUnique_eventually` | Explicit value and derivative bounds on a scalar remainder imply exactly one nonzero root of each sign in a fixed sufficiently small window for small parameters on the bifurcating side. These bounds differ from the second row's bounds and are not silently identified. This proves scalar uniqueness under those bounds, not uniqueness or exhaustion of PDE solution branches. |

## Provenance, review and limitations

Le Chen is responsible for the Lean formalization. Le Chen, Ian Ruau and Wenxian
Shen are the paper's authors. Codex CLI and Claude Code assisted with proofs,
tooling, documentation and fidelity review; they are not listed as human authors.
Mathlib and the pinned Lean toolchain provide the foundational library.

The supplied statements are source-based analytic results and deductions,
including an explicit scalar uniqueness argument used in the analysis. No claim
of novelty, priority, human expert endorsement or complete paper verification is
made. This preparation does not confer Gold status. The wider companion retains
47 verified, 23 conditional and 3 excluded overlapping manuscript-facing scopes;
those counts are not twelve result counts or a correctness percentage.

Historical source and Comparator receipts are preserved in `.lean-receipts/`.
They distinguish the original source build, a refused producer envelope, its
accepted phase-collection successor, and Comparator reuse of compiled scientific
outputs. A metadata-only submission descendant does not retrospectively become a
fresh full-library build. Challenge `sorry` holes are intentional; the selected
Solution proofs must use only `propext`, `Quot.sound` and `Classical.choice`.
Palomar will perform its own verification and automated editorial review if a
submission is authorized.

Full PDE local bifurcation and branch exhaustion, center-manifold construction,
operator/Fredholm identification, global continuation and PDE stability remain
outside this submission. The conditional analytic inputs are not custom axioms
and must not be described as already established for every PDE solution.

## Mechanical preflight before intake

The preparation branch's manual `lean.yml` workflow calls Palomar's complete
reusable verifier at immutable revision
`ad5db9e7ff8b17523d73aeb244aaeabcde810c64`, with `mode: full`,
`execution_profile: palomar-standard-v1`, and the same revision as
`pipeline_commit`. It checks this branch's exact commit, the headline Comparator
configuration and this directory's metadata. It has read-only repository
permissions and no automatic push or pull-request trigger. The released main
branch's workflow is unchanged.

A passing local Comparator replay or metadata check is not equivalent to that
complete preflight. Before actual intake, retain a `status: pass` mechanical
report for the exact selected source commit. Intake and permanent registration
remain separate actions; no registration is authorized by preparing this packet.
