module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import ChemotaxisBifurcation.MobilityDerivatives
public import ChemotaxisBifurcation.ConstantModeJet
public import ChemotaxisBifurcation.BetaDecomposition
public import ChemotaxisBifurcation.PhysicalBetaRegimes
public import ChemotaxisBifurcation.NormalizedSpecialization

@[expose] public section

/-!
# Named identifications of manuscript coefficients

Short corollaries that name, in the manuscript's own form, coefficients whose ingredients are
already proved elsewhere. References are to arXiv:2610.20976v1.

* `B0_Bu_Bv_eq` (Equation 2.8): `B₀`, `B_u`, `B_v` are the value and the two first partial
  derivatives of the mobility `u^m (1+v)^{-β}` at `(u*, v*)`.
* `beta_n0_pq_logistic`, `beta_n0_pq_fixedMass` (Equation 3.1): the dictionary between the
  rational fields `bAsecond`, `bAthird` and the physical `b A''`, `b A'''` of (2.10), and the
  constant-mode choice `a_{0,1}` (the value (2.33) in the logistic model, `0` in the
  fixed-mass minimal model, where also `b A'' = b A''' = 0` and `β_{n₀} = -q(β)`).
* `physicalBetaA_neg_fixedMass` (Equation 3.4 for the minimal model): the leading coefficient
  `A` of the minimal-model `β_{n₀}(β)` is the same `physicalBetaA` and is negative.
* `example_3_1_display` (Example 3.1): the all-ones logistic coefficient equals the displayed
  quotient, written out coefficient by coefficient.
-/

namespace ChemotaxisBifurcation.CoefficientDictionary

open ChemotaxisBifurcation
open ChemotaxisBifurcation.BetaDecomposition
open ChemotaxisBifurcation.PhysicalModeGuards

noncomputable section

/-- **Equation 2.8.** At a positive equilibrium `(u*, v*)` with `1 + v* > 0`, the mobility
`B(u, v) = u^m (1+v)^{-β}` has value `B₀ = (u*)^m/(1+v*)^β` and first partial derivatives
`B_u = m (u*)^{m-1}/(1+v*)^β` and `B_v = -β (u*)^m/(1+v*)^{β+1}`. -/
theorem B0_Bu_Bv_eq (m beta uStar vStar : ℝ) (hu : 0 < uStar) (hv : 0 < 1 + vStar) :
    mobilityInU m beta (1 + vStar) uStar = uStar ^ m / (1 + vStar) ^ beta ∧
    deriv (mobilityInU m beta (1 + vStar)) uStar =
      m * uStar ^ (m - 1) / (1 + vStar) ^ beta ∧
    deriv (fun z : ℝ => mobilityInW m beta uStar (1 + z)) vStar =
      -beta * uStar ^ m / (1 + vStar) ^ (beta + 1) := by
  have hneg : ∀ y : ℝ, (1 + vStar) ^ (-y) = ((1 + vStar) ^ y)⁻¹ :=
    fun y => Real.rpow_neg hv.le y
  refine ⟨?_, ?_, ?_⟩
  · rw [mobilityInU, hneg, div_eq_mul_inv]
  · rw [(mobilityInU_hasDerivAt_normalized m beta (1 + vStar) uStar hu).deriv, hneg,
      div_eq_mul_inv]
  · rw [(mobilityInV_hasDerivAt m beta uStar vStar hv).deriv,
      show -beta - 1 = -(beta + 1) by ring, hneg, div_eq_mul_inv]

/-- **Equation 3.1, logistic model** (dictionary check). Under the logistic equilibrium
relation `a = b (u*)^α`: the rational fields are `bAsecond = b A''` and `bAthird = b A'''`
with `A''`, `A'''` the factorial-normalized Taylor coefficients of (2.10); the constant mode
is `a_{0,1} = -bA''/(2aα)`, which is the value `-(1+α)/(4u*)` of (2.33) when `a, α > 0`; and
the assembled coefficient `logisticBetaCoefficient`, whose quadratic jet carries
`a0 = logisticA0`, is the right side of (3.1) written with `b A''`, `b A'''`. -/
theorem beta_n0_pq_logistic (p : PhysicalParams) (x beta : ℝ)
    (hu : 0 < p.uStar) (hlog : p.LogisticEquilibrium) :
    (mobilityScaledTaylor p beta).bAsecond = p.b * (rawTaylorData p 0).Asecond ∧
    (mobilityScaledTaylor p beta).bAthird = p.b * (rawTaylorData p 0).Athird ∧
    (rawTaylorData p 0).Asecond = (1 + p.alpha) * p.alpha * p.uStar ^ (p.alpha - 1) / 2 ∧
    (rawTaylorData p 0).Athird =
      (1 + p.alpha) * p.alpha * (p.alpha - 1) * p.uStar ^ (p.alpha - 2) / 6 ∧
    (logisticQuadraticJet p x beta).a0 = logisticA0 p ∧
    logisticA0 p = -(p.b * (rawTaylorData p 0).Asecond) / (2 * (p.a * p.alpha)) ∧
    logisticBetaCoefficient p x beta =
      p.b * (rawTaylorData p 0).Asecond / 2 * (4 * logisticA0 p + 2 * pTerm p x beta) -
        qTerm p x (logisticA0 p) beta + 3 * (p.b * (rawTaylorData p 0).Athird) / 4 := by
  have h2 : (mobilityScaledTaylor p beta).bAsecond = p.b * (rawTaylorData p 0).Asecond :=
    (bAsecond_eq_scaled p hu hlog).symm
  have h3 : (mobilityScaledTaylor p beta).bAthird = p.b * (rawTaylorData p 0).Athird :=
    (bAthird_eq_scaled p hu hlog).symm
  refine ⟨h2, h3, rfl, rfl, rfl, ?_, ?_⟩
  · rw [logisticA0, ← (bAsecond_eq_scaled p hu hlog), PhysicalParams.logisticSlope]
  · have h := betaCoefficientAtA0_eq_pq p x (logisticA0 p) beta
    rw [h2, h3] at h
    exact h

/-- The (2.33) value of the logistic constant mode, restated beside the dictionary: for
`a, α, u* > 0`, `logisticA0 = -(1+α)/(4u*)`. -/
theorem logisticA0_eq_233 (p : PhysicalParams) (ha : 0 < p.a) (halpha : 0 < p.alpha)
    (hu : 0 < p.uStar) : logisticA0 p = -(1 + p.alpha) / (4 * p.uStar) :=
  ConstantModeJet.logisticA0_eq_explicit p ha halpha hu

/-- **Equation 3.1, fixed-mass minimal model** (dictionary check). With `a = b = 0` the
logistic fields vanish, `bAsecond = bAthird = 0`; the quadratic jet of the minimal model
carries `a0 = fixedMassA0 = 0`; hence `β_{n₀}(β) = -q(β)` (v1, paragraph after (3.5)). -/
theorem beta_n0_pq_fixedMass (p : PhysicalParams) (x beta : ℝ) (ha : p.a = 0) :
    (mobilityScaledTaylor p beta).bAsecond = 0 ∧
    (mobilityScaledTaylor p beta).bAthird = 0 ∧
    (fixedMassQuadraticJet p x beta).a0 = 0 ∧
    fixedMassBetaCoefficient p x beta = -qTerm p x fixedMassA0 beta := by
  have h2 : (mobilityScaledTaylor p beta).bAsecond = 0 := by
    simp [mobilityScaledTaylor, ha]
  have h3 : (mobilityScaledTaylor p beta).bAthird = 0 := by
    simp [mobilityScaledTaylor, ha]
  refine ⟨h2, h3, rfl, ?_⟩
  have h := betaCoefficientAtA0_eq_pq p x fixedMassA0 beta
  rw [h2, h3] at h
  change betaCoefficientAtA0 p x fixedMassA0 beta = _
  rw [h]; ring

/-- **Equation 3.4, minimal model.** For fixed-mass admissible parameters (`a = b = 0`) and a
strict critical mode, the minimal-model coefficient `β_{n₀}(β)` (constant mode `a0 = 0`) is
the quadratic `A β² + B β + C` with the same leading coefficient `A = physicalBetaA` as in the
logistic model, and `A < 0`. This instantiates `physicalBetaA_neg` at `a = b = 0`, `a0 = 0`. -/
theorem physicalBetaA_neg_fixedMass (p : PhysicalParams) (d : ModeData) (betaRef : ℝ)
    (hp : p.FixedMassAdmissible) (hc : StrictCriticalMode p d betaRef) :
    physicalBetaA p d < 0 ∧
    ∀ beta : ℝ, fixedMassBetaCoefficient p d.eigenvalue beta =
      betaQuadratic (physicalBetaA p d) (physicalBetaB p d fixedMassA0)
        (physicalBetaC p d fixedMassA0) beta :=
  ⟨physicalBetaA_neg p d betaRef (fixedMass_positive_parameters p hp) hc,
    fun beta => fixedMassBetaCoefficient_physical_quadratic p d betaRef beta hp hc⟩

/-- **Example 3.1, coefficient by coefficient.** In the all-ones model
(`a = b = μ = ν = m = α = γ = 1`, so `u* = v* = 1`), for `λ > 1/2` the logistic cubic
coefficient `β_{n₀}` equals the displayed quotient
`[(224-96β)λ⁴ + (192-152β)λ³ + (8-104β-16β²)λ² + (96-28β-8β²)λ + 56 + 11β - β²] /
[96(1+λ)(4λ²-1)]`; its numerator is the `P(λ, β)` of Table 3.2 (not the `P` of (1.15)). -/
theorem example_3_1_display {x beta : ℝ} (hx : 1 / 2 < x) :
    logisticBetaCoefficient NormalizedSpecialization.allOnesParams x beta =
      ((224 - 96 * beta) * x ^ 4 + (192 - 152 * beta) * x ^ 3 +
          (8 - 104 * beta - 16 * beta ^ 2) * x ^ 2 + (96 - 28 * beta - 8 * beta ^ 2) * x +
          56 + 11 * beta - beta ^ 2) /
        (96 * (1 + x) * (4 * x ^ 2 - 1)) := by
  rw [NormalizedSpecialization.logisticBetaCoefficient_allOnes hx]
  rfl

end

end ChemotaxisBifurcation.CoefficientDictionary
