module
public import ChemotaxisBifurcation.PolynomialDegree

@[expose] public section

/-!
# The minimal-model rational form of `β_{n₀}` (Theorem 1.2(2), Eq. 1.15)

For the minimal model (`a = b = 0`, fixed mass), the 44-page manuscript states
`β_{n₀} = P(λ_{n₀}) / Q(λ_{n₀})` with `deg P ≤ 3` and
`Q(λ) = 24 (u*)² (μ+λ)² > 0` for `λ > 0`.

The general rational chain (`RationalCoefficient`, `PolynomialDegree`) already
covers the logistic case. With `a = 0` the logistic constant mode
`logisticA0 = -bA''/(2 a α)` is zero (and so is `bA''`), so the fixed-mass
coefficient is the same expression. With `d = a₀ = bA'' = 0` the cubic
numerator `n₄` vanishes at `0`; dividing by `X` leaves a cubic `m₃` and
`β_{n₀} = m₃(λ) / (48 K² (μ+λ)²)`. Writing `P = (u*)² m₃ / (2K²)` gives the
manuscript's normalization.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.MinimalRational

open Polynomial RationalCoefficient PolynomialDegree PolynomialDegree.RationalData

noncomputable section

/-- The cubic left after removing the factor `X` from `n₄`. -/
def m3Poly (r : RationalData) : ℝ[X] := n4Poly r /ₘ (X - C 0)

theorem n4_eval_zero (r : RationalData) (hd : r.d = 0) (ha0 : r.a0 = 0) (hb : r.bA2 = 0) :
    (n4Poly r).eval 0 = 0 := by
  rw [eval_n4Poly]
  simp [RationalData.n4, RationalData.n3, RationalData.n2, RationalData.delta,
    RationalData.s, hd, ha0, hb]

theorem X_mul_m3Poly (r : RationalData) (hd : r.d = 0) (ha0 : r.a0 = 0) (hb : r.bA2 = 0) :
    (X - C 0) * m3Poly r = n4Poly r :=
  mul_divByMonic_eq_iff_isRoot.mpr (IsRoot.def.mpr (n4_eval_zero r hd ha0 hb))

theorem natDegree_m3Poly_le (r : RationalData) : (m3Poly r).natDegree ≤ 3 := by
  have hmon : (X - C (0 : ℝ)).Monic := by simp [monic_X]
  rw [m3Poly, natDegree_divByMonic _ hmon]
  have h4 := natDegree_n4Poly_le r
  have h1 : (X - C (0 : ℝ)).natDegree = 1 := by simp
  omega

/-- On the minimal data the symbolic coefficient is `m₃(x) / (48 K² (μ+x)²)`. -/
theorem coefficient_eq_m3 (r : RationalData) {x : ℝ}
    (hd : r.d = 0) (ha0 : r.a0 = 0) (hb2 : r.bA2 = 0) (hb3 : r.bA3 = 0)
    (hx : x ≠ 0) (hK : r.K ≠ 0) (hp : r.p1 x ≠ 0) (hq : r.q x ≠ 0) :
    r.coefficient x = (m3Poly r).eval x / (48 * r.K ^ 2 * (r.mu + x) ^ 2) := by
  have hdelta : r.delta x ≠ 0 := by
    unfold RationalData.delta
    rw [hd]
    simpa using pow_ne_zero 2 hx
  rw [r.coefficient_eq_numerator_div_denominator hx hK hp hq hdelta]
  have hn4 : r.n4 x = x * (m3Poly r).eval x := by
    have := congrArg (eval x) (X_mul_m3Poly r hd ha0 hb2)
    rw [eval_mul, eval_n4Poly] at this
    simpa using this.symm
  have hp' : r.mu + x ≠ 0 := by simpa [RationalData.p1] using hp
  unfold RationalData.numerator RationalData.denominator RationalData.betaConstant
  rw [hn4]
  simp only [RationalData.s, RationalData.p1, hd, ha0, hb2, hb3]
  field_simp
  ring

/-- With `a = 0` the logistic and fixed-mass coefficients coincide. -/
theorem fixedMass_eq_logistic (p : PhysicalParams) (x beta : ℝ) (ha : p.a = 0) :
    fixedMassBetaCoefficient p x beta = logisticBetaCoefficient p x beta := by
  have h0 : logisticA0 p = fixedMassA0 := by
    simp [logisticA0, fixedMassA0, PhysicalParams.logisticSlope, ha]
  unfold fixedMassBetaCoefficient logisticBetaCoefficient fixedMassQuadraticJet
    logisticQuadraticJet
  rw [h0]

/-- The minimal-model numerator in the manuscript's normalization. -/
def minimalNumeratorPoly (p : PhysicalParams) (beta : ℝ) : ℝ[X] :=
  C (p.uStar ^ 2 / (2 * (mobilityScaledTaylor p 0).Cprime ^ 2)) *
    m3Poly (physicalRationalData p beta)

theorem natDegree_minimalNumeratorPoly_le (p : PhysicalParams) (beta : ℝ) :
    (minimalNumeratorPoly p beta).natDegree ≤ 3 :=
  (natDegree_C_mul_le _ _).trans (natDegree_m3Poly_le _)

/-- Theorem 1.2(2), minimal model: `β_{n₀} = P(λ)/(24 (u*)² (μ+λ)²)` with
`deg P ≤ 3`, and the denominator is positive, for every `λ > 0`. -/
theorem fixedMassBetaCoefficient_eq_cubic_ratio
    (p : PhysicalParams) (hp : p.FixedMassAdmissible) (x beta : ℝ) (hx : 0 < x) :
    fixedMassBetaCoefficient p x beta =
        (minimalNumeratorPoly p beta).eval x / (24 * p.uStar ^ 2 * (p.mu + x) ^ 2) ∧
      (minimalNumeratorPoly p beta).natDegree ≤ 3 ∧
      0 < 24 * p.uStar ^ 2 * (p.mu + x) ^ 2 := by
  obtain ⟨ha, hb, hm, hgamma, hnu, hmu, hu, hv, _⟩ := hp
  have hK : (mobilityScaledTaylor p 0).Cprime ≠ 0 := by
    simp only [mobilityScaledTaylor]
    positivity
  refine ⟨?_, natDegree_minimalNumeratorPoly_le p beta, by positivity⟩
  rw [fixedMass_eq_logistic p x beta ha,
    logisticBetaCoefficient_eq_symbolic p x beta hmu.ne' (by positivity) (by positivity)]
  rw [coefficient_eq_m3 (physicalRationalData p beta)
      (by simp [physicalRationalData, PhysicalParams.logisticSlope, ha])
      (by simp [physicalRationalData, logisticA0, PhysicalParams.logisticSlope, ha])
      (by simp [physicalRationalData, mobilityScaledTaylor, ha])
      (by simp [physicalRationalData, mobilityScaledTaylor, ha])
      hx.ne' (by simpa [physicalRationalData] using hK)
      (by simp only [physicalRationalData, RationalData.p1]; positivity)
      (by simp only [physicalRationalData, RationalData.q]; positivity)]
  simp only [minimalNumeratorPoly, eval_C_mul, physicalRationalData]
  field_simp
  ring

end

end ChemotaxisBifurcation.MinimalRational
