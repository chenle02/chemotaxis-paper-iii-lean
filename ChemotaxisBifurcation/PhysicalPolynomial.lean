module
public import ChemotaxisBifurcation.PhysicalModeGuards
public import ChemotaxisBifurcation.PolynomialDegree
public import ChemotaxisBifurcation.Taylor

@[expose] public section

/-!
# Literal physical polynomial lift

The field-algebra layer divides out the common mobility factor `B₀`, so its
symbolic `K` is `C'`.  The manuscript writes `K = B₀ C'`.  This module restores
the literal paper numerator and denominator by multiplying both checked
polynomials by `B₀²`.
-/

namespace ChemotaxisBifurcation.PhysicalPolynomial

open Polynomial
open ChemotaxisBifurcation
open ChemotaxisBifurcation.RationalCoefficient
open ChemotaxisBifurcation.PolynomialDegree.RationalData

noncomputable section

/-- The literal paper numerator, with the common `B₀²` factor restored. -/
def paperNumeratorPoly (p : PhysicalParams) (beta : ℝ) : ℝ[X] :=
  C (p.mobilityB0 beta ^ 2) * numeratorPoly (physicalRationalData p beta)

/-- The literal paper denominator, with the common `B₀²` factor restored. -/
def paperDenominatorPoly (p : PhysicalParams) (beta : ℝ) : ℝ[X] :=
  C (p.mobilityB0 beta ^ 2) * denominatorPoly (physicalRationalData p beta)

/-- The balanced quartic numerator after the manuscript's `x+μ` cancellation. -/
def paperBalancedNumeratorPoly (p : PhysicalParams) (beta : ℝ) : ℝ[X] :=
  C (p.mobilityB0 beta ^ 2) *
    balancedNumeratorPoly (physicalRationalData p beta)

/-- The balanced cubic denominator after the manuscript's `x+μ` cancellation. -/
def paperBalancedDenominatorPoly (p : PhysicalParams) (beta : ℝ) : ℝ[X] :=
  C (p.mobilityB0 beta ^ 2) *
    balancedDenominatorPoly (physicalRationalData p beta)

/-- The scaled `C'` agrees with the physical signal derivative under the
signal equilibrium relation. -/
theorem scaledCprime_eq_physical (p : PhysicalParams)
    (hu : 0 < p.uStar) (hsig : p.SignalEquilibrium) :
    (mobilityScaledTaylor p 0).Cprime = p.signalC1Physical := by
  have h := Cprime_eq_scaled p hu hsig
  exact h.symm

/-- The lifted denominator is exactly the denominator printed in Equation
1.12, with the paper's `K = B₀C'`. -/
theorem paperDenominatorPoly_eval (p : PhysicalParams) (x beta : ℝ)
    (hu : 0 < p.uStar) (hsig : p.SignalEquilibrium) :
    (paperDenominatorPoly p beta).eval x =
      12 * p.thresholdK beta ^ 2 * (p.mu + x) ^ 2 *
        (4 * x ^ 2 - p.logisticSlope * p.mu) := by
  unfold paperDenominatorPoly
  rw [eval_C_mul, eval_denominatorPoly]
  have hC := scaledCprime_eq_physical p hu hsig
  simp only [physicalRationalData]
  unfold RationalData.denominator RationalData.p1
  unfold PhysicalParams.thresholdK
  rw [hC]
  ring

/-- Restoring the common physical factor does not change the rational
coefficient. -/
theorem paperRatio_eq_scaledRatio (p : PhysicalParams) (x beta : ℝ)
    (hB0 : p.mobilityB0 beta ≠ 0)
    (hQ : (denominatorPoly (physicalRationalData p beta)).eval x ≠ 0) :
    (paperNumeratorPoly p beta).eval x /
        (paperDenominatorPoly p beta).eval x =
      (numeratorPoly (physicalRationalData p beta)).eval x /
        (denominatorPoly (physicalRationalData p beta)).eval x := by
  unfold paperNumeratorPoly paperDenominatorPoly
  simp only [eval_C_mul]
  field_simp [hB0, hQ]

/-- The assembled physical coefficient is exactly the literal manuscript
ratio on the admissible non-minimal eigenvalue range. -/
theorem logisticBetaCoefficient_eq_paperRatio
    (p : PhysicalParams) (x beta : ℝ)
    (hp : p.LogisticAdmissible)
    (hxRange : Real.sqrt (p.logisticSlope * p.mu) / 2 < x) :
    logisticBetaCoefficient p x beta =
      (paperNumeratorPoly p beta).eval x /
        (paperDenominatorPoly p beta).eval x := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hmode := PhysicalModeGuards.logistic_positive_parameters p
    ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hd : 0 < p.logisticSlope := mul_pos ha halpha
  have hdmu : 0 ≤ p.logisticSlope * p.mu := mul_nonneg hd.le hmu.le
  have hsqrt : 0 ≤ Real.sqrt (p.logisticSlope * p.mu) := Real.sqrt_nonneg _
  have hsqrt_sq := Real.sq_sqrt hdmu
  have hx : 0 < x := by linarith
  have hK : (mobilityScaledTaylor p 0).Cprime ≠ 0 :=
    (PhysicalModeGuards.scaledCprime_pos p hmode).ne'
  have hp1 : p.mu + x ≠ 0 := by positivity
  have hq : p.mu + 4 * x ≠ 0 := by positivity
  have hdelta : p.logisticSlope * p.mu - 4 * x ^ 2 ≠ 0 := by
    have : p.logisticSlope * p.mu - 4 * x ^ 2 < 0 := by nlinarith
    exact this.ne
  have hB0 : p.mobilityB0 beta ≠ 0 := by
    unfold PhysicalParams.mobilityB0
    exact (div_pos (Real.rpow_pos_of_pos hu _)
      (Real.rpow_pos_of_pos (PhysicalModeGuards.signalOffset_pos p hmode) _)).ne'
  have hscaledQ :
      (denominatorPoly (physicalRationalData p beta)).eval x ≠ 0 := by
    rw [eval_denominatorPoly]
    exact ne_of_gt <| RationalData.denominator_pos
      (physicalRationalData p beta) hK
      (by simpa [physicalRationalData, RationalData.p1] using hp1)
      hdmu (by simpa [physicalRationalData] using hxRange)
  rw [logisticBetaCoefficient_eq_numerator_div_denominator
    p x beta hx.ne' hK hmu.ne' hp1 hq hdelta]
  rw [← eval_numeratorPoly, ← eval_denominatorPoly]
  exact (paperRatio_eq_scaledRatio p x beta hB0 hscaledQ).symm

/-- The literal manuscript denominator is positive on the admissible
eigenvalue range. -/
theorem paperDenominatorPoly_eval_pos
    (p : PhysicalParams) (x beta : ℝ)
    (hp : p.LogisticAdmissible)
    (hxRange : Real.sqrt (p.logisticSlope * p.mu) / 2 < x) :
    0 < (paperDenominatorPoly p beta).eval x := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hmode := PhysicalModeGuards.logistic_positive_parameters p
    ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hd : 0 < p.logisticSlope := mul_pos ha halpha
  have hdmu : 0 ≤ p.logisticSlope * p.mu := mul_nonneg hd.le hmu.le
  have hsqrt : 0 ≤ Real.sqrt (p.logisticSlope * p.mu) := Real.sqrt_nonneg _
  have hsqrt_sq := Real.sq_sqrt hdmu
  have hx : 0 < x := by nlinarith
  have htwox : Real.sqrt (p.logisticSlope * p.mu) < 2 * x := by linarith
  have hsq : (Real.sqrt (p.logisticSlope * p.mu)) ^ 2 < (2 * x) ^ 2 :=
    (sq_lt_sq₀ hsqrt (by positivity)).mpr htwox
  have hgap : 0 < 4 * x ^ 2 - p.logisticSlope * p.mu := by nlinarith
  rw [paperDenominatorPoly_eval p x beta hu heq.2]
  have hthreshold := PhysicalModeGuards.thresholdK_pos p beta hmode
  positivity

theorem natDegree_paperNumeratorPoly_le (p : PhysicalParams) (beta : ℝ) :
    (paperNumeratorPoly p beta).natDegree ≤ 5 := by
  unfold paperNumeratorPoly
  exact (natDegree_C_mul_le _ _).trans
    (natDegree_numeratorPoly_le (physicalRationalData p beta))

theorem natDegree_paperDenominatorPoly_le (p : PhysicalParams) (beta : ℝ) :
    (paperDenominatorPoly p beta).natDegree ≤ 4 := by
  unfold paperDenominatorPoly
  exact (natDegree_C_mul_le _ _).trans
    (natDegree_denominatorPoly_le (physicalRationalData p beta))

/-- Under positive physical data the literal generic denominator has exact
degree four. -/
theorem natDegree_paperDenominatorPoly_eq_four
    (p : PhysicalParams) (beta : ℝ) (hp : p.LogisticAdmissible) :
    (paperDenominatorPoly p beta).natDegree = 4 := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hmode := PhysicalModeGuards.logistic_positive_parameters p
    ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hB0 : p.mobilityB0 beta ≠ 0 := by
    unfold PhysicalParams.mobilityB0
    exact (div_pos (Real.rpow_pos_of_pos hu _)
      (Real.rpow_pos_of_pos (PhysicalModeGuards.signalOffset_pos p hmode) _)).ne'
  have hK : (physicalRationalData p beta).K ≠ 0 := by
    exact (PhysicalModeGuards.scaledCprime_pos p hmode).ne'
  apply natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_paperDenominatorPoly_le p beta)
  unfold paperDenominatorPoly
  rw [coeff_C_mul, coeff_denominatorPoly_four]
  exact mul_ne_zero (pow_ne_zero 2 hB0)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hK))

theorem natDegree_paperBalancedNumeratorPoly_le
    (p : PhysicalParams) (beta : ℝ) :
    (paperBalancedNumeratorPoly p beta).natDegree ≤ 4 := by
  unfold paperBalancedNumeratorPoly
  exact (natDegree_C_mul_le _ _).trans
    (natDegree_balancedNumeratorPoly_le (physicalRationalData p beta))

theorem natDegree_paperBalancedDenominatorPoly_le
    (p : PhysicalParams) (beta : ℝ) :
    (paperBalancedDenominatorPoly p beta).natDegree ≤ 3 := by
  unfold paperBalancedDenominatorPoly
  exact (natDegree_C_mul_le _ _).trans
    (natDegree_balancedDenominatorPoly_le (physicalRationalData p beta))

/-- Under positive physical data the balanced literal denominator has exact
degree three. -/
theorem natDegree_paperBalancedDenominatorPoly_eq_three
    (p : PhysicalParams) (beta : ℝ) (hp : p.LogisticAdmissible) :
    (paperBalancedDenominatorPoly p beta).natDegree = 3 := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hmode := PhysicalModeGuards.logistic_positive_parameters p
    ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hB0 : p.mobilityB0 beta ≠ 0 := by
    unfold PhysicalParams.mobilityB0
    exact (div_pos (Real.rpow_pos_of_pos hu _)
      (Real.rpow_pos_of_pos (PhysicalModeGuards.signalOffset_pos p hmode) _)).ne'
  have hK : (physicalRationalData p beta).K ≠ 0 := by
    exact (PhysicalModeGuards.scaledCprime_pos p hmode).ne'
  unfold paperBalancedDenominatorPoly balancedDenominatorPoly pPoly
  compute_degree! <;> positivity

/-- Mathlib's root multiset for the literal generic numerator has cardinality
at most five.  For a nonzero numerator this counts its algebraic real roots
with multiplicity.  This statement does not identify the root multiset of the
zero polynomial with its full set of real zeros; paper-facing zero-set bounds
therefore retain the manuscript's `P ≠ 0` hypothesis. -/
theorem card_roots_paperNumeratorPoly_le_five
    (p : PhysicalParams) (beta : ℝ) :
    (paperNumeratorPoly p beta).roots.card ≤ 5 :=
  (Polynomial.card_roots' _).trans (natDegree_paperNumeratorPoly_le p beta)

/-- The corresponding Mathlib root-multiset bound after balanced cancellation.
Any paper-facing real-zero-set consequence separately assumes that the
balanced numerator is nonzero. -/
theorem card_roots_paperBalancedNumeratorPoly_le_four
    (p : PhysicalParams) (beta : ℝ) :
    (paperBalancedNumeratorPoly p beta).roots.card ≤ 4 :=
  (Polynomial.card_roots' _).trans
    (natDegree_paperBalancedNumeratorPoly_le p beta)

/-- In the balanced case the lifted physical polynomials retain the checked
`x+μ` factorization. -/
theorem paperPolynomials_balanced_factor
    (p : PhysicalParams) (beta : ℝ)
    (hbalanced : p.logisticSlope = p.mu) :
    paperNumeratorPoly p beta =
        pPoly (physicalRationalData p beta) * paperBalancedNumeratorPoly p beta ∧
      paperDenominatorPoly p beta =
        pPoly (physicalRationalData p beta) * paperBalancedDenominatorPoly p beta := by
  constructor
  · unfold paperNumeratorPoly paperBalancedNumeratorPoly
    rw [numeratorPoly_eq_pPoly_mul_balanced _ hbalanced]
    ring
  · unfold paperDenominatorPoly paperBalancedDenominatorPoly
    rw [denominatorPoly_eq_pPoly_mul_balanced _ hbalanced]
    ring

end

end ChemotaxisBifurcation.PhysicalPolynomial
