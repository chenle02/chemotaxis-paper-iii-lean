module
public import ChemotaxisBifurcation.CoefficientLimits
public import ChemotaxisBifurcation.PhysicalPolynomial

@[expose] public section

/-!
# The explicit inverse-eigenvalue remainder rate

The degree gap gives the manuscript's O(1/λ) error, strengthening the already
checked vanishing remainder. No analytic center-manifold estimate is asserted.
-/
namespace ChemotaxisBifurcation.SmallDomain

open Polynomial Filter Asymptotics
open scoped Topology
open RationalCoefficient PolynomialDegree.RationalData

noncomputable section

/-- Reuse polynomial asymptotic comparison after multiplication by X. -/
theorem polynomial_ratio_isBigO_inv (P Q : ℝ[X]) (hQ : Q ≠ 0)
    (hdeg : (X * P).degree ≤ Q.degree) :
    (fun x : ℝ => P.eval x / Q.eval x) =O[atTop] (fun x => 1 / x) := by
  have hb := Polynomial.isBigO_atTop_of_degree_le (X * P) Q hdeg
  have hm := hb.mul (isBigO_refl (fun x : ℝ => 1 / (x * Q.eval x)) atTop)
  apply hm.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [eval_mul, eval_X]
    field_simp [hx.ne']
  · filter_upwards [Q.eventually_atTop_not_isRoot hQ] with x hx
    have hqx : Q.eval x ≠ 0 := hx
    field_simp [hqx]

theorem smallDomainRemainder_ratio_isBigO_inv
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0)
    (hK : (physicalRationalData p beta).K ≠ 0) :
    (fun x => (smallDomainRemainderPoly p beta).eval x /
      (physicalDenominatorPoly p beta).eval x) =O[atTop] (fun x : ℝ => 1 / x) := by
  have hQdeg := natDegree_physicalDenominatorPoly_eq_four p beta hK
  have hQ : physicalDenominatorPoly p beta ≠ 0 := by
    intro hz
    simp [hz] at hQdeg
  apply polynomial_ratio_isBigO_inv _ _ hQ
  have hR := natDegree_smallDomainRemainderPoly_le_three p beta hu hw hmu hd
  have hX : (X * smallDomainRemainderPoly p beta).natDegree ≤ 4 := by
    calc
      _ ≤ X.natDegree + (smallDomainRemainderPoly p beta).natDegree := natDegree_mul_le
      _ ≤ 4 := by simp only [natDegree_X]; omega
  calc
    _ ≤ ((X * smallDomainRemainderPoly p beta).natDegree : WithBot ℕ) :=
      degree_le_natDegree
    _ ≤ (4 : WithBot ℕ) := by exact_mod_cast hX
    _ = (physicalDenominatorPoly p beta).degree := by
      rw [degree_eq_natDegree hQ, hQdeg]
      norm_num

theorem rationalCoefficient_affine_error_isBigO_inv
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0)
    (hK : (physicalRationalData p beta).K ≠ 0) :
    (fun x => (physicalNumeratorPoly p beta).eval x /
      (physicalDenominatorPoly p beta).eval x - cSD p beta * x - dBeta p beta)
      =O[atTop] (fun x : ℝ => 1 / x) := by
  have hQ : physicalDenominatorPoly p beta ≠ 0 := by
    intro hz
    have hdeg := natDegree_physicalDenominatorPoly_eq_four p beta hK
    simp [hz] at hdeg
  apply (smallDomainRemainder_ratio_isBigO_inv p beta hu hw hmu hd hK).congr'
  · filter_upwards [(physicalDenominatorPoly p beta).eventually_atTop_not_isRoot hQ]
      with x hx
    have hQx : (physicalDenominatorPoly p beta).eval x ≠ 0 := hx
    unfold smallDomainRemainderPoly smallDomainAffinePoly
    simp only [eval_sub, eval_mul, eval_add, eval_C_mul, eval_X, eval_C]
    field_simp [hQx]
    ring
  · exact Filter.EventuallyEq.rfl

/-- The actual assembled coefficient has the displayed O(1/λ) error. -/
theorem logisticCoefficient_affine_error_isBigO_inv
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0)
    (hK : (physicalRationalData p beta).K ≠ 0) :
    (fun x => logisticBetaCoefficient p x beta - cSD p beta * x - dBeta p beta)
      =O[atTop] (fun x : ℝ => 1 / x) := by
  apply (rationalCoefficient_affine_error_isBigO_inv p beta hu hw hmu hd hK).congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_gt_atTop (-p.mu), eventually_gt_atTop (-p.mu / 4),
      (deltaPoly (physicalRationalData p beta)).eventually_atTop_not_isRoot
        (physicalDeltaPoly_ne_zero p beta)] with x hx0 hxp hxq hdeltaRoot
    have hx : x ≠ 0 := ne_of_gt hx0
    have hp1 : p.mu + x ≠ 0 := by nlinarith
    have hq : p.mu + 4 * x ≠ 0 := by nlinarith
    have hdelta : p.logisticSlope * p.mu - 4 * x ^ 2 ≠ 0 := by
      intro hzero
      apply hdeltaRoot
      unfold Polynomial.IsRoot
      rw [eval_deltaPoly]
      simpa [physicalRationalData, RationalData.delta] using hzero
    have hphysicalK : (mobilityScaledTaylor p 0).Cprime ≠ 0 := by
      simpa [physicalRationalData] using hK
    rw [logisticBetaCoefficient_eq_numerator_div_denominator
      p x beta hx hphysicalK hmu hp1 hq hdelta]
    unfold physicalNumeratorPoly physicalDenominatorPoly
    rw [eval_numeratorPoly, eval_denominatorPoly]
  · exact Filter.EventuallyEq.rfl

/-- Along the actual admissible small-domain path the error is O(L²). -/
theorem physical_small_domain_error_isBigO_length_sq
    (p : PhysicalParams) (beta : ℝ) {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hp : p.LogisticAdmissible)
    (hL : Tendsto (fun i => (d i).L) l (𝓝[>] (0 : ℝ)))
    (hs : ∀ᶠ i in l, PhysicalModeGuards.StrictCriticalMode p (d i) beta) :
    (fun i => logisticBetaCoefficient p (d i).eigenvalue beta -
      cSD p beta * (d i).eigenvalue - dBeta p beta)
      =O[l] (fun i => (d i).L ^ 2) := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hp' : p.LogisticAdmissible :=
    ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hmode := PhysicalModeGuards.logistic_positive_parameters p hp'
  have hw := PhysicalModeGuards.signalOffset_pos p hmode
  have hK : (physicalRationalData p beta).K ≠ 0 :=
    (PhysicalModeGuards.scaledCprime_pos p hmode).ne'
  have hrate := logisticCoefficient_affine_error_isBigO_inv p beta
    hu.ne' hw.ne' hmu.ne' (mul_pos ha halpha).ne' hK
  have hr := CoefficientLimits.balancingEigenvalue_pos p hp'
  have hrsq := CoefficientLimits.balancingEigenvalue_sq p hp'
  have hone := ModeIntervals.eventually_first_critical_mode p d beta
    (CoefficientLimits.balancingEigenvalue p) hmode hr hrsq hL hs
  have hfirst := DomainLimits.firstMode_tendsto_atTop_small_domain.comp hL
  have heigen : Tendsto (fun i => (d i).eigenvalue) l atTop := by
    apply hfirst.congr'
    filter_upwards [hone] with i hi
    simp only [ModeData.eigenvalue, Semidiscrete.continuumLam, Function.comp_def]
    rw [hi]
    norm_num
  apply (hrate.comp_tendsto heigen).trans
  apply (isBigO_const_mul_self (1 / Real.pi ^ 2) (fun i => (d i).L ^ 2) l).congr'
  · filter_upwards [hone, hs] with i hi hsi
    have hLi : (d i).L ≠ 0 := hsi.1.ne'
    simp only [ModeData.eigenvalue, Semidiscrete.continuumLam, Function.comp_def]
    rw [hi]
    norm_num
    field_simp [hLi, Real.pi_ne_zero]
    <;> ring
  · exact Filter.EventuallyEq.rfl

end
end ChemotaxisBifurcation.SmallDomain
