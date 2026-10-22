module
public import ChemotaxisBifurcation.PolynomialDegree
public import Mathlib.Analysis.Polynomial.Basic

@[expose] public section

/-!
# Small-domain constants for Paper III

This module formalizes the exact finite algebra in Equations 1.13--1.16 and
2.32--2.35 of the corrected 38-page manuscript.  It does not claim the
asymptotic expansion of the full cubic coefficient: that limit requires the
generic rational coefficient chain proved in the preceding modules.
-/

namespace ChemotaxisBifurcation.SmallDomain

open ChemotaxisBifurcation
open Polynomial
open Filter Topology
open ChemotaxisBifurcation.RationalCoefficient
open ChemotaxisBifurcation.PolynomialDegree.RationalData

noncomputable section

/-- The exponent combination `h = γ + m - 1`. -/
def h (p : PhysicalParams) : ℝ := p.gamma + p.m - 1

/-- The positive-gap expression `D = α + 2 - γ`. -/
def D (p : PhysicalParams) : ℝ := p.alpha + 2 - p.gamma

/-- The polynomial denoted by `𝖯` in Equation 1.13. -/
def scriptP (p : PhysicalParams) : ℝ :=
  h p * (6 * p.alpha - 4 * p.gamma - p.m + 13)

/-- The intermediate constant polynomial `𝖳₀` from Equation 2.33. -/
def scriptT0 (p : PhysicalParams) : ℝ :=
  -6 * p.alpha ^ 2 + 16 * p.alpha * p.gamma + 19 * p.alpha * p.m
    - 40 * p.alpha - 10 * p.gamma ^ 2 - 17 * p.gamma * p.m
    + 42 * p.gamma + 2 * p.m ^ 2 + 42 * p.m - 50

/-- The reduced critical polynomial `𝖳` from Equation 1.16. -/
def scriptT (p : PhysicalParams) : ℝ :=
  -6 * p.alpha ^ 2 + 4 * p.alpha * p.gamma + 7 * p.alpha * p.m
    - 28 * p.alpha - 2 * p.gamma ^ 2 - 7 * p.gamma * p.m
    + 8 * p.gamma + 4 * p.m ^ 2 + 14 * p.m - 24

/-- The reduced critical polynomial `M` from Equation 1.16. -/
def scriptM (p : PhysicalParams) : ℝ :=
  24 * p.alpha - 14 * p.gamma - 5 * p.m + 53

/-- `τ_β = β γ v* / (1 + v*)`. -/
def tauBeta (p : PhysicalParams) (beta : ℝ) : ℝ :=
  beta * p.gamma * p.vStar / p.signalOffset

/-- The leading small-domain coefficient `c_sd`: the coefficient `c` of Theorem 1.2(2), given
in arXiv:2610.20976v1 by (1.16) with the factored form (1.17) (p. 9). (The module header's
equation numbers are those of the corrected 38-page manuscript; in v1, (1.13) is `α_{n₀}`.) -/
def cSD (p : PhysicalParams) (beta : ℝ) : ℝ :=
  (scriptP p -
      6 * beta * p.gamma * D p * p.vStar / p.signalOffset) /
    (24 * p.uStar ^ 2)

/-- The critical signal-sensitivity exponent `β_sd` from Equation 1.14. -/
def betaSD (p : PhysicalParams) : ℝ :=
  scriptP p * p.signalOffset /
    (6 * p.gamma * D p * p.vStar)

/-- The constant term `d(β)` from Equation 2.33. -/
def dBeta (p : PhysicalParams) (beta : ℝ) : ℝ :=
  (p.logisticSlope * scriptT0 p - 2 * p.mu * h p ^ 2) /
      (48 * p.uStar ^ 2) -
    tauBeta p beta *
      (6 * p.logisticSlope * D p - 5 * p.mu * h p) /
      (24 * p.uStar ^ 2)

/-- The finite critical small-domain limit `d*` from Equation 1.16. -/
def dStar (p : PhysicalParams) : ℝ :=
  (3 * p.logisticSlope * D p * scriptT p +
      p.mu * h p ^ 2 * scriptM p) /
    (144 * p.uStar ^ 2 * D p)

/-- The threshold ratio `κ*` used in Equation 2.35. -/
def kappaStar (p : PhysicalParams) : ℝ :=
  h p ^ 2 * scriptM p /
    (3 * p.alpha * D p * |scriptT p|)

/-- First polynomial reduction used at the critical exponent. -/
theorem scriptT0_sub_two_scriptP (p : PhysicalParams) :
    scriptT0 p - 2 * scriptP p = scriptT p := by
  unfold scriptT0 scriptP scriptT h
  ring

/-- Second polynomial reduction used at the critical exponent. -/
theorem scriptM_identity (p : PhysicalParams) :
    5 * (6 * p.alpha - 4 * p.gamma - p.m + 13) - 6 * D p =
      scriptM p := by
  unfold D scriptM
  ring

/-- Equation 1.15: the leading coefficient factors at `β_sd`. -/
theorem cSD_eq_factored (p : PhysicalParams)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hgamma : p.gamma ≠ 0) (hD : D p ≠ 0) (hv : p.vStar ≠ 0)
    (beta : ℝ) :
    cSD p beta =
      p.gamma * D p * p.vStar /
        (4 * p.uStar ^ 2 * p.signalOffset) * (betaSD p - beta) := by
  unfold cSD betaSD
  field_simp [hu, hw, hgamma, hD, hv]
  ring

/-- At the critical exponent the leading small-domain coefficient vanishes. -/
theorem cSD_betaSD_eq_zero (p : PhysicalParams)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hgamma : p.gamma ≠ 0) (hD : D p ≠ 0) (hv : p.vStar ≠ 0) :
    cSD p (betaSD p) = 0 := by
  rw [cSD_eq_factored p hu hw hgamma hD hv]
  ring

/-- The exact critical constant reduction `d(β_sd) = d*`. -/
theorem dBeta_betaSD_eq_dStar (p : PhysicalParams)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hgamma : p.gamma ≠ 0) (hD : D p ≠ 0) (hv : p.vStar ≠ 0) :
    dBeta p (betaSD p) = dStar p := by
  unfold dBeta betaSD dStar tauBeta PhysicalParams.logisticSlope
  rw [show scriptT0 p = scriptT p + 2 * scriptP p by
    linarith [scriptT0_sub_two_scriptP p]]
  rw [show scriptM p =
      5 * (6 * p.alpha - 4 * p.gamma - p.m + 13) - 6 * D p by
    exact (scriptM_identity p).symm]
  unfold scriptP h
  field_simp [hu, hw, hgamma, hD, hv]
  ring

/-- Equation 2.35, before using positivity to read off the sign. -/
theorem dStar_eq_kappa_form (p : PhysicalParams)
    (hu : p.uStar ≠ 0) (halpha : p.alpha ≠ 0)
    (hD : D p ≠ 0) (hT : scriptT p < 0) :
    dStar p =
      p.alpha * |scriptT p| / (48 * p.uStar ^ 2) *
        (kappaStar p * p.mu - p.a) := by
  have hT0 : scriptT p ≠ 0 := ne_of_lt hT
  unfold dStar kappaStar PhysicalParams.logisticSlope
  rw [abs_of_neg hT]
  field_simp [hu, halpha, hD, hT0]
  ring

/-- The sign of `c_sd` below the critical exponent. -/
theorem cSD_pos_of_lt_betaSD (p : PhysicalParams)
    (hu : 0 < p.uStar) (hv : 0 < p.vStar)
    (hgamma : 0 < p.gamma) (hD : 0 < D p)
    {beta : ℝ} (hbeta : beta < betaSD p) :
    0 < cSD p beta := by
  have hw : 0 < p.signalOffset := by
    unfold PhysicalParams.signalOffset
    linarith
  rw [cSD_eq_factored p (ne_of_gt hu) (ne_of_gt hw)
    (ne_of_gt hgamma) (ne_of_gt hD) (ne_of_gt hv)]
  have hfactor :
      0 < p.gamma * D p * p.vStar /
        (4 * p.uStar ^ 2 * p.signalOffset) := by
    positivity
  exact mul_pos hfactor (sub_pos.mpr hbeta)

/-- The sign of `c_sd` above the critical exponent. -/
theorem cSD_neg_of_betaSD_lt (p : PhysicalParams)
    (hu : 0 < p.uStar) (hv : 0 < p.vStar)
    (hgamma : 0 < p.gamma) (hD : 0 < D p)
    {beta : ℝ} (hbeta : betaSD p < beta) :
    cSD p beta < 0 := by
  have hw : 0 < p.signalOffset := by
    unfold PhysicalParams.signalOffset
    linarith
  rw [cSD_eq_factored p (ne_of_gt hu) (ne_of_gt hw)
    (ne_of_gt hgamma) (ne_of_gt hD) (ne_of_gt hv)]
  have hfactor :
      0 < p.gamma * D p * p.vStar /
        (4 * p.uStar ^ 2 * p.signalOffset) := by
    positivity
  exact mul_neg_of_pos_of_neg hfactor (sub_neg.mpr hbeta)

/-- If the leading exponent polynomial is negative, then every nonnegative
sensitivity exponent gives a negative small-domain coefficient. -/
theorem cSD_neg_of_scriptP_neg (p : PhysicalParams)
    (hu : 0 < p.uStar) (hv : 0 < p.vStar)
    (hgamma : 0 < p.gamma) (hD : 0 < D p)
    (hP : scriptP p < 0) {beta : ℝ} (hbeta : 0 ≤ beta) :
    cSD p beta < 0 := by
  have hw : 0 < p.signalOffset := by
    unfold PhysicalParams.signalOffset
    linarith
  unfold cSD
  have hcorrection :
      0 ≤ 6 * beta * p.gamma * D p * p.vStar / p.signalOffset := by
    positivity
  have hden : 0 < 24 * p.uStar ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (by linarith) hden

/-- Constructed numerator polynomial for the physical coefficient. -/
noncomputable def physicalNumeratorPoly
    (p : PhysicalParams) (beta : ℝ) : ℝ[X] :=
  numeratorPoly (physicalRationalData p beta)

/-- Constructed denominator polynomial for the physical coefficient. -/
noncomputable def physicalDenominatorPoly
    (p : PhysicalParams) (beta : ℝ) : ℝ[X] :=
  denominatorPoly (physicalRationalData p beta)

/-- The affine part `c_sd X + d(β)` of the small-domain expansion. -/
noncomputable def smallDomainAffinePoly
    (p : PhysicalParams) (beta : ℝ) : ℝ[X] :=
  C (cSD p beta) * X + C (dBeta p beta)

/-- Exact polynomial remainder after subtracting the affine asymptote. -/
noncomputable def smallDomainRemainderPoly
    (p : PhysicalParams) (beta : ℝ) : ℝ[X] :=
  physicalNumeratorPoly p beta -
    smallDomainAffinePoly p beta * physicalDenominatorPoly p beta

theorem logisticA0_eq_explicit (p : PhysicalParams)
    (hu : p.uStar ≠ 0) (hd : p.logisticSlope ≠ 0) :
    logisticA0 p = -(1 + p.alpha) / (4 * p.uStar) := by
  have ha : p.a ≠ 0 := by
    intro ha
    apply hd
    simp [PhysicalParams.logisticSlope, ha]
  have halpha : p.alpha ≠ 0 := by
    intro halpha
    apply hd
    simp [PhysicalParams.logisticSlope, halpha]
  unfold logisticA0 mobilityScaledTaylor PhysicalParams.logisticSlope
  field_simp [hu, ha, halpha] <;> ring

theorem physical_numeratorCoeff5_eq
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0) :
    numeratorCoeff5 (physicalRationalData p beta) =
      48 * (physicalRationalData p beta).K ^ 2 * cSD p beta := by
  unfold numeratorCoeff5 RationalData.E physicalRationalData
  rw [logisticA0_eq_explicit p hu hd]
  simp only [mobilityScaledTaylor]
  unfold cSD scriptP h D
  unfold PhysicalParams.signalOffset
  field_simp [hu, hw, hmu, hd] <;> ring

theorem physical_numeratorCoeff4_eq
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0) :
    numeratorCoeff4 (physicalRationalData p beta) =
      48 * (physicalRationalData p beta).K ^ 2 * dBeta p beta +
        96 * (physicalRationalData p beta).K ^ 2 * p.mu * cSD p beta := by
  unfold numeratorCoeff4 RationalData.E physicalRationalData
  rw [logisticA0_eq_explicit p hu hd]
  simp only [mobilityScaledTaylor]
  unfold cSD dBeta tauBeta scriptP scriptT0 h D
  unfold PhysicalParams.signalOffset
  simp only [PhysicalParams.logisticSlope]
  field_simp [hu, hw, hmu, hd] <;> ring

theorem coeff_affine_mul_denominator_five
    (p : PhysicalParams) (beta : ℝ) :
    (smallDomainAffinePoly p beta * physicalDenominatorPoly p beta).coeff 5 =
      48 * (physicalRationalData p beta).K ^ 2 * cSD p beta := by
  unfold smallDomainAffinePoly physicalDenominatorPoly denominatorPoly pPoly
  compute_degree! <;> ring

theorem coeff_affine_mul_denominator_four
    (p : PhysicalParams) (beta : ℝ) :
    (smallDomainAffinePoly p beta * physicalDenominatorPoly p beta).coeff 4 =
      48 * (physicalRationalData p beta).K ^ 2 * dBeta p beta +
        96 * (physicalRationalData p beta).K ^ 2 * p.mu * cSD p beta := by
  unfold smallDomainAffinePoly
  rw [add_mul, coeff_add]
  rw [show C (cSD p beta) * X * physicalDenominatorPoly p beta =
      C (cSD p beta) * (X * physicalDenominatorPoly p beta) by ring]
  rw [coeff_C_mul, coeff_C_mul]
  have hx : (X * physicalDenominatorPoly p beta).coeff 4 =
      (physicalDenominatorPoly p beta).coeff 3 := by
    simpa using coeff_X_mul (physicalDenominatorPoly p beta) 3
  rw [hx]
  unfold physicalDenominatorPoly
  rw [coeff_denominatorPoly_three, coeff_denominatorPoly_four]
  simp only [physicalRationalData]
  ring

theorem coeff_smallDomainRemainderPoly_five
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0) :
    (smallDomainRemainderPoly p beta).coeff 5 = 0 := by
  unfold smallDomainRemainderPoly physicalNumeratorPoly
  rw [coeff_sub, coeff_numeratorPoly_five,
    physical_numeratorCoeff5_eq p beta hu hw hmu hd,
    coeff_affine_mul_denominator_five]
  ring

theorem coeff_smallDomainRemainderPoly_four
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0) :
    (smallDomainRemainderPoly p beta).coeff 4 = 0 := by
  unfold smallDomainRemainderPoly physicalNumeratorPoly
  rw [coeff_sub, coeff_numeratorPoly_four,
    physical_numeratorCoeff4_eq p beta hu hw hmu hd,
    coeff_affine_mul_denominator_four]
  ring

theorem natDegree_smallDomainRemainderPoly_le_three
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0) :
    (smallDomainRemainderPoly p beta).natDegree ≤ 3 := by
  have hP := natDegree_numeratorPoly_le (physicalRationalData p beta)
  have hQ := natDegree_denominatorPoly_le (physicalRationalData p beta)
  have hle5 : (smallDomainRemainderPoly p beta).natDegree ≤ 5 := by
    unfold smallDomainRemainderPoly physicalNumeratorPoly
    unfold smallDomainAffinePoly physicalDenominatorPoly
    compute_degree!
    omega
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hn5 : 5 < n
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle5 hn5)
  have hn_cases : n = 4 ∨ n = 5 := by omega
  rcases hn_cases with rfl | rfl
  · exact coeff_smallDomainRemainderPoly_four p beta hu hw hmu hd
  · exact coeff_smallDomainRemainderPoly_five p beta hu hw hmu hd

theorem natDegree_physicalDenominatorPoly_eq_four
    (p : PhysicalParams) (beta : ℝ)
    (hK : (physicalRationalData p beta).K ≠ 0) :
    (physicalDenominatorPoly p beta).natDegree = 4 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_denominatorPoly_le (physicalRationalData p beta))
  rw [coeff_denominatorPoly_four]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hK)

theorem smallDomainRemainder_degree_lt_denominator
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0)
    (hK : (physicalRationalData p beta).K ≠ 0) :
    (smallDomainRemainderPoly p beta).degree <
      (physicalDenominatorPoly p beta).degree := by
  apply degree_lt_degree
  rw [natDegree_physicalDenominatorPoly_eq_four p beta hK]
  have := natDegree_smallDomainRemainderPoly_le_three p beta hu hw hmu hd
  omega

theorem smallDomainRemainder_ratio_tendsto_zero
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0)
    (hK : (physicalRationalData p beta).K ≠ 0) :
    Tendsto
      (fun x => (smallDomainRemainderPoly p beta).eval x /
        (physicalDenominatorPoly p beta).eval x)
      atTop (𝓝 0) := by
  exact Polynomial.div_tendsto_atTop_zero_of_degree_lt _ _
    (smallDomainRemainder_degree_lt_denominator p beta hu hw hmu hd hK)

theorem rationalCoefficient_sub_linear_tendsto_dBeta
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0)
    (hK : (physicalRationalData p beta).K ≠ 0) :
    Tendsto
      (fun x => (physicalNumeratorPoly p beta).eval x /
          (physicalDenominatorPoly p beta).eval x - cSD p beta * x)
      atTop (𝓝 (dBeta p beta)) := by
  have hQ : physicalDenominatorPoly p beta ≠ 0 := by
    intro hzero
    have hdeg := natDegree_physicalDenominatorPoly_eq_four p beta hK
    rw [hzero, natDegree_zero] at hdeg
    norm_num at hdeg
  have hratio := smallDomainRemainder_ratio_tendsto_zero
    p beta hu hw hmu hd hK
  have hsum : Tendsto
      (fun x => dBeta p beta +
        (smallDomainRemainderPoly p beta).eval x /
          (physicalDenominatorPoly p beta).eval x)
      atTop (𝓝 (dBeta p beta)) := by
    simpa using tendsto_const_nhds.add hratio
  apply hsum.congr'
  filter_upwards [(physicalDenominatorPoly p beta).eventually_atTop_not_isRoot hQ]
    with x hx
  have hQx : (physicalDenominatorPoly p beta).eval x ≠ 0 := by
    simpa [Polynomial.IsRoot] using hx
  unfold smallDomainRemainderPoly smallDomainAffinePoly
  simp only [eval_sub, eval_mul, eval_add, eval_C_mul, eval_X, eval_C]
  field_simp [hQx]
  ring

theorem physicalDeltaPoly_ne_zero (p : PhysicalParams) (beta : ℝ) :
    deltaPoly (physicalRationalData p beta) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun f : ℝ[X] => f.coeff 2) hzero
  simp [deltaPoly] at hcoeff

/-- The actual physical cubic coefficient has the manuscript's small-domain
constant term after subtraction of its linear leading term. -/
theorem logisticBetaCoefficient_sub_linear_tendsto_dBeta
    (p : PhysicalParams) (beta : ℝ)
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0)
    (hK : (physicalRationalData p beta).K ≠ 0) :
    Tendsto
      (fun x => logisticBetaCoefficient p x beta - cSD p beta * x)
      atTop (𝓝 (dBeta p beta)) := by
  have hrational := rationalCoefficient_sub_linear_tendsto_dBeta
    p beta hu hw hmu hd hK
  have heq :
      (fun x => logisticBetaCoefficient p x beta - cSD p beta * x) =ᶠ[atTop]
        (fun x => (physicalNumeratorPoly p beta).eval x /
          (physicalDenominatorPoly p beta).eval x - cSD p beta * x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_gt_atTop (-p.mu), eventually_gt_atTop (-p.mu / 4),
      (deltaPoly (physicalRationalData p beta)).eventually_atTop_not_isRoot
        (physicalDeltaPoly_ne_zero p beta)] with x hx0 hxp hxq hdeltaRoot
    have hx : x ≠ 0 := ne_of_gt hx0
    have hp : p.mu + x ≠ 0 := by nlinarith
    have hq : p.mu + 4 * x ≠ 0 := by nlinarith
    have hdelta : p.logisticSlope * p.mu - 4 * x ^ 2 ≠ 0 := by
      intro hzero
      apply hdeltaRoot
      unfold Polynomial.IsRoot
      rw [eval_deltaPoly]
      simpa [physicalRationalData, RationalData.delta] using hzero
    have hphysicalK : (mobilityScaledTaylor p 0).Cprime ≠ 0 := by
      simpa [physicalRationalData] using hK
    have hcoeff := logisticBetaCoefficient_eq_numerator_div_denominator
      p x beta hx hphysicalK hmu hp hq hdelta
    calc
      logisticBetaCoefficient p x beta - cSD p beta * x =
          (physicalRationalData p beta).numerator x /
              (physicalRationalData p beta).denominator x -
            cSD p beta * x := congrArg (fun y => y - cSD p beta * x) hcoeff
      _ = (physicalNumeratorPoly p beta).eval x /
              (physicalDenominatorPoly p beta).eval x - cSD p beta * x := by
            unfold physicalNumeratorPoly physicalDenominatorPoly
            rw [eval_numeratorPoly, eval_denominatorPoly]
  exact hrational.congr' heq.symm

end

/-- Square completion used to control the sign of `𝖳`. -/
theorem scriptT_square_completion (p : PhysicalParams) :
    scriptT p =
      -2 * (p.gamma - (4 * p.alpha - 7 * p.m + 8) / 4) ^ 2 +
        81 / 8 * p.m ^ 2 - 4 * p.alpha ^ 2 - 20 * p.alpha - 16 := by
  unfold scriptT
  ring

/-- The parameter region used by Remark 2.1. -/
def CriticalExponentRegion (p : PhysicalParams) : Prop :=
  0 < p.alpha ∧ 0 < p.gamma ∧
    p.gamma ≤ (1 + p.alpha) / 2 ∧
    1 ≤ p.m ∧ p.m < (p.alpha + 2) / 2

theorem critical_region_D_pos (p : PhysicalParams)
    (hr : CriticalExponentRegion p) : 0 < D p := by
  rcases hr with ⟨halpha, hgamma0, hgamma, hm1, hm⟩
  unfold D
  linarith

theorem critical_region_h_pos (p : PhysicalParams)
    (hr : CriticalExponentRegion p) : 0 < h p := by
  rcases hr with ⟨halpha, hgamma0, hgamma, hm1, hm⟩
  unfold h
  linarith

theorem critical_region_factor_pos (p : PhysicalParams)
    (hr : CriticalExponentRegion p) :
    0 < 6 * p.alpha - 4 * p.gamma - p.m + 13 := by
  rcases hr with ⟨halpha, hgamma0, hgamma, hm1, hm⟩
  linarith

theorem critical_region_scriptP_pos (p : PhysicalParams)
    (hr : CriticalExponentRegion p) : 0 < scriptP p := by
  unfold scriptP
  exact mul_pos (critical_region_h_pos p hr)
    (critical_region_factor_pos p hr)

theorem critical_region_scriptM_pos (p : PhysicalParams)
    (hr : CriticalExponentRegion p) : 0 < scriptM p := by
  rcases hr with ⟨halpha, hgamma0, hgamma, hm1, hm⟩
  unfold scriptM
  linarith

theorem critical_region_scriptT_neg (p : PhysicalParams)
    (hr : CriticalExponentRegion p) : scriptT p < 0 := by
  rcases hr with ⟨halpha, hgamma0, hgamma, hm1, hm⟩
  rw [scriptT_square_completion]
  have hsquare :
      0 ≤ (p.gamma - (4 * p.alpha - 7 * p.m + 8) / 4) ^ 2 := sq_nonneg _
  have hm0 : 0 ≤ p.m := by linarith
  have hmbound : 4 * p.m ^ 2 < (p.alpha + 2) ^ 2 := by
    nlinarith [sq_nonneg (p.alpha + 2 - 2 * p.m)]
  nlinarith [sq_nonneg p.alpha]

theorem critical_region_kappaStar_pos (p : PhysicalParams)
    (hu : 0 < p.uStar) (hr : CriticalExponentRegion p) :
    0 < kappaStar p := by
  have halpha : 0 < p.alpha := hr.1
  have hD : 0 < D p := critical_region_D_pos p hr
  have hh : 0 < h p := critical_region_h_pos p hr
  have hM : 0 < scriptM p := critical_region_scriptM_pos p hr
  have hT : scriptT p < 0 := critical_region_scriptT_neg p hr
  unfold kappaStar
  exact div_pos (mul_pos (sq_pos_of_pos hh) hM)
    (mul_pos (mul_pos (mul_pos (by norm_num) halpha) hD)
      (abs_pos.mpr hT.ne))

theorem dStar_pos_iff (p : PhysicalParams)
    (hu : 0 < p.uStar) (hr : CriticalExponentRegion p) :
    0 < dStar p ↔ p.a < kappaStar p * p.mu := by
  have halpha : 0 < p.alpha := hr.1
  have hD : 0 < D p := critical_region_D_pos p hr
  have hT : scriptT p < 0 := critical_region_scriptT_neg p hr
  rw [dStar_eq_kappa_form p (ne_of_gt hu) (ne_of_gt halpha)
    (ne_of_gt hD) hT]
  have hfactor : 0 < p.alpha * |scriptT p| / (48 * p.uStar ^ 2) := by
    exact div_pos (mul_pos halpha (abs_pos.mpr hT.ne))
      (mul_pos (by norm_num) (sq_pos_of_pos hu))
  constructor
  · intro hpos
    have : 0 < kappaStar p * p.mu - p.a :=
      pos_of_mul_pos_left (by simpa [mul_comm] using hpos) (le_of_lt hfactor)
    linarith
  · intro hlt
    exact mul_pos hfactor (sub_pos.mpr hlt)

theorem dStar_eq_zero_iff (p : PhysicalParams)
    (hu : 0 < p.uStar) (hr : CriticalExponentRegion p) :
    dStar p = 0 ↔ p.a = kappaStar p * p.mu := by
  have halpha : 0 < p.alpha := hr.1
  have hD : 0 < D p := critical_region_D_pos p hr
  have hT : scriptT p < 0 := critical_region_scriptT_neg p hr
  rw [dStar_eq_kappa_form p (ne_of_gt hu) (ne_of_gt halpha)
    (ne_of_gt hD) hT]
  have hfactor : p.alpha * |scriptT p| / (48 * p.uStar ^ 2) ≠ 0 := by
    exact ne_of_gt <| div_pos (mul_pos halpha (abs_pos.mpr hT.ne))
      (mul_pos (by norm_num) (sq_pos_of_pos hu))
  rw [mul_eq_zero]
  simp only [hfactor, false_or]
  constructor <;> intro h <;> linarith

theorem dStar_neg_iff (p : PhysicalParams)
    (hu : 0 < p.uStar) (hr : CriticalExponentRegion p) :
    dStar p < 0 ↔ kappaStar p * p.mu < p.a := by
  have halpha : 0 < p.alpha := hr.1
  have hD : 0 < D p := critical_region_D_pos p hr
  have hT : scriptT p < 0 := critical_region_scriptT_neg p hr
  rw [dStar_eq_kappa_form p (ne_of_gt hu) (ne_of_gt halpha)
    (ne_of_gt hD) hT]
  have hfactor : 0 < p.alpha * |scriptT p| / (48 * p.uStar ^ 2) := by
    exact div_pos (mul_pos halpha (abs_pos.mpr hT.ne))
      (mul_pos (by norm_num) (sq_pos_of_pos hu))
  constructor
  · intro hneg
    have : kappaStar p * p.mu - p.a < 0 :=
      neg_of_mul_neg_left (by simpa [mul_comm] using hneg) (le_of_lt hfactor)
    linarith
  · intro hlt
    exact mul_neg_of_pos_of_neg hfactor (sub_neg.mpr hlt)

end ChemotaxisBifurcation.SmallDomain
