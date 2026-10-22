module
public import ChemotaxisBifurcation.DomainLimits
public import ChemotaxisBifurcation.ModeLengths
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# Coefficient continuity at the balancing eigenvalue

This module consumes the all-parameter P/Q identity.  The strict-mode module
supplies the eigenvalue convergence; the current theorems require only the
physical non-minimal assumptions and a path converging to the balancing value.
-/

namespace ChemotaxisBifurcation.CoefficientLimits

open Filter Topology Polynomial
open ChemotaxisBifurcation
open ChemotaxisBifurcation.RationalCoefficient
open ChemotaxisBifurcation.PolynomialDegree.RationalData
open ChemotaxisBifurcation.SmallDomain

noncomputable section

/-- The eigenvalue balancing the two terms in the modal threshold. -/
def balancingEigenvalue (p : PhysicalParams) : ℝ :=
  Real.sqrt (p.logisticSlope * p.mu)

theorem balancingEigenvalue_pos (p : PhysicalParams)
    (hp : p.LogisticAdmissible) : 0 < balancingEigenvalue p := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  unfold balancingEigenvalue
  exact Real.sqrt_pos.2 (mul_pos (mul_pos ha halpha) hmu)

theorem balancingEigenvalue_sq (p : PhysicalParams)
    (hp : p.LogisticAdmissible) :
    balancingEigenvalue p ^ 2 = p.logisticSlope * p.mu := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  unfold balancingEigenvalue
  exact Real.sq_sqrt (mul_nonneg (mul_nonneg ha.le halpha.le) hmu.le)

/-- The physical denominator is nonzero at the balancing eigenvalue. -/
theorem denominator_ne_zero_at_balancing (p : PhysicalParams) (beta : ℝ)
    (hp : p.LogisticAdmissible) :
    (physicalDenominatorPoly p beta).eval (balancingEigenvalue p) ≠ 0 := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hd : 0 < p.logisticSlope := by
    exact mul_pos ha halpha
  have hr : 0 < balancingEigenvalue p :=
    balancingEigenvalue_pos p
      ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hK : (physicalRationalData p beta).K ≠ 0 := by
    unfold physicalRationalData mobilityScaledTaylor
    positivity
  have hp1 : (physicalRationalData p beta).p1 (balancingEigenvalue p) ≠ 0 := by
    unfold physicalRationalData RationalData.p1
    positivity
  have hpos := RationalData.denominator_pos (physicalRationalData p beta)
    hK hp1 (mul_nonneg hd.le hmu.le) (by
      rw [show Real.sqrt ((physicalRationalData p beta).d *
          (physicalRationalData p beta).mu) = balancingEigenvalue p by rfl]
      linarith)
  unfold physicalDenominatorPoly
  rw [eval_denominatorPoly]
  exact ne_of_gt hpos

/-- Along any path converging to the balancing eigenvalue, the assembled
physical cubic coefficient converges to its value there. -/
theorem logisticBetaCoefficient_tendsto_balancing
    (p : PhysicalParams) (beta : ℝ)
    {ι : Type*} {l : Filter ι} {lambda : ι → ℝ}
    (hp : p.LogisticAdmissible)
    (hlambda : Tendsto lambda l (𝓝 (balancingEigenvalue p))) :
    Tendsto (fun i => logisticBetaCoefficient p (lambda i) beta) l
      (𝓝 (logisticBetaCoefficient p (balancingEigenvalue p) beta)) := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  let r := balancingEigenvalue p
  let data := physicalRationalData p beta
  let P := numeratorPoly data
  let Q := denominatorPoly data
  have hr : 0 < r := balancingEigenvalue_pos p
    ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hrsq : r ^ 2 = p.logisticSlope * p.mu := balancingEigenvalue_sq p
    ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hK : (mobilityScaledTaylor p 0).Cprime ≠ 0 := by
    unfold mobilityScaledTaylor
    positivity
  have hQr : Q.eval r ≠ 0 := by
    dsimp [Q, r]
    exact denominator_ne_zero_at_balancing p beta
      ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hrat : Tendsto (fun x => P.eval x / Q.eval x) (𝓝 r)
      (𝓝 (P.eval r / Q.eval r)) :=
    P.continuousAt.div Q.continuousAt hQr
  have hnearX : ∀ᶠ x in 𝓝 r, x ≠ 0 := eventually_ne_nhds (ne_of_gt hr)
  have hnearP : ∀ᶠ x in 𝓝 r, p.mu + x ≠ 0 := by
    have : r ≠ -p.mu := by nlinarith
    filter_upwards [eventually_ne_nhds this] with x hx
    intro hzero
    apply hx
    linarith
  have hnearQ : ∀ᶠ x in 𝓝 r, p.mu + 4 * x ≠ 0 := by
    have : r ≠ -p.mu / 4 := by nlinarith
    filter_upwards [eventually_ne_nhds this] with x hx
    intro hzero
    apply hx
    linarith
  have hnearDelta : ∀ᶠ x in 𝓝 r,
      p.logisticSlope * p.mu - 4 * x ^ 2 ≠ 0 := by
    have hplus : r ≠ r / 2 := by linarith
    have hminus : r ≠ -r / 2 := by linarith
    filter_upwards [eventually_ne_nhds hplus,
      eventually_ne_nhds hminus] with x hxplus hxminus
    intro hzero
    have hfactor : (r - 2 * x) * (r + 2 * x) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hleft | hright
    · apply hxplus
      linarith
    · apply hxminus
      linarith
  have heq :
      (fun x => logisticBetaCoefficient p x beta) =ᶠ[𝓝 r]
        (fun x => P.eval x / Q.eval x) := by
    filter_upwards [hnearX, hnearP, hnearQ, hnearDelta] with x hx hp1 hq hdelta
    have hcoeff := logisticBetaCoefficient_eq_numerator_div_denominator
      p x beta hx hK hmu.ne' hp1 hq hdelta
    dsimp [P, Q, data]
    rw [eval_numeratorPoly, eval_denominatorPoly]
    exact hcoeff
  have hpoint := logisticBetaCoefficient_eq_numerator_div_denominator
    p r beta (ne_of_gt hr) hK hmu.ne' (by positivity) (by positivity) (by
      rw [← hrsq]
      nlinarith)
  have hratPath := hrat.comp hlambda
  have hpathEq :
      (fun i => logisticBetaCoefficient p (lambda i) beta) =ᶠ[l]
        (fun i => P.eval (lambda i) / Q.eval (lambda i)) :=
    hlambda.eventually heq
  have hlimitEq : logisticBetaCoefficient p r beta = P.eval r / Q.eval r := by
    dsimp [P, Q, data]
    rw [eval_numeratorPoly, eval_denominatorPoly]
    exact hpoint
  rw [hlimitEq]
  exact hratPath.congr' hpathEq.symm

/-- Along any large-domain path of actual strict critical modes, the physical
cubic coefficient converges to its value at the balancing eigenvalue. -/
theorem physical_critical_coefficient_tendsto_large_domain
    (p : PhysicalParams) (beta : ℝ)
    {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hp : p.LogisticAdmissible)
    (hstrict : ∀ᶠ i in l,
      PhysicalModeGuards.StrictCriticalMode p (d i) beta)
    (hL : Tendsto (fun i => (d i).L) l atTop) :
    Tendsto (fun i => logisticBetaCoefficient p (d i).eigenvalue beta) l
      (𝓝 (logisticBetaCoefficient p (balancingEigenvalue p) beta)) := by
  have hmode := PhysicalModeGuards.logistic_positive_parameters p hp
  have hr := balancingEigenvalue_pos p hp
  have hrsq := balancingEigenvalue_sq p hp
  have hlambda := DomainLimits.physical_critical_eigenvalue_tendsto_balancing
    p beta (balancingEigenvalue p) hmode hstrict hL hr hrsq
  exact logisticBetaCoefficient_tendsto_balancing p beta hp hlambda

/-- Under the general assumptions of Remark 1.1, the actual coefficient at
the critical small-domain exponent converges to the finite constant `d*`. -/
theorem physical_critical_coefficient_tendsto_small_domain_of_D_pos
    (p : PhysicalParams) {d : ℝ → ModeData}
    (hp : p.LogisticAdmissible)
    (hDpos : 0 < D p) (_hP : 0 ≤ scriptP p)
    (hLength : ∀ᶠ L in 𝓝[>] (0 : ℝ), (d L).L = L)
    (hstrict : ∀ᶠ L in 𝓝[>] (0 : ℝ),
      PhysicalModeGuards.StrictCriticalMode p (d L) (betaSD p)) :
    Tendsto
      (fun L => logisticBetaCoefficient p (d L).eigenvalue (betaSD p))
      (𝓝[>] 0) (𝓝 (dStar p)) := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hmode : PhysicalModeGuards.PositiveModeParameters p :=
    PhysicalModeGuards.logistic_positive_parameters p
      ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hw : 0 < p.signalOffset := PhysicalModeGuards.signalOffset_pos p hmode
  have hD : D p ≠ 0 := ne_of_gt hDpos
  have hslope : p.logisticSlope ≠ 0 := by
    exact (mul_pos ha halpha).ne'
  have hK : (physicalRationalData p (betaSD p)).K ≠ 0 := by
    exact (PhysicalModeGuards.scaledCprime_pos p hmode).ne'
  have hlambda := DomainLimits.physical_critical_eigenvalue_tendsto_atTop_small_domain
    p (betaSD p) hLength hstrict
  have hlimit := DomainLimits.logisticCoefficient_sub_linear_tendsto_dBeta_of_eigenvalue
    p (betaSD p) hu.ne' hw.ne' hmu.ne' hslope hK hlambda
  have hc := cSD_betaSD_eq_zero p hu.ne' hw.ne' hgamma.ne' hD hv.ne'
  have hdstar := dBeta_betaSD_eq_dStar p hu.ne' hw.ne' hgamma.ne' hD hv.ne'
  simpa [hc, hdstar] using hlimit

/-- Paper-facing specialization on the exponent region used for the sign of
the critical constant. -/
theorem physical_critical_coefficient_tendsto_small_domain
    (p : PhysicalParams) {d : ℝ → ModeData}
    (hp : p.LogisticAdmissible)
    (hregion : CriticalExponentRegion p)
    (hLength : ∀ᶠ L in 𝓝[>] (0 : ℝ), (d L).L = L)
    (hstrict : ∀ᶠ L in 𝓝[>] (0 : ℝ),
      PhysicalModeGuards.StrictCriticalMode p (d L) (betaSD p)) :
    Tendsto
      (fun L => logisticBetaCoefficient p (d L).eigenvalue (betaSD p))
      (𝓝[>] 0) (𝓝 (dStar p)) :=
  physical_critical_coefficient_tendsto_small_domain_of_D_pos p hp
    (critical_region_D_pos p hregion)
    (critical_region_scriptP_pos p hregion).le hLength hstrict

/-- Along any actual small-domain path of strict critical modes, the remainder
after subtracting the literal first-mode leading term tends to `d(β)`. -/
theorem physical_critical_coefficient_sub_first_mode_tendsto_small_domain
    (p : PhysicalParams) (beta : ℝ)
    {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hp : p.LogisticAdmissible)
    (hL : Tendsto (fun i => (d i).L) l (𝓝[>] (0 : ℝ)))
    (hstrict : ∀ᶠ i in l,
      PhysicalModeGuards.StrictCriticalMode p (d i) beta) :
    Tendsto
      (fun i => logisticBetaCoefficient p (d i).eigenvalue beta -
        cSD p beta * (Real.pi / (d i).L) ^ 2)
      l (𝓝 (dBeta p beta)) := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hmode : PhysicalModeGuards.PositiveModeParameters p :=
    PhysicalModeGuards.logistic_positive_parameters p
      ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hw := PhysicalModeGuards.signalOffset_pos p hmode
  have hslope : p.logisticSlope ≠ 0 := (mul_pos ha halpha).ne'
  have hK : (physicalRationalData p beta).K ≠ 0 :=
    (PhysicalModeGuards.scaledCprime_pos p hmode).ne'
  have hr := balancingEigenvalue_pos p
    ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hrsq := balancingEigenvalue_sq p
    ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hone := ModeIntervals.eventually_first_critical_mode p d beta
    (balancingEigenvalue p) hmode hr hrsq hL hstrict
  have hfirst := DomainLimits.firstMode_tendsto_atTop_small_domain.comp hL
  have heigen : Tendsto (fun i => (d i).eigenvalue) l atTop := by
    apply hfirst.congr'
    filter_upwards [hone] with i hi
    unfold ModeData.eigenvalue
    rw [hi]
    norm_num
  have hlimit := DomainLimits.logisticCoefficient_sub_linear_tendsto_dBeta_of_eigenvalue
    p beta hu.ne' hw.ne' hmu.ne' hslope hK heigen
  apply hlimit.congr'
  filter_upwards [hone] with i hi
  unfold ModeData.eigenvalue
  rw [hi]
  norm_num

theorem physical_critical_coefficient_tendsto_atTop_small_domain
    (p : PhysicalParams) (beta : ℝ)
    {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hp : p.LogisticAdmissible)
    (hL : Tendsto (fun i => (d i).L) l (𝓝[>] (0 : ℝ)))
    (hstrict : ∀ᶠ i in l,
      PhysicalModeGuards.StrictCriticalMode p (d i) beta)
    (hc : 0 < cSD p beta) :
    Tendsto (fun i => logisticBetaCoefficient p (d i).eigenvalue beta) l atTop := by
  have hrem := physical_critical_coefficient_sub_first_mode_tendsto_small_domain
    p beta hp hL hstrict
  have hfirst := DomainLimits.firstMode_tendsto_atTop_small_domain.comp hL
  have hlead : Tendsto (fun i => cSD p beta * (Real.pi / (d i).L) ^ 2)
      l atTop := hfirst.const_mul_atTop hc
  have hsum := hlead.atTop_add hrem
  apply hsum.congr'
  filter_upwards [] with i
  ring

theorem physical_critical_coefficient_tendsto_atBot_small_domain
    (p : PhysicalParams) (beta : ℝ)
    {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hp : p.LogisticAdmissible)
    (hL : Tendsto (fun i => (d i).L) l (𝓝[>] (0 : ℝ)))
    (hstrict : ∀ᶠ i in l,
      PhysicalModeGuards.StrictCriticalMode p (d i) beta)
    (hc : cSD p beta < 0) :
    Tendsto (fun i => logisticBetaCoefficient p (d i).eigenvalue beta) l atBot := by
  have hrem := physical_critical_coefficient_sub_first_mode_tendsto_small_domain
    p beta hp hL hstrict
  have hfirst := DomainLimits.firstMode_tendsto_atTop_small_domain.comp hL
  have hlead : Tendsto (fun i => cSD p beta * (Real.pi / (d i).L) ^ 2)
      l atBot := hfirst.const_mul_atTop_of_neg hc
  have hsum := hlead.atBot_add hrem
  apply hsum.congr'
  filter_upwards [] with i
  ring

/-- If the exponent polynomial is negative, every nonnegative beta gives a
subcritical small-domain divergence. -/
theorem physical_critical_coefficient_tendsto_atBot_of_scriptP_neg
    (p : PhysicalParams) (beta : ℝ)
    {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hp : p.LogisticAdmissible)
    (hL : Tendsto (fun i => (d i).L) l (𝓝[>] (0 : ℝ)))
    (hstrict : ∀ᶠ i in l,
      PhysicalModeGuards.StrictCriticalMode p (d i) beta)
    (hD : 0 < D p) (hP : scriptP p < 0) (hbeta : 0 ≤ beta) :
    Tendsto (fun i => logisticBetaCoefficient p (d i).eigenvalue beta) l atBot := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hc := cSD_neg_of_scriptP_neg p hu hv hgamma hD hP hbeta
  exact physical_critical_coefficient_tendsto_atBot_small_domain
    p beta ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩ hL hstrict hc

/-- A nonzero positive critical limit fixes the eventual direction at
`betaSD`; the zero case is intentionally left unclassified. -/
theorem eventually_pos_at_critical_small_domain
    (p : PhysicalParams) {d : ℝ → ModeData}
    (hp : p.LogisticAdmissible) (hD : 0 < D p) (hP : 0 ≤ scriptP p)
    (hLength : ∀ᶠ L in 𝓝[>] (0 : ℝ), (d L).L = L)
    (hstrict : ∀ᶠ L in 𝓝[>] (0 : ℝ),
      PhysicalModeGuards.StrictCriticalMode p (d L) (betaSD p))
    (hpos : 0 < dStar p) :
    ∀ᶠ L in 𝓝[>] (0 : ℝ),
      0 < logisticBetaCoefficient p (d L).eigenvalue (betaSD p) :=
  (physical_critical_coefficient_tendsto_small_domain_of_D_pos
    p hp hD hP hLength hstrict).eventually (eventually_gt_nhds hpos)

/-- A nonzero negative critical limit fixes the eventual direction at
`betaSD`; the zero case is intentionally left unclassified. -/
theorem eventually_neg_at_critical_small_domain
    (p : PhysicalParams) {d : ℝ → ModeData}
    (hp : p.LogisticAdmissible) (hD : 0 < D p) (hP : 0 ≤ scriptP p)
    (hLength : ∀ᶠ L in 𝓝[>] (0 : ℝ), (d L).L = L)
    (hstrict : ∀ᶠ L in 𝓝[>] (0 : ℝ),
      PhysicalModeGuards.StrictCriticalMode p (d L) (betaSD p))
    (hneg : dStar p < 0) :
    ∀ᶠ L in 𝓝[>] (0 : ℝ),
      logisticBetaCoefficient p (d L).eigenvalue (betaSD p) < 0 :=
  (physical_critical_coefficient_tendsto_small_domain_of_D_pos
    p hp hD hP hLength hstrict).eventually (eventually_lt_nhds hneg)

/-- A positive large-domain limiting coefficient gives eventual positivity. -/
theorem eventually_pos_of_large_domain_limit
    (p : PhysicalParams) (beta : ℝ)
    {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hp : p.LogisticAdmissible)
    (hstrict : ∀ᶠ i in l,
      PhysicalModeGuards.StrictCriticalMode p (d i) beta)
    (hL : Tendsto (fun i => (d i).L) l atTop)
    (hpos : 0 < logisticBetaCoefficient p (balancingEigenvalue p) beta) :
    ∀ᶠ i in l, 0 < logisticBetaCoefficient p (d i).eigenvalue beta :=
  (physical_critical_coefficient_tendsto_large_domain p beta hp hstrict hL).eventually
    (eventually_gt_nhds hpos)

/-- A negative large-domain limiting coefficient gives eventual negativity. -/
theorem eventually_neg_of_large_domain_limit
    (p : PhysicalParams) (beta : ℝ)
    {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hp : p.LogisticAdmissible)
    (hstrict : ∀ᶠ i in l,
      PhysicalModeGuards.StrictCriticalMode p (d i) beta)
    (hL : Tendsto (fun i => (d i).L) l atTop)
    (hneg : logisticBetaCoefficient p (balancingEigenvalue p) beta < 0) :
    ∀ᶠ i in l, logisticBetaCoefficient p (d i).eigenvalue beta < 0 :=
  (physical_critical_coefficient_tendsto_large_domain p beta hp hstrict hL).eventually
    (eventually_lt_nhds hneg)

end

end ChemotaxisBifurcation.CoefficientLimits
