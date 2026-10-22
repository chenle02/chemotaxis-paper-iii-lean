module
public import ChemotaxisBifurcation.SpikeEstimatesLogistic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Full-mobility classical logistic C1 deduction

The frozen v2 argument uses a first-integral/Gronwall route for
`1 <= m <= alpha + 2`, beyond the older energy estimate's mobility range.
This file bounds the derivative of `log(u+1)`, integrates that bound over the
whole interval, and exponentiates. Constants are intentionally nonoptimal.
The final chain derives the first-integral and signal-gradient inputs from
the literal stationary equations; upstream mass and moment deductions remain
explicit so the actual classical-profile wrapper can supply them.
-/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
namespace ChemotaxisBifurcation.SpikeEstimates

/-- A logarithmic Gronwall estimate for a positive classical population
profile. The power moment controls the coefficient, not the unknown maximum.
No supremum or Gronwall conclusion is an input. -/
theorem sup_le_of_derivative_power_bound (L uStar A H m M : ℝ) (u du : ℝ → ℝ)
    (hL : 0 < L) (hA : 0 ≤ A) (hH : 0 ≤ H) (hm : 1 ≤ m)
    (hu : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo 0 L, |du x| ≤ A * u x ^ m + H)
    (hmean : ∫ x in (0 : ℝ)..L, u x ≤ L * uStar)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (m - 1) ≤ M) :
    ∀ x ∈ Icc 0 L, u x ≤ (uStar + 1) * Real.exp (A * M + H * L) := by
  have hr : 0 ≤ m - 1 := by linarith
  have hpow := hu.rpow_const (p := m - 1) (fun _ _ => Or.inr hr)
  have hweight : ContinuousOn (fun x => A * u x ^ (m - 1) + H) (Icc 0 L) :=
    (hpow.const_smul A).add continuousOn_const
  have hweight0 : ∀ x ∈ Icc 0 L, 0 ≤ A * u x ^ (m - 1) + H := fun x hx =>
    add_nonneg (mul_nonneg hA (Real.rpow_nonneg (hpos x hx).le _)) hH
  have hlog : ContinuousOn (fun x => Real.log (u x + 1)) (Icc 0 L) :=
    (hu.add continuousOn_const).log (fun x hx => by
      simp only [Pi.add_apply]
      linarith [hpos x hx])
  have hlogderiv : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun x => Real.log (u x + 1)) (du x / (u x + 1)) x := by
    intro x hx
    exact ((hderiv x hx).add_const 1).log (by linarith [hpos x (Ioo_subset_Icc_self hx)])
  have hlogbound : ∀ x ∈ Ioo 0 L,
      |du x / (u x + 1)| ≤ A * u x ^ (m - 1) + H := by
    intro x hx
    have hux := hpos x (Ioo_subset_Icc_self hx)
    have hden : 0 < u x + 1 := by linarith
    have hp : u x ^ m = u x ^ (m - 1) * u x := by
      have ht := Real.rpow_add_one hux.ne' (m - 1)
      simpa only [sub_add_cancel] using ht
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
    calc |du x| ≤ A * u x ^ m + H := hdu x hx
      _ ≤ (A * u x ^ (m - 1) + H) * (u x + 1) := by
        rw [hp]
        nlinarith [mul_nonneg hA (Real.rpow_nonneg hux.le (m - 1)),
          mul_nonneg hH hux.le]
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hu
  have hlow := IntervalMoments.le_integral_of_le hL.le hu (fun z hz => hmin hz)
  have huy : u y ≤ uStar := le_of_mul_le_mul_left (hlow.trans hmean) hL
  have hwint : (∫ t in (0 : ℝ)..L, A * u t ^ (m - 1) + H) ≤ A * M + H * L := by
    rw [intervalIntegral.integral_add ((hpow.intervalIntegrable_of_Icc hL.le).const_mul A)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hmoment hA]
  intro x hx
  have ht := le_add_integral_of_abs_deriv_le hlog hlogderiv hweight hweight0 hlogbound x hx y hy
  have hly : Real.log (u y + 1) ≤ Real.log (uStar + 1) :=
    Real.log_le_log (by linarith [hpos y hy]) (by linarith)
  have hlexp : Real.log (u x + 1) ≤ Real.log (uStar + 1) + (A * M + H * L) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlexp
  rw [Real.exp_add, Real.exp_log (by linarith [hpos x hx]),
    Real.exp_log (by linarith [hpos y hy])] at hexp
  linarith

/-- The moment interpolation estimate includes exponent zero. This matters
for the full manuscript mobility endpoint m=1. -/
theorem logistic_power_integral_le_nonneg (L uStar alpha r : ℝ) (u : ℝ → ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (huStar : 0 ≤ uStar)
    (hr : 0 ≤ r) (hr1 : r ≤ 1 + alpha)
    (hu : ContinuousOn u (Icc 0 L)) (hu0 : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha)) :
    ∫ x in (0 : ℝ)..L, u x ^ r ≤ L * uStar ^ r := by
  rcases eq_or_lt_of_le hr with heq | hlt
  · rw [← heq]
    simp
  · exact IntervalMoments.logistic_power_integral_le L uStar alpha r u hL halpha huStar
      hlt hr1 hu hu0 hmoment


/-- An explicit, deliberately nonoptimal full-mobility population bound. -/
noncomputable def gronwallPopulationBound (L a gamma nu Xbar m uStar : ℝ) : ℝ :=
  (uStar + 1) * Real.exp
    ((Xbar * (2 * nu * L * uStar ^ gamma)) * (L * uStar ^ (m - 1)) +
      (2 * a * L * uStar) * L)

/-- Full-range C1 estimate from the first integral and moment inputs of the
classical stationary system. Covers 1<=m<=alpha+2, including both endpoints.
The first integral and moment bounds are derived upstream from the literal
population equation; this statement assumes no maximum bound. -/
theorem logistic_C1_gronwall_of_first_integral
    (L a alpha gamma nu chi Xbar m beta uStar : ℝ) (u v du dv F : ℝ → ℝ)
    (hL : 0 < L) (ha : 0 ≤ a) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha + 2) (hbeta : 0 ≤ beta)
    (hnu : 0 ≤ nu) (huStar : 0 ≤ uStar) (hchi : |chi| ≤ Xbar)
    (hu : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hv0 : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hfirst : ∀ x ∈ Icc 0 L,
      du x = chi * (u x ^ m / (1 + v x) ^ beta) * dv x - F x)
    (hF : ∀ x ∈ Icc 0 L, |F x| ≤ 2 * a * L * uStar)
    (hvx : ∀ x ∈ Icc 0 L, |dv x| ≤ 2 * nu * L * uStar ^ gamma)
    (hmean : ∫ x in (0 : ℝ)..L, u x ≤ L * uStar)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha)) :
    ∀ x ∈ Icc 0 L,
      |u x| ≤ max (gronwallPopulationBound L a gamma nu Xbar m uStar)
        (Xbar * (gronwallPopulationBound L a gamma nu Xbar m uStar) ^ m *
          (2 * nu * L * uStar ^ gamma) + 2 * a * L * uStar) ∧
      |du x| ≤ max (gronwallPopulationBound L a gamma nu Xbar m uStar)
        (Xbar * (gronwallPopulationBound L a gamma nu Xbar m uStar) ^ m *
          (2 * nu * L * uStar ^ gamma) + 2 * a * L * uStar) := by
  have hu0 : ∀ x ∈ Icc 0 L, 0 ≤ u x := fun x hx => (hpos x hx).le
  set K := 2 * nu * L * uStar ^ gamma with hKdef
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hX : 0 ≤ Xbar := (abs_nonneg chi).trans hchi
  have hH : 0 ≤ 2 * a * L * uStar := by positivity
  have hpow := logistic_power_integral_le_nonneg L uStar alpha (m - 1) u hL halpha
    huStar (by linarith) (by linarith) hu hu0 hmoment
  have hdubound : ∀ x ∈ Ioo 0 L, |du x| ≤ (Xbar * K) * u x ^ m + 2 * a * L * uStar := by
    intro x hx
    have hx' := Ioo_subset_Icc_self hx
    have hJ := flux_abs_le chi m beta K (u x) (v x) _ (dv x) (hu0 x hx') (hv0 x hx')
      hbeta rfl (hvx x hx')
    have hJK : |chi| * u x ^ m * K ≤ (Xbar * K) * u x ^ m := by
      have hh := mul_le_mul_of_nonneg_right hchi (mul_nonneg (Real.rpow_nonneg (hu0 x hx') m) hK)
      nlinarith
    rw [hfirst x hx']
    exact (abs_sub _ _).trans (by linarith [hF x hx'])
  have hB := sup_le_of_derivative_power_bound L uStar (Xbar * K) (2 * a * L * uStar)
    m (L * uStar ^ (m - 1)) u du hL (mul_nonneg hX hK) hH hm hu hpos hderiv hdubound hmean hpow
  intro x hx
  have hout := logistic_C1_bound L a uStar chi Xbar m beta K
    (gronwallPopulationBound L a gamma nu Xbar m uStar) u v du dv F
    (by linarith) hbeta hK hchi hu0 hv0 hfirst hF hvx
    (by simpa only [gronwallPopulationBound, hKdef] using hB) x hx
  rw [abs_of_pos (hpos x hx)]
  exact ⟨hout.2.1, hout.2.2⟩

/-- The full current-v2 mobility C1 chain from the literal two stationary
system equations, Neumann data and upstream logistic mass/moment deductions.
Unlike the energy route this includes every 1<=m<=alpha+2. -/
theorem logistic_C1_gronwall_chain (L a b alpha gamma mu nu chi Xbar m beta uStar : ℝ)
    (u v du ddu dv ddv dJ : ℝ → ℝ)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1 + alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha + 2) (hbeta : 0 ≤ beta)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (huStar : 0 ≤ uStar) (hchi : |chi| ≤ Xbar)
    (hu : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hdu_cont : ContinuousOn du (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hv : ContinuousOn v (Icc 0 L)) (hv0 : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hdv : ContinuousOn dv (Icc 0 L))
    (hddv : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (hsignal : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hJcont : ContinuousOn (MinimalFlux.flux chi m beta u v dv) (Icc 0 L))
    (hJ : ∀ x ∈ Ioo 0 L, HasDerivAt (MinimalFlux.flux chi m beta u v dv) (dJ x) x)
    (hstat : ∀ x ∈ Ioo 0 L, ddu x - dJ x + a * u x - b * u x ^ (1 + alpha) = 0)
    (hbc_u0 : du 0 = 0) (_hbc_uL : du L = 0) (hbc_v0 : dv 0 = 0) (hbc_vL : dv L = 0)
    (hmass : a * ∫ x in (0 : ℝ)..L, u x = b * ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha))
    (hmean : ∫ x in (0 : ℝ)..L, u x ≤ L * uStar)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha)) :
    ∀ x ∈ Icc 0 L,
      |u x| ≤ max (gronwallPopulationBound L a gamma nu Xbar m uStar)
        (Xbar * (gronwallPopulationBound L a gamma nu Xbar m uStar) ^ m *
          (2 * nu * L * uStar ^ gamma) + 2 * a * L * uStar) ∧
      |du x| ≤ max (gronwallPopulationBound L a gamma nu Xbar m uStar)
        (Xbar * (gronwallPopulationBound L a gamma nu Xbar m uStar) ^ m *
          (2 * nu * L * uStar ^ gamma) + 2 * a * L * uStar) := by
  have hu0 : ∀ x ∈ Icc 0 L, 0 ≤ u x := fun x hx => (hpos x hx).le
  have hgrad := logistic_gradient_le L mu nu gamma alpha uStar u v dv ddv hL hmu hnu
    halpha hgamma0 hgamma1 huStar hu hu0 hv hv0 hdv hddv hsignal hbc_v0 hbc_vL hmoment
  have hfirst := logistic_first_integral L a b alpha chi m beta u v du ddu dv dJ hL.le
    halpha hu hdu_cont hddu hJcont hJ hstat hbc_u0 hbc_v0
  have hF := logistic_F_bound L a b alpha uStar u ha.le hb.le halpha hu hu0 hmass hmean
  exact logistic_C1_gronwall_of_first_integral L a alpha gamma nu chi Xbar m beta uStar u v du dv
    (fun x => ∫ y in (0 : ℝ)..x, (a * u y - b * u y ^ (1 + alpha)))
    hL ha.le halpha hm hm1 hbeta hnu huStar hchi hu hpos hdu hv0 hfirst
    (fun x hx => (hF x hx).2) hgrad hmean hmoment
end ChemotaxisBifurcation.SpikeEstimates
