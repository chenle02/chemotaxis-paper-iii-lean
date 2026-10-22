module
public import ChemotaxisBifurcation.PhysicalStrongPositivity
public import ChemotaxisBifurcation.SignedEllipticEnergy

@[expose] public section

/-! Actual classical population energy for small-sensitivity uniqueness.
Analytic PDE tests are derived, while scalar local compact bounds are explicit.
-/
set_option autoImplicit false
namespace ChemotaxisBifurcation.LocalStationaryEnergy
open Set MeasureTheory
noncomputable section

/-- Test the actual conservative population equation against u-uStar.
No energy identity is supplied as an input. -/
theorem population_energy {L a b alpha chi m beta U : ℝ}
    (p : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
    (hL : 0 < L) (hm : 1 ≤ m) (halpha : 0 ≤ alpha)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hbase : ∀ x ∈ Icc 0 L, 0 < 1 + p.v x)
    (hequil : a = b * U ^ alpha)
    (hv0 : p.dv 0 = 0) (hvL : p.dv L = 0) :
    (∫ x in (0 : ℝ)..L, p.du x ^ 2) +
      (∫ x in (0 : ℝ)..L, b * p.u x * (p.u x - U) * (p.u x ^ alpha - U ^ alpha)) =
      ∫ x in (0 : ℝ)..L, p.du x * MinimalFlux.flux chi m beta p.u p.v p.dv x := by
  have hu : ContinuousOn p.u (Icc 0 L) := fun x hx => (p.derivative_u x hx).continuousWithinAt
  have hdu : ContinuousOn p.du (Icc 0 L) := fun x hx => (p.derivative_du x hx).continuousWithinAt
  have hv : ContinuousOn p.v (Icc 0 L) := fun x hx => (p.derivative_v x hx).continuousWithinAt
  have hdv : ContinuousOn p.dv (Icc 0 L) := fun x hx => (p.derivative_dv x hx).continuousWithinAt
  let J := MinimalFlux.flux chi m beta p.u p.v p.dv
  have hJ : ContinuousOn J (Icc 0 L) := by
    exact ((continuousOn_const.mul ((hu.rpow_const fun _ _ => Or.inr (by linarith : 0 ≤ m)).div
      ((continuousOn_const.add hv).rpow_const fun x hx => Or.inl (hbase x hx).ne')
      (fun x hx => (Real.rpow_pos_of_pos (hbase x hx) beta).ne'))).mul hdv)
  have hreact : ContinuousOn (fun x => b * p.u x * (p.u x - U) * (p.u x ^ alpha - U ^ alpha))
      (Icc 0 L) := ((continuousOn_const.mul hu).mul (hu.sub continuousOn_const)).mul
      ((hu.rpow_const fun _ _ => Or.inr halpha).sub continuousOn_const)
  have hD : IntervalIntegrable (fun x => p.du x ^ 2) volume 0 L :=
    (hdu.pow 2).intervalIntegrable_of_Icc hL.le
  have hR := hreact.intervalIntegrable_of_Icc (μ := volume) hL.le
  have hDJ : IntervalIntegrable (fun x => p.du x * J x) volume 0 L :=
    (hdu.mul hJ).intervalIntegrable_of_Icc hL.le
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL.le
    (f := fun x => (p.u x - U) * (p.du x - J x))
    ((hu.sub continuousOn_const).mul (hdu.sub hJ))
    (f' := fun x => p.du x ^ 2 + b * p.u x * (p.u x - U) * (p.u x ^ alpha - U ^ alpha) - p.du x * J x)
    (fun x hx => by
      have hx' := Ioo_subset_Icc_self hx
      have hflux := (PhysicalStrongPositivity.flux_hasDerivWithinAt
        (chi := chi) (beta := beta) hm hbase hx' (p.derivative_u x hx')
        (p.derivative_v x hx') (p.derivative_dv x hx')).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
      have hstat := p.stationary x hx
      rw [hflux.deriv, Real.rpow_add (hpos x hx'), Real.rpow_one] at hstat
      have htest := ((p.derivative_u x hx').hasDerivAt (Icc_mem_nhds hx.1 hx.2)).sub_const U
      have htotal := ((p.derivative_du x hx').hasDerivAt (Icc_mem_nhds hx.1 hx.2)).fun_sub hflux
      convert htest.mul htotal using 1
      dsimp only [J]
      linear_combination -(p.u x - U) * hstat + (p.u x - U) * p.u x * hequil)
    ((hD.add hR).sub hDJ)
  have hJ0 : J 0 = 0 := by simp [J, MinimalFlux.flux, hv0]
  have hJL : J L = 0 := by simp [J, MinimalFlux.flux, hvL]
  rw [p.neumann_left, p.neumann_right, hJ0, hJL] at h
  rw [intervalIntegral.integral_sub (hD.add hR) hDJ,
    intervalIntegral.integral_add hD hR] at h
  exact sub_eq_zero.mp (by simpa only [sub_self, mul_zero] using h)


/-- The same signed elliptic energy controls the gradient in L2. -/
theorem signal_gradient_bound {L mu : ℝ} {F : ℝ → ℝ}
    (p : SignedEllipticEnergy.Profile L mu F) (hL : 0 ≤ L) (hmu : 0 < mu)
    (hF : ContinuousOn F (Icc 0 L)) :
    2 * mu * (∫ x in (0 : ℝ)..L, p.dV x ^ 2) ≤ ∫ x in (0 : ℝ)..L, F x ^ 2 := by
  have hV0 : 0 ≤ ∫ x in (0 : ℝ)..L, p.V x ^ 2 :=
    intervalIntegral.integral_nonneg hL fun _ _ => sq_nonneg _
  have hE := p.energy hL hF
  have hF2 : IntervalIntegrable (fun x => F x ^ 2) volume 0 L :=
    (hF.pow 2).intervalIntegrable_of_Icc hL
  have hV2 : IntervalIntegrable (fun x => p.V x ^ 2) volume 0 L :=
    (p.continuous_V.pow 2).intervalIntegrable_of_Icc hL
  have hFV : IntervalIntegrable (fun x => F x * p.V x) volume 0 L :=
    (hF.mul p.continuous_V).intervalIntegrable_of_Icc hL
  have hY : 2 * mu * (∫ x in (0 : ℝ)..L, F x * p.V x) ≤
      (∫ x in (0 : ℝ)..L, F x ^ 2) + mu ^ 2 * (∫ x in (0 : ℝ)..L, p.V x ^ 2) := by
    have h := intervalIntegral.integral_mono_on hL (hFV.const_mul (2 * mu))
      (hF2.add (hV2.const_mul (mu ^ 2))) (fun x _ => by nlinarith [sq_nonneg (F x - mu * p.V x)])
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hF2
      (hV2.const_mul (mu ^ 2)), intervalIntegral.integral_const_mul] at h
    exact h
  nlinarith [mul_nonneg (sq_nonneg mu) hV0]

/-- Scalar absorption of the two derived PDE energies. -/
theorem absorb_energies {Du U2 Dv mu c chi M K : ℝ}
    (hDu : 0 ≤ Du) (hU : 0 ≤ U2) (hmu : 0 < mu)
    (hpop : Du + 2 * c * U2 ≤ chi ^ 2 * M ^ 2 * Dv)
    (hsig : 2 * mu * Dv ≤ K ^ 2 * U2)
    (hsmall : chi ^ 2 * M ^ 2 * K ^ 2 < 4 * mu * c) : U2 = 0 := by
  have h0 := mul_le_mul_of_nonneg_left hpop (show 0 ≤ 2 * mu by positivity)
  have h1 := mul_le_mul_of_nonneg_left hsig (mul_nonneg (sq_nonneg chi) (sq_nonneg M))
  have hgap : 0 < 4 * mu * c - chi ^ 2 * M ^ 2 * K ^ 2 := by linarith
  have hprod : (4 * mu * c - chi ^ 2 * M ^ 2 * K ^ 2) * U2 ≤ 0 := by
    nlinarith [mul_nonneg hmu.le hDu]
  exact le_antisymm (nonpos_of_mul_nonpos_right hprod hgap) hU


/-- Small physical sensitivity forces the actual stationary population to
be the equilibrium. The functional inputs are explicit scalar mobility,
source-Lipschitz and reaction-coercivity bounds; the PDE energies are proved.
The signal Profile records an actual shifted elliptic equation, not energy. -/
theorem eq_equilibrium_of_small_sensitivity
    {L a b alpha chi m beta U mu c M K : ℝ} {F : ℝ → ℝ}
    (p : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
    (sig : SignedEllipticEnergy.Profile L mu F)
    (hL : 0 < L) (hmu : 0 < mu) (hm : 1 ≤ m) (halpha : 0 ≤ alpha)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hbase : ∀ x ∈ Icc 0 L, 0 < 1 + p.v x)
    (hequil : a = b * U ^ alpha) (hv0 : p.dv 0 = 0) (hvL : p.dv L = 0)
    (hF : ContinuousOn F (Icc 0 L)) (hsigDv : sig.dV = p.dv)
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hmob : ∀ x ∈ Icc 0 L, |p.u x ^ m / (1 + p.v x) ^ beta| ≤ M)
    (hsource : ∀ x ∈ Icc 0 L, |F x| ≤ K * |p.u x - U|)
    (hcoerc : ∀ x ∈ Icc 0 L,
      c * (p.u x - U) ^ 2 ≤ b * p.u x * (p.u x - U) * (p.u x ^ alpha - U ^ alpha))
    (hsmall : chi ^ 2 * M ^ 2 * K ^ 2 < 4 * mu * c) :
    ∀ x ∈ Icc 0 L, p.u x = U := by
  have hu : ContinuousOn p.u (Icc 0 L) := fun x hx => (p.derivative_u x hx).continuousWithinAt
  have hdu : ContinuousOn p.du (Icc 0 L) := fun x hx => (p.derivative_du x hx).continuousWithinAt
  have hv : ContinuousOn p.v (Icc 0 L) := fun x hx => (p.derivative_v x hx).continuousWithinAt
  have hdv : ContinuousOn p.dv (Icc 0 L) := fun x hx => (p.derivative_dv x hx).continuousWithinAt
  let J := MinimalFlux.flux chi m beta p.u p.v p.dv
  have hJ : ContinuousOn J (Icc 0 L) := by
    exact ((continuousOn_const.mul ((hu.rpow_const fun _ _ => Or.inr (by linarith : 0 ≤ m)).div
      ((continuousOn_const.add hv).rpow_const fun x hx => Or.inl (hbase x hx).ne')
      (fun x hx => (Real.rpow_pos_of_pos (hbase x hx) beta).ne'))).mul hdv)
  have hR : ContinuousOn (fun x => b * p.u x * (p.u x - U) * (p.u x ^ alpha - U ^ alpha))
      (Icc 0 L) := ((continuousOn_const.mul hu).mul (hu.sub continuousOn_const)).mul
      ((hu.rpow_const fun _ _ => Or.inr halpha).sub continuousOn_const)
  have hUi : IntervalIntegrable (fun x => (p.u x - U) ^ 2) volume 0 L :=
    ((hu.sub continuousOn_const).pow 2).intervalIntegrable_of_Icc hL.le
  have hDi : IntervalIntegrable (fun x => p.du x ^ 2) volume 0 L :=
    (hdu.pow 2).intervalIntegrable_of_Icc hL.le
  have hDvi : IntervalIntegrable (fun x => p.dv x ^ 2) volume 0 L :=
    (hdv.pow 2).intervalIntegrable_of_Icc hL.le
  have hJi : IntervalIntegrable (fun x => p.du x * J x) volume 0 L :=
    (hdu.mul hJ).intervalIntegrable_of_Icc hL.le
  have hci := intervalIntegral.integral_mono_on hL.le (hUi.const_mul c)
    (hR.intervalIntegrable_of_Icc hL.le) hcoerc
  rw [intervalIntegral.integral_const_mul] at hci
  have hY : ∀ x ∈ Icc 0 L, 2 * (p.du x * J x) ≤ p.du x ^ 2 + chi ^ 2 * M ^ 2 * p.dv x ^ 2 := by
    intro x hx
    have hsq := (sq_le_sq₀ (abs_nonneg (p.u x ^ m / (1 + p.v x) ^ beta)) hM).mpr (hmob x hx)
    rw [sq_abs] at hsq
    have hJsq : J x ^ 2 ≤ chi ^ 2 * M ^ 2 * p.dv x ^ 2 := by
      calc
        J x ^ 2 = (chi * p.dv x) ^ 2 * (p.u x ^ m / (1 + p.v x) ^ beta) ^ 2 := by
          dsimp only [J, MinimalFlux.flux]
          ring
        _ ≤ (chi * p.dv x) ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = chi ^ 2 * M ^ 2 * p.dv x ^ 2 := by ring
    nlinarith [sq_nonneg (p.du x - J x)]
  have hyi := intervalIntegral.integral_mono_on hL.le (hJi.const_mul 2)
    (hDi.add (hDvi.const_mul (chi ^ 2 * M ^ 2))) hY
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hDi
    (hDvi.const_mul (chi ^ 2 * M ^ 2)), intervalIntegral.integral_const_mul] at hyi
  have he := population_energy p hL hm halpha hpos hbase hequil hv0 hvL
  have hpop : (∫ x in (0 : ℝ)..L, p.du x ^ 2) +
      2 * c * (∫ x in (0 : ℝ)..L, (p.u x - U) ^ 2) ≤
      chi ^ 2 * M ^ 2 * (∫ x in (0 : ℝ)..L, p.dv x ^ 2) := by
    change (∫ x in (0 : ℝ)..L, p.du x ^ 2) + _ = (∫ x in (0 : ℝ)..L, p.du x * J x) at he
    linarith
  have hF2 : (∫ x in (0 : ℝ)..L, F x ^ 2) ≤ K ^ 2 * (∫ x in (0 : ℝ)..L, (p.u x - U) ^ 2) := by
    have hi := intervalIntegral.integral_mono_on hL.le
      ((hF.pow 2).intervalIntegrable_of_Icc hL.le) (hUi.const_mul (K ^ 2)) (fun x hx => by
        change F x ^ 2 ≤ K ^ 2 * (p.u x - U) ^ 2
        have hsq := (sq_le_sq₀ (abs_nonneg (F x)) (mul_nonneg hK (abs_nonneg (p.u x - U)))).mpr
          (hsource x hx)
        simpa only [sq_abs, mul_pow] using hsq)
    simpa only [intervalIntegral.integral_const_mul, Pi.pow_apply] using hi
  have hs := signal_gradient_bound sig hL.le hmu hF
  rw [hsigDv] at hs
  have hDu0 : 0 ≤ ∫ x in (0 : ℝ)..L, p.du x ^ 2 :=
    intervalIntegral.integral_nonneg hL.le fun _ _ => sq_nonneg _
  have hU0 : 0 ≤ ∫ x in (0 : ℝ)..L, (p.u x - U) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le fun _ _ => sq_nonneg _
  have hz := absorb_energies hDu0 hU0 hmu hpop (hs.trans hF2) hsmall
  have hzero := IntervalMoments.eq_zero_of_integral_eq_zero hL
    ((hu.sub continuousOn_const).pow 2) (fun _ _ => sq_nonneg _) hz
  intro x hx
  have hzx : (p.u x - U) ^ 2 = 0 := by
    simpa only [Pi.pow_apply, Pi.sub_apply] using hzero x hx
  nlinarith


/-- Positive powers have a strictly positive lower slope on every fixed
compact interval away from zero. This includes fractional positive powers. -/
theorem power_coercivity_on_compact {ell H alpha : ℝ}
    (hell : 0 < ell) (hLH : ell ≤ H) (halpha : 0 < alpha) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ Icc ell H, ∀ y ∈ Icc ell H,
      d * (x - y) ^ 2 ≤ (x - y) * (x ^ alpha - y ^ alpha) := by
  have hc : ContinuousOn (fun x : ℝ => alpha * x ^ (alpha - 1)) (Icc ell H) :=
    continuousOn_const.mul (continuousOn_id.rpow_const fun x hx =>
      Or.inl (hell.trans_le hx.1).ne')
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hLH) hc
  let d := alpha * z ^ (alpha - 1)
  have hd : 0 < d := mul_pos halpha (Real.rpow_pos_of_pos (hell.trans_le hz.1) _)
  refine ⟨d, hd, ?_⟩
  have hord : ∀ x ∈ Icc ell H, ∀ y ∈ Icc ell H, x < y →
      d * (y - x) ^ 2 ≤ (y - x) * (y ^ alpha - x ^ alpha) := by
    intro x hx y hy hxy
    have hsub : Icc x y ⊆ Icc ell H := Icc_subset_Icc hx.1 hy.2
    have hcont : ContinuousOn (fun t : ℝ => t ^ alpha) (Icc x y) :=
      continuousOn_id.rpow_const fun t ht => Or.inl (hell.trans_le (hsub ht).1).ne'
    obtain ⟨t, ht, hmean⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ alpha)
      (fun t => alpha * t ^ (alpha - 1)) hxy hcont
      (fun t ht => Real.hasDerivAt_rpow_const (Or.inl (hell.trans_le (hsub (Ioo_subset_Icc_self ht)).1).ne'))
    have hbnd : d ≤ alpha * t ^ (alpha - 1) := hmin (hsub (Ioo_subset_Icc_self ht))
    rw [hmean] at hbnd
    have hinc := (le_div_iff₀ (sub_pos.mpr hxy)).mp hbnd
    have hprod := mul_le_mul_of_nonneg_left hinc (sub_nonneg.mpr hxy.le)
    nlinarith
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have h := hord x hx y hy hxy
    nlinarith
  · rw [hxy]
    simp
  · exact hord y hy x hx hyx

/-- The logistic reaction supplies uniform quadratic coercivity on a fixed
positive compact population range. -/
theorem reaction_coercivity_on_compact {ell H alpha b U : ℝ}
    (hell : 0 < ell) (hLH : ell ≤ H) (halpha : 0 < alpha) (hb : 0 < b)
    (hU : U ∈ Icc ell H) :
    ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Icc ell H,
      c * (u - U) ^ 2 ≤ b * u * (u - U) * (u ^ alpha - U ^ alpha) := by
  obtain ⟨d, hd, hpow⟩ := power_coercivity_on_compact hell hLH halpha
  refine ⟨b * ell * d, mul_pos (mul_pos hb hell) hd, ?_⟩
  intro u hu
  have hu0 : 0 ≤ u := (hell.trans_le hu.1).le
  have h1 := mul_le_mul_of_nonneg_left (hpow u hu U hU) (mul_nonneg hb.le hu0)
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu.1 hb.le)
    (mul_nonneg hd.le (sq_nonneg (u - U)))
  nlinarith


/-- A bounded population and nonnegative signal give a uniform mobility
bound without a separate coefficient or flux estimate. -/
theorem mobility_bound {u v H m beta : ℝ} (hu : 0 ≤ u) (hH : u ≤ H)
    (hv : 0 ≤ v) (hm : 0 ≤ m) (hbeta : 0 ≤ beta) :
    |u ^ m / (1 + v) ^ beta| ≤ H ^ m := by
  have hden : 1 ≤ (1 + v) ^ beta := Real.one_le_rpow (by linarith) hbeta
  rw [abs_of_nonneg (div_nonneg (Real.rpow_nonneg hu m)
    (Real.rpow_nonneg (by linarith : 0 ≤ 1 + v) beta))]
  exact (div_le_self (Real.rpow_nonneg hu m) hden).trans (Real.rpow_le_rpow hu hH hm)

/-- A strictly positive scalar sensitivity radius follows without division
by the source Lipschitz constant, so degenerate K=0 is included. -/
theorem exists_small_sensitivity_radius {mu c M K : ℝ} (hmu : 0 < mu) (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ chi : ℝ, |chi| < epsilon →
      chi ^ 2 * M ^ 2 * K ^ 2 < 4 * mu * c := by
  have hden : 0 < 1 + M ^ 2 * K ^ 2 := by positivity
  let epsilon := min 1 (4 * mu * c / (1 + M ^ 2 * K ^ 2))
  have heps : 0 < epsilon := lt_min one_pos (div_pos (by positivity) hden)
  refine ⟨epsilon, heps, ?_⟩
  intro chi hchi
  have hchi1 : |chi| < 1 := hchi.trans_le (min_le_left _ _)
  have hsq : chi ^ 2 ≤ |chi| := by nlinarith [sq_abs chi, abs_nonneg chi]
  have hq : chi ^ 2 < 4 * mu * c / (1 + M ^ 2 * K ^ 2) :=
    (hsq.trans_lt hchi).trans_le (min_le_right _ _)
  have h := (lt_div_iff₀ hden).mp hq
  nlinarith [sq_nonneg chi]

/-- Local uniqueness on a fixed positive compact population range, with
reaction coercivity, mobility bound and positive sensitivity radius derived.
Only the source Lipschitz estimate and actual shifted signal equation remain
functional application data; they do not assume the local-uniqueness target. -/
theorem exists_uniqueness_radius_on_compact
    {L a b alpha m beta U mu ell H K : ℝ}
    (hL : 0 < L) (hmu : 0 < mu) (hm : 1 ≤ m) (hbeta : 0 ≤ beta)
    (halpha : 0 < alpha) (hb : 0 < b) (hell : 0 < ell) (hLH : ell ≤ H)
    (hU : U ∈ Icc ell H) (hequil : a = b * U ^ alpha) (hK : 0 ≤ K) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ chi : ℝ, |chi| < epsilon →
      ∀ p : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta,
      ∀ (F : ℝ → ℝ) (sig : SignedEllipticEnergy.Profile L mu F),
      ContinuousOn F (Icc 0 L) → sig.dV = p.dv →
      (∀ x ∈ Icc 0 L, p.u x ∈ Icc ell H) →
      (∀ x ∈ Icc 0 L, 0 ≤ p.v x) → p.dv 0 = 0 → p.dv L = 0 →
      (∀ x ∈ Icc 0 L, |F x| ≤ K * |p.u x - U|) →
      ∀ x ∈ Icc 0 L, p.u x = U := by
  obtain ⟨c, hc, hcoerc⟩ := reaction_coercivity_on_compact hell hLH halpha hb hU
  obtain ⟨epsilon, heps, hsmall⟩ := exists_small_sensitivity_radius
    (M := H ^ m) (K := K) hmu hc
  refine ⟨epsilon, heps, ?_⟩
  intro chi hchi p F sig hF hsig hup hv hv0 hvL hsource
  apply eq_equilibrium_of_small_sensitivity p sig hL hmu hm halpha.le
    (fun x hx => hell.trans_le (hup x hx).1)
    (fun x hx => by linarith [hv x hx]) hequil hv0 hvL hF hsig
    (Real.rpow_nonneg (hell.le.trans hLH) m) hK
    (fun x hx => mobility_bound ((hell.trans_le (hup x hx).1).le) (hup x hx).2
      (hv x hx) (by linarith) hbeta) hsource
    (fun x hx => hcoerc (p.u x) (hup x hx)) (hsmall chi hchi)


/-- Construct the shifted signal-energy profile from the literal physical
signal equation. The source is nu*(u^gamma-U^gamma), not an abstract forcing
identified only through its desired energy estimate. -/
def shiftedSignalProfile {L a b alpha chi m beta mu nu gamma U V : ℝ}
    (p : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
    (hequil : mu * V = nu * U ^ gamma)
    (hsignal : ∀ x ∈ Ioo 0 L, p.ddv x - mu * p.v x + nu * p.u x ^ gamma = 0)
    (hv0 : p.dv 0 = 0) (hvL : p.dv L = 0) :
    SignedEllipticEnergy.Profile L mu (fun x => nu * (p.u x ^ gamma - U ^ gamma)) where
  V := fun x => p.v x - V
  dV := p.dv
  continuous_V := by
    have hv : ContinuousOn p.v (Icc 0 L) := fun x hx => (p.derivative_v x hx).continuousWithinAt
    exact hv.sub continuousOn_const
  continuous_dV := fun x hx => (p.derivative_dv x hx).continuousWithinAt
  derivative_V := fun x hx =>
    ((p.derivative_v x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).sub_const V
  equation := fun x hx => by
    have hd := (p.derivative_dv x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
    convert hd using 1
    linarith [hsignal x hx]
  neumann_left := hv0
  neumann_right := hvL

/-- The compact-range small-sensitivity theorem for both literal physical
stationary equations. Source Lipschitz control is the sole remaining scalar
application estimate, supplied by the independently proved power-source MVT. -/
theorem exists_uniqueness_radius_of_physical_system
    {L a b alpha m beta U V mu nu gamma ell H K : ℝ}
    (hL : 0 < L) (hmu : 0 < mu) (hm : 1 ≤ m) (hbeta : 0 ≤ beta)
    (halpha : 0 < alpha) (hb : 0 < b) (hell : 0 < ell) (hLH : ell ≤ H)
    (hU : U ∈ Icc ell H) (hequil : a = b * U ^ alpha)
    (hsigequil : mu * V = nu * U ^ gamma) (hK : 0 ≤ K) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ chi : ℝ, |chi| < epsilon →
      ∀ p : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta,
      (∀ x ∈ Icc 0 L, p.u x ∈ Icc ell H) →
      (∀ x ∈ Icc 0 L, 0 ≤ p.v x) → p.dv 0 = 0 → p.dv L = 0 →
      (∀ x ∈ Ioo 0 L, p.ddv x - mu * p.v x + nu * p.u x ^ gamma = 0) →
      (∀ x ∈ Icc 0 L, |nu * (p.u x ^ gamma - U ^ gamma)| ≤ K * |p.u x - U|) →
      ∀ x ∈ Icc 0 L, p.u x = U := by
  obtain ⟨epsilon, heps, huni⟩ := exists_uniqueness_radius_on_compact
    hL hmu hm hbeta halpha hb hell hLH hU hequil hK
  refine ⟨epsilon, heps, ?_⟩
  intro chi hchi p hup hv hv0 hvL hsignal hsource
  let sig := shiftedSignalProfile p hsigequil hsignal hv0 hvL
  have hu : ContinuousOn p.u (Icc 0 L) := fun x hx => (p.derivative_u x hx).continuousWithinAt
  have hF : ContinuousOn (fun x => nu * (p.u x ^ gamma - U ^ gamma)) (Icc 0 L) :=
    continuousOn_const.mul ((hu.rpow_const fun x hx =>
      Or.inl (hell.trans_le (hup x hx).1).ne').sub continuousOn_const)
  exact huni chi hchi p _ sig hF rfl hup hv hv0 hvL hsource

end
end ChemotaxisBifurcation.LocalStationaryEnergy
