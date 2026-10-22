module
public import ChemotaxisBifurcation.SpikeEstimates
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section

/-!
# Constant limits at large sensitivity (Lemma 5.1)

This file proves the finite and real-analysis deductions in the proof of
Lemma 5.1 (TeX `L:minimal-spike-limit`, lines 3407–3477 of the October 8
manuscript) once its analytic inputs are granted.

The analytic inputs are kept as explicit hypotheses:

* the subsequence extraction (weak compactness in `L^q`, the compact embedding
  `W^{2,q} ↪ C¹`, TeX lines 3423–3430) is represented by a single sequence
  along which `(v_n)_x → V_x` uniformly on `[0,L]` and
  `∫_p^q u_n^γ → ∫_p^q W` for every subinterval `[p,q] ⊆ [0,L]` (weak
  convergence tested against indicators);
* the limiting equation `E:lm2-v-limit` (TeX line 3432) is stated in the
  integrated form `V_x(x) = ∫_0^x (μ V - ν W)`, `V_x(L) = 0`;
* the first integral `E:un-eq` (TeX line 3438), the bound on `F_n`, the
  lower bound `(1+v_n)^{-β} ≥ κ`, the mass bound `∫ u_n ≤ M` and the
  `L^r` bound are hypotheses on each `u_n` (they are proved separately in
  `SpikeEstimatesLogistic`, `MinimalFlux` and `IntervalMoments`).

What is proved here:

* the test-function estimate `χ_n κ σ ∫_J u_n^m ≤ |∫ u_n φ_x| + |∫ F_n φ|`
  (TeX lines 3453–3457) by integration by parts, and `∫_J u_n^m → 0`;
* `∫_J u_n^γ → 0`, hence `W = 0` a.e. on `J` (TeX lines 3458–3463). The
  manuscript uses Hölder and Chebyshev; here the same conclusion is reached
  from the pointwise bound `t^γ ≤ ε^γ + η t^r + C_{ε,η} t^m` (`γ < r`);
* `W V_x = 0` a.e. from the vanishing on every closed interval where
  `V_x ≠ 0` (TeX line 3464, "exhausting the components");
* constancy of `V_x² - μ V²` through the fundamental theorem of calculus for
  absolutely continuous functions (TeX lines 3465–3469), constancy of `V`
  from the extremum argument (TeX lines 3470–3472), and `W = c`,
  `V = ν c/μ` with `c ≥ 0` (TeX line 3474).
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.SpikeLimit

open Set Filter Topology MeasureTheory
open scoped Interval

/-! ### Real-sequence steps -/

/-- **Lemma 5.1, TeX line 3458.** If `χ_n k a_n ≤ C` eventually, with
`a_n ≥ 0`, `k > 0` and `χ_n → ∞`, then `a_n → 0`. -/
theorem tendsto_zero_of_mul_le {chi a : ℕ → ℝ} {k C : ℝ} (hk : 0 < k)
    (hchi : Tendsto chi atTop atTop) (ha : ∀ n, 0 ≤ a n)
    (hle : ∀ᶠ n in atTop, chi n * k * a n ≤ C) :
    Tendsto a atTop (𝓝 0) := by
  have hden : Tendsto (fun n => chi n * k) atTop atTop := hchi.atTop_mul_const hk
  have hlim : Tendsto (fun n => C / (chi n * k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall ha) ?_
  filter_upwards [hle, hden.eventually_gt_atTop 0] with n hn hpos
  rw [le_div_iff₀ hpos]
  linarith

/-- The pointwise three-term bound replacing Hölder–Chebyshev in TeX
lines 3459–3462: for `0 < γ < r`, `m > 0`, `ε, η > 0` there is `C ≥ 0` with
`t^γ ≤ ε^γ + η t^r + C t^m` for all `t ≥ 0`. -/
theorem rpow_le_three_term {gamma m r ε η : ℝ} (hγ : 0 < gamma) (hγr : gamma < r)
    (hm : 0 < m) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ^ gamma ≤ ε ^ gamma + η * t ^ r + C * t ^ m := by
  set T : ℝ := max ε (η ^ (-(r - gamma)⁻¹)) with hT_def
  have hT : 0 < T := lt_max_of_lt_left hε
  have hTε : ε ≤ T := le_max_left _ _
  have hrg : 0 < r - gamma := sub_pos.mpr hγr
  refine ⟨T ^ gamma / ε ^ m, div_nonneg (Real.rpow_nonneg hT.le _)
    (Real.rpow_nonneg hε.le _), fun t ht => ?_⟩
  have h1 : 0 ≤ ε ^ gamma := Real.rpow_nonneg hε.le _
  have h2 : 0 ≤ η * t ^ r := mul_nonneg hη.le (Real.rpow_nonneg ht _)
  have h3 : 0 ≤ T ^ gamma / ε ^ m * t ^ m :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg hε.le _))
      (Real.rpow_nonneg ht _)
  rcases le_or_gt t ε with htε | htε
  · have := Real.rpow_le_rpow ht htε hγ.le
    linarith
  have htpos : 0 < t := hε.trans htε
  rcases le_or_gt T t with hTt | hTt
  · -- large `t`: `t^γ ≤ η t^r`
    have hbig : η ^ (-(r - gamma)⁻¹) ≤ t := (le_max_right _ _).trans hTt
    have hpow : (η ^ (-(r - gamma)⁻¹)) ^ (r - gamma) ≤ t ^ (r - gamma) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hη.le _) hbig hrg.le
    rw [← Real.rpow_mul hη.le, neg_mul, inv_mul_cancel₀ hrg.ne', Real.rpow_neg_one] at hpow
    have hsplit : t ^ r = t ^ gamma * t ^ (r - gamma) := by
      rw [← Real.rpow_add htpos]; ring_nf
    have hge : 1 ≤ η * t ^ (r - gamma) := by
      rw [← inv_mul_cancel₀ hη.ne', mul_comm η⁻¹ η]
      exact mul_le_mul_of_nonneg_left hpow hη.le
    have hγpos : 0 ≤ t ^ gamma := Real.rpow_nonneg ht _
    have : t ^ gamma ≤ η * t ^ r := by
      rw [hsplit]
      nlinarith
    linarith
  · -- middle range `ε < t < T`: `t^γ ≤ T^γ ≤ (T^γ/ε^m) t^m`
    have hle : t ^ gamma ≤ T ^ gamma := Real.rpow_le_rpow ht hTt.le hγ.le
    have hεm : 0 < ε ^ m := Real.rpow_pos_of_pos hε _
    have hmono : ε ^ m ≤ t ^ m := Real.rpow_le_rpow hε.le htε.le hm.le
    have : T ^ gamma ≤ T ^ gamma / ε ^ m * t ^ m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hεm]
      exact mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hT.le _)
    linarith

/-- **Lemma 5.1, TeX lines 3459–3463.** On an interval `[p,q]`, nonnegative
continuous `u_n` with `∫_p^q u_n^r ≤ R` and `∫_p^q u_n^m → 0` satisfy
`∫_p^q u_n^γ → 0` for `0 < γ < r`, `m > 0`. -/
theorem tendsto_integral_rpow_zero {p q gamma m r R : ℝ} (hpq : p ≤ q) (u : ℕ → ℝ → ℝ)
    (hγ : 0 < gamma) (hγr : gamma < r) (hm : 0 < m)
    (hcont : ∀ n, ContinuousOn (u n) (Icc p q)) (hnonneg : ∀ n, ∀ x ∈ Icc p q, 0 ≤ u n x)
    (hR : ∀ n, ∫ x in p..q, u n x ^ r ≤ R)
    (hm0 : Tendsto (fun n => ∫ x in p..q, u n x ^ m) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in p..q, u n x ^ gamma) atTop (𝓝 0) := by
  have hr : 0 < r := hγ.trans hγr
  have hcpow : ∀ n (s : ℝ), 0 ≤ s → IntervalIntegrable (fun x => u n x ^ s) volume p q :=
    fun n s hs => ((hcont n).rpow_const fun _ _ => Or.inr hs).intervalIntegrable_of_Icc hpq
  have hγnonneg : ∀ n, 0 ≤ ∫ x in p..q, u n x ^ gamma := fun n =>
    intervalIntegral.integral_nonneg hpq fun x hx => Real.rpow_nonneg (hnonneg n x hx) _
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε : ℝ := (δ / (3 * (q - p + 1))) ^ gamma⁻¹ with hε_def
  have hqp : 0 < q - p + 1 := by linarith
  have hbase : 0 < δ / (3 * (q - p + 1)) := by positivity
  have hε : 0 < ε := Real.rpow_pos_of_pos hbase _
  have hεγ : ε ^ gamma = δ / (3 * (q - p + 1)) := by
    rw [hε_def, Real.rpow_inv_rpow hbase.le hγ.ne']
  set η : ℝ := δ / (3 * (|R| + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨C, hC0, hCbd⟩ := rpow_le_three_term hγ hγr hm hε hη
  have hCm : Tendsto (fun n => C * ∫ x in p..q, u n x ^ m) atTop (𝓝 0) := by
    simpa using hm0.const_mul C
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hCm) (δ / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbound : ∫ x in p..q, u n x ^ gamma ≤
      ∫ x in p..q, (ε ^ gamma + η * u n x ^ r + C * u n x ^ m) :=
    intervalIntegral.integral_mono_on hpq (hcpow n gamma hγ.le)
      (((intervalIntegrable_const).add ((hcpow n r hr.le).const_mul η)).add
        ((hcpow n m hm.le).const_mul C))
      fun x hx => hCbd _ (hnonneg n x hx)
  rw [intervalIntegral.integral_add ((intervalIntegrable_const).add
      ((hcpow n r hr.le).const_mul η)) ((hcpow n m hm.le).const_mul C),
    intervalIntegral.integral_add intervalIntegrable_const ((hcpow n r hr.le).const_mul η),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, smul_eq_mul] at hbound
  have hNn := hN n hn
  rw [Real.dist_eq, sub_zero] at hNn ⊢
  rw [abs_of_nonneg (hγnonneg n)]
  have hA : (q - p) * ε ^ gamma < δ / 3 := by
    rw [hεγ, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hB : η * ∫ x in p..q, u n x ^ r < δ / 3 := by
    have hRle : ∫ x in p..q, u n x ^ r ≤ |R| := (hR n).trans (le_abs_self R)
    have : η * ∫ x in p..q, u n x ^ r ≤ η * |R| := mul_le_mul_of_nonneg_left hRle hη.le
    have h2 : η * |R| < δ / 3 := by
      rw [hη_def, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg R]
    linarith
  have hCle : C * ∫ x in p..q, u n x ^ m < δ / 3 := lt_of_abs_lt hNn
  linarith

/-- **Lemma 5.1, TeX line 3434.** A uniform bound `0 ≤ v ≤ B` gives the
uniform lower bound `(1+v)^{-β} ≥ κ := (1+B)^{-β} > 0` for `β ≥ 0`. -/
theorem kappa_le_of_le {beta B v : ℝ} (hbeta : 0 ≤ beta) (hv0 : 0 ≤ v) (hvB : v ≤ B) :
    0 < 1 / (1 + B) ^ beta ∧ 1 / (1 + B) ^ beta ≤ 1 / (1 + v) ^ beta := by
  have hv1 : 0 < 1 + v := by linarith
  have hB1 : 0 < 1 + B := by linarith
  exact ⟨one_div_pos.mpr (Real.rpow_pos_of_pos hB1 _),
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hv1 _)
      (Real.rpow_le_rpow hv1.le (by linarith) hbeta)⟩

/-! ### The test-function estimate (TeX lines 3446–3457) -/

/-- **Lemma 5.1, TeX lines 3453–3457.** Let `u ≥ 0` be `C¹` on `[0,L]` and
satisfy the first integral `u_x = χ u^m/(1+v)^β v_x - F` (`E:un-eq`). Let
`φ` be `C¹` with `φ(0) = φ(L) = 0`, `φ ≥ 0` on `[0,L]`, `φ = 1` on
`J = [p,q] ⊆ [0,L]`, and suppose `s v_x ≥ σ > 0` wherever `φ ≠ 0`, with
`|s| = 1`, and `(1+v)^{-β} ≥ κ > 0`. Then, for `χ ≥ 0`,
`χ κ σ ∫_J u^m ≤ |∫_0^L u φ_x| + |∫_0^L F φ|`. -/
theorem flux_test_bound {L p q chi m beta kappa sigma s : ℝ} {u du v dv F phi dphi : ℝ → ℝ}
    (hL : 0 ≤ L) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ L) (hchi : 0 ≤ chi) (hm : 0 < m)
    (hs : |s| = 1) (hkappa : 0 < kappa) (hsigma : 0 < sigma)
    (hu : ContinuousOn u (Icc 0 L)) (hu0 : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x) (hdu_cont : ContinuousOn du (Icc 0 L))
    (hv : ContinuousOn v (Icc 0 L)) (hv0 : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hdv : ContinuousOn dv (Icc 0 L)) (hF : ContinuousOn F (Icc 0 L))
    (hphi : ∀ x, HasDerivAt phi (dphi x) x) (hdphi : Continuous dphi)
    (hphi0 : phi 0 = 0) (hphiL : phi L = 0) (hphi_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ phi x)
    (hphi_one : ∀ x ∈ Icc p q, phi x = 1)
    (hflux : ∀ x ∈ Icc 0 L, du x = chi * (u x ^ m / (1 + v x) ^ beta * dv x) - F x)
    (hkappa_le : ∀ x ∈ Icc 0 L, kappa ≤ 1 / (1 + v x) ^ beta)
    (hsign : ∀ x ∈ Icc 0 L, phi x ≠ 0 → sigma ≤ s * dv x) :
    chi * kappa * sigma * ∫ x in p..q, u x ^ m ≤
      |∫ x in (0 : ℝ)..L, u x * dphi x| + |∫ x in (0 : ℝ)..L, F x * phi x| := by
  have hphic : Continuous phi := continuous_iff_continuousAt.mpr fun x => (hphi x).continuousAt
  have hIcc : uIcc (0 : ℝ) L = Icc 0 L := uIcc_of_le hL
  have hv1 : ∀ x ∈ Icc 0 L, 0 < 1 + v x := fun x hx => by linarith [hv0 x hx]
  -- the chemotactic factor `G = u^m/(1+v)^β v_x`
  set G : ℝ → ℝ := fun x => u x ^ m / (1 + v x) ^ beta * dv x with hG_def
  have hGc : ContinuousOn G (Icc 0 L) := by
    refine ContinuousOn.mul (ContinuousOn.div (hu.rpow_const fun _ _ => Or.inr hm.le)
      ((continuousOn_const.add hv).rpow_const fun x hx => Or.inl (hv1 x hx).ne') ?_) hdv
    intro x hx; exact (Real.rpow_pos_of_pos (hv1 x hx) _).ne'
  -- integration by parts: `∫ u φ' = - ∫ u' φ`
  have hibp : ∫ x in (0 : ℝ)..L, u x * dphi x = -∫ x in (0 : ℝ)..L, du x * phi x := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := u) (v := phi) (u' := du) (v' := dphi) (a := 0) (b := L)
      (by rw [hIcc]; exact hu) hphic.continuousOn
      (fun x hx => by
        rw [min_eq_left hL, max_eq_right hL] at hx; exact hdu x hx)
      (fun x _ => hphi x)
      (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL]
          exact hdu_cont.integrableOn_Icc)
      (hdphi.intervalIntegrable 0 L)
    rw [h, hphi0, hphiL]; ring
  -- the first integral tested against `φ`
  have hsplit : ∫ x in (0 : ℝ)..L, du x * phi x =
      chi * (∫ x in (0 : ℝ)..L, G x * phi x) - ∫ x in (0 : ℝ)..L, F x * phi x := by
    have hGi : IntervalIntegrable (fun x => G x * phi x) volume 0 L :=
      (hGc.mul hphic.continuousOn).intervalIntegrable_of_Icc hL
    have hFi : IntervalIntegrable (fun x => F x * phi x) volume 0 L :=
      (hF.mul hphic.continuousOn).intervalIntegrable_of_Icc hL
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hGi.const_mul chi) hFi]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [hIcc] at hx
    simp only [hflux x hx, hG_def]; ring
  have hkey : chi * (∫ x in (0 : ℝ)..L, G x * phi x) =
      -(∫ x in (0 : ℝ)..L, u x * dphi x) + ∫ x in (0 : ℝ)..L, F x * phi x := by
    linarith
  -- pointwise facts for `s G φ`
  have hnn : ∀ x ∈ Icc 0 L, 0 ≤ s * G x * phi x := by
    intro x hx
    by_cases h0 : phi x = 0
    · rw [h0, mul_zero]
    have hsd := hsign x hx h0
    have hk := hkappa_le x hx
    have : s * G x * phi x = u x ^ m * (1 / (1 + v x) ^ beta) * (s * dv x) * phi x := by
      simp only [hG_def]; ring
    rw [this]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (hu0 x hx) _)
      (hkappa.le.trans hk)) (hsigma.le.trans hsd)) (hphi_nonneg x hx)
  have hJlow : ∀ x ∈ Icc p q, kappa * sigma * u x ^ m ≤ s * G x * phi x := by
    intro x hx
    have hx' : x ∈ Icc 0 L := ⟨hp.trans hx.1, hx.2.trans hq⟩
    have h1 := hphi_one x hx
    have hsd := hsign x hx' (by rw [h1]; exact one_ne_zero)
    have hk := hkappa_le x hx'
    have : s * G x * phi x = u x ^ m * (1 / (1 + v x) ^ beta) * (s * dv x) := by
      simp only [hG_def, h1]; ring
    rw [this]
    have hum := Real.rpow_nonneg (hu0 x hx') m
    have := mul_le_mul hk hsd hsigma.le (hkappa.le.trans hk)
    nlinarith
  have hsGc : ContinuousOn (fun x => s * G x * phi x) (Icc 0 L) :=
    (continuousOn_const.mul hGc).mul hphic.continuousOn
  have hJsub : Icc p q ⊆ Icc 0 L := Icc_subset_Icc hp hq
  have hmono1 : ∫ x in p..q, kappa * sigma * u x ^ m ≤ ∫ x in p..q, s * G x * phi x :=
    intervalIntegral.integral_mono_on hpq
      (((hu.mono hJsub).rpow_const fun _ _ => Or.inr hm.le).intervalIntegrable_of_Icc hpq
        |>.const_mul _)
      ((hsGc.mono hJsub).intervalIntegrable_of_Icc hpq) hJlow
  have hmono2 : ∫ x in p..q, s * G x * phi x ≤ ∫ x in (0 : ℝ)..L, s * G x * phi x := by
    refine intervalIntegral.integral_mono_interval hp hpq hq ?_
      (hsGc.intervalIntegrable_of_Icc hL)
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Eventually.of_forall fun x hx => hnn x (Ioc_subset_Icc_self hx))
  have hpull : ∫ x in (0 : ℝ)..L, s * G x * phi x = s * ∫ x in (0 : ℝ)..L, G x * phi x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [intervalIntegral.integral_const_mul] at hmono1
  have hchain : kappa * sigma * ∫ x in p..q, u x ^ m ≤ s * ∫ x in (0 : ℝ)..L, G x * phi x := by
    rw [← hpull]; exact hmono1.trans hmono2
  have hmul := mul_le_mul_of_nonneg_left hchain hchi
  have hrhs : chi * (s * ∫ x in (0 : ℝ)..L, G x * phi x) =
      s * (-(∫ x in (0 : ℝ)..L, u x * dphi x) + ∫ x in (0 : ℝ)..L, F x * phi x) := by
    rw [← hkey]; ring
  have habs : s * (-(∫ x in (0 : ℝ)..L, u x * dphi x) + ∫ x in (0 : ℝ)..L, F x * phi x) ≤
      |∫ x in (0 : ℝ)..L, u x * dphi x| + |∫ x in (0 : ℝ)..L, F x * phi x| := by
    calc _ ≤ |s * (-(∫ x in (0 : ℝ)..L, u x * dphi x) + ∫ x in (0 : ℝ)..L, F x * phi x)| :=
          le_abs_self _
      _ = |-(∫ x in (0 : ℝ)..L, u x * dphi x) + ∫ x in (0 : ℝ)..L, F x * phi x| := by
          rw [abs_mul, hs, one_mul]
      _ ≤ _ := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg]
  calc chi * kappa * sigma * ∫ x in p..q, u x ^ m
      = chi * (kappa * sigma * ∫ x in p..q, u x ^ m) := by ring
    _ ≤ _ := hmul
    _ = _ := hrhs
    _ ≤ _ := habs

/-! ### The limiting signal profile is constant (TeX lines 3464–3474) -/

/-- At a minimum or maximum point of `V` on `[0,L]`, `V_x = 0`: in the
interior by Fermat's theorem, at the endpoints by the Neumann data
(TeX line 3471, "including the Neumann endpoints"). -/
theorem deriv_eq_zero_of_extremum {L : ℝ} {V dV : ℝ → ℝ}
    (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x) (hbc0 : dV 0 = 0) (hbcL : dV L = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc 0 L) (hext : IsMinOn V (Icc 0 L) x₀ ∨ IsMaxOn V (Icc 0 L) x₀) :
    dV x₀ = 0 := by
  rcases eq_or_lt_of_le hx₀.1 with h0 | h0
  · rw [← h0]; exact hbc0
  rcases eq_or_lt_of_le hx₀.2 with hL | hL
  · rw [hL]; exact hbcL
  have hnhds : Icc 0 L ∈ 𝓝 x₀ := Icc_mem_nhds h0 hL
  rcases hext with hmin | hmax
  · exact (hmin.isLocalMin hnhds).hasDerivAt_eq_zero (hdV x₀ ⟨h0, hL⟩)
  · exact (hmax.isLocalMax hnhds).hasDerivAt_eq_zero (hdV x₀ ⟨h0, hL⟩)

/-- **Lemma 5.1, TeX lines 3470–3473.** If `V ≥ 0` on `[0,L]`, `μ > 0`,
`V_x(0) = V_x(L) = 0` and `V_x² - μ V²` is constant on `[0,L]`, then `V` is
constant: at the extrema `V_x = 0`, so `(min V)² = (max V)²`. -/
theorem eq_const_of_energy {L mu : ℝ} {V dV : ℝ → ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (hV : ContinuousOn V (Icc 0 L)) (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x)
    (hV0 : ∀ x ∈ Icc 0 L, 0 ≤ V x) (hbc0 : dV 0 = 0) (hbcL : dV L = 0)
    (hE : ∃ E, ∀ x ∈ Icc 0 L, dV x ^ 2 - mu * V x ^ 2 = E) :
    ∀ x ∈ Icc 0 L, V x = V 0 := by
  obtain ⟨E, hE⟩ := hE
  have hne : (Icc (0 : ℝ) L).Nonempty := nonempty_Icc.mpr hL.le
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hV
  obtain ⟨x₁, hx₁, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hV
  have h0 := hE x₀ hx₀
  have h1 := hE x₁ hx₁
  rw [deriv_eq_zero_of_extremum hdV hbc0 hbcL hx₀ (Or.inl hmin)] at h0
  rw [deriv_eq_zero_of_extremum hdV hbc0 hbcL hx₁ (Or.inr hmax)] at h1
  have hsq : V x₀ ^ 2 = V x₁ ^ 2 := by
    have : mu * V x₀ ^ 2 = mu * V x₁ ^ 2 := by linarith
    exact mul_left_cancel₀ hmu.ne' this
  have ha := hV0 x₀ hx₀
  have hb := hV0 x₁ hx₁
  have hle : V x₀ ≤ V x₁ := hmin hx₁
  have heq : V x₀ = V x₁ := by nlinarith
  have hconst : ∀ x ∈ Icc 0 L, V x = V x₀ := fun x hx =>
    le_antisymm (heq ▸ hmax hx) (hmin hx)
  intro x hx
  rw [hconst x hx, hconst 0 (left_mem_Icc.mpr hL.le)]

/-- **Lemma 5.1, TeX lines 3465–3469.** Let `V` be `C¹` on `[0,L]` and let
`V_x` satisfy the integrated limiting equation `V_x(x) = ∫_0^x (μ V - ν W)`
(`E:lm2-v-limit` with `V_x(0) = 0`), `W ∈ L¹(0,L)`. If `W V_x = 0` a.e.,
then `V_x² - μ V²` is constant on `[0,L]`. The function `V_x² - μ V²` is
absolutely continuous and has derivative `-2ν W V_x = 0` a.e. -/
theorem energy_const {L mu nu : ℝ} {V dV W : ℝ → ℝ} (hL : 0 ≤ L)
    (hV : ContinuousOn V (Icc 0 L)) (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x)
    (hdV_cont : ContinuousOn dV (Icc 0 L)) (hW : IntervalIntegrable W volume 0 L)
    (heq : ∀ x ∈ Icc 0 L, dV x = ∫ y in (0 : ℝ)..x, (mu * V y - nu * W y))
    (hWdV : ∀ᵐ x, x ∈ Ioo 0 L → W x * dV x = 0) :
    ∃ E, ∀ x ∈ Icc 0 L, dV x ^ 2 - mu * V x ^ 2 = E := by
  have hIcc : uIcc (0 : ℝ) L = Icc 0 L := uIcc_of_le hL
  set g : ℝ → ℝ := fun y => mu * V y - nu * W y with hg_def
  have hg : IntervalIntegrable g volume 0 L :=
    ((hV.intervalIntegrable_of_Icc hL).const_mul mu).sub (hW.const_mul nu)
  set P : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, g y with hP_def
  have hPac : AbsolutelyContinuousOnInterval P 0 L :=
    hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hdVi : IntervalIntegrable dV volume 0 L := hdV_cont.intervalIntegrable_of_Icc hL
  set Q : ℝ → ℝ := fun x => V 0 + ∫ y in (0 : ℝ)..x, dV y with hQ_def
  have hQac : AbsolutelyContinuousOnInterval Q 0 L :=
    ((LipschitzWith.const (V 0)).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (hdVi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hQV : ∀ x ∈ Icc 0 L, Q x = V x := by
    intro x hx
    have hsub : Icc 0 x ⊆ Icc 0 L := Icc_subset_Icc le_rfl hx.2
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 (hV.mono hsub)
      (fun y hy => hdV y ⟨hy.1, hy.2.trans_le hx.2⟩)
      (hdVi.mono_set (by rw [hIcc, uIcc_of_le hx.1]; exact hsub))
    simp only [hQ_def, h]; ring
  have hPdV : ∀ x ∈ Icc 0 L, P x = dV x := fun x hx => (heq x hx).symm
  set E : ℝ → ℝ := fun x => P x * P x - mu * (Q x * Q x) with hE_def
  have hEac : AbsolutelyContinuousOnInterval E 0 L :=
    (hPac.fun_mul hPac).sub ((hQac.fun_mul hQac).const_mul mu)
  have hPder := hg.ae_hasDerivAt_integral
  have hne0 : ∀ᵐ x, x ≠ (0 : ℝ) := by simp [ae_iff, measure_singleton]
  have hneL : ∀ᵐ x, x ≠ L := by simp [ae_iff, measure_singleton]
  have hE0 : ∀ᵐ x, x ∈ uIcc 0 L → HasDerivAt E 0 x := by
    filter_upwards [hPder, hWdV, hne0, hneL] with x hP hWx hx0 hxL hx
    have hx' : x ∈ Icc 0 L := by rw [← hIcc]; exact hx
    have hxI : x ∈ Ioo 0 L := ⟨lt_of_le_of_ne hx'.1 (Ne.symm hx0), lt_of_le_of_ne hx'.2 hxL⟩
    have hPx : HasDerivAt P (g x) x := hP hx 0 left_mem_uIcc
    have hQx : HasDerivAt Q (dV x) x := by
      refine (hdV x hxI).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
      exact hQV y (Ioo_subset_Icc_self hy)
    have hd := (hPx.mul hPx).sub ((hQx.mul hQx).const_mul mu)
    convert hd using 1
    rw [hPdV x hx', hQV x hx', hg_def]
    have := hWx hxI
    linear_combination (2 * nu) * this
  obtain ⟨C, hC⟩ := hEac.const_of_ae_hasDerivAt_zero hE0
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x (by rw [hIcc]; exact hx)
  simp only [hE_def, hPdV x hx, hQV x hx] at h
  rw [← h]; ring

/-- **Lemma 5.1, TeX lines 3464–3474: the limit is constant.** Let `μ, ν > 0`,
let `V ≥ 0` be `C¹` on `[0,L]` with `V_x(L) = 0`, let `W ∈ L¹(0,L)`, and let
the integrated limiting equation `V_x(x) = ∫_0^x (μ V - ν W)` hold on `[0,L]`
(`E:lm2-v-limit`). If `W V_x = 0` a.e. on `(0,L)`, then there is `c ≥ 0`
with `V = (ν/μ) c` on `[0,L]` and `W = c` a.e. on `[0,L]`. -/
theorem limit_eq_const {L mu nu : ℝ} {V dV W : ℝ → ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (hnu : 0 < nu) (hV : ContinuousOn V (Icc 0 L))
    (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x) (hdV_cont : ContinuousOn dV (Icc 0 L))
    (hV0 : ∀ x ∈ Icc 0 L, 0 ≤ V x) (hW : IntervalIntegrable W volume 0 L)
    (heq : ∀ x ∈ Icc 0 L, dV x = ∫ y in (0 : ℝ)..x, (mu * V y - nu * W y))
    (hbcL : dV L = 0) (hWdV : ∀ᵐ x, x ∈ Ioo 0 L → W x * dV x = 0) :
    ∃ c, 0 ≤ c ∧ (∀ x ∈ Icc 0 L, V x = nu / mu * c) ∧ ∀ᵐ x, x ∈ Icc 0 L → W x = c := by
  have h0mem : (0 : ℝ) ∈ Icc 0 L := left_mem_Icc.mpr hL.le
  have hbc0 : dV 0 = 0 := by rw [heq 0 h0mem, intervalIntegral.integral_same]
  have hconst := eq_const_of_energy hL hmu hV hdV hV0 hbc0 hbcL
    (energy_const hL.le hV hdV hdV_cont hW heq hWdV)
  -- `V_x = 0` on `(0,L)`
  have hdV0 : ∀ x ∈ Ioo 0 L, dV x = 0 := by
    intro x hx
    have h1 : HasDerivAt V 0 x := by
      refine (hasDerivAt_const x (V 0)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hconst y (Ioo_subset_Icc_self hy)
    exact (hdV x hx).unique h1
  have hP0 : ∀ x ∈ Icc 0 L, ∫ y in (0 : ℝ)..x, (mu * V y - nu * W y) = 0 := by
    intro x hx
    rw [← heq x hx]
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hbc0
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · rw [h']; exact hbcL
    exact hdV0 x ⟨h, h'⟩
  have hg : IntervalIntegrable (fun y => mu * V y - nu * W y) volume 0 L :=
    ((hV.intervalIntegrable_of_Icc hL.le).const_mul mu).sub (hW.const_mul nu)
  refine ⟨mu * V 0 / nu, div_nonneg (mul_nonneg hmu.le (hV0 0 h0mem)) hnu.le, ?_, ?_⟩
  · intro x hx
    rw [hconst x hx]; field_simp
  have hne0 : ∀ᵐ x, x ≠ (0 : ℝ) := by simp [ae_iff, measure_singleton]
  have hneL : ∀ᵐ x, x ≠ L := by simp [ae_iff, measure_singleton]
  filter_upwards [hg.ae_hasDerivAt_integral, hne0, hneL] with x hP hx0 hxL hx
  have hxI : x ∈ Ioo 0 L := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hxL⟩
  have hd := hP (by rw [uIcc_of_le hL.le]; exact hx) 0 left_mem_uIcc
  have hz : HasDerivAt (fun x => ∫ y in (0 : ℝ)..x, (mu * V y - nu * W y)) 0 x := by
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
    exact hP0 y (Ioo_subset_Icc_self hy)
  have hzero : mu * V x - nu * W x = 0 := hd.unique hz
  rw [hconst x hx] at hzero
  field_simp
  linarith

/-! ### Vanishing of the weak limit where `V_x ≠ 0` (TeX lines 3446–3464) -/

/-- **Lemma 5.1, TeX line 3464, "exhausting the components".** If `W = 0`
a.e. on every `[p',q']` with `[p',q'] ⊂ (p,q)`, `[p,q] ⊂ (0,L)` and
`V_x ≠ 0` on `[p,q]`, then `W V_x = 0` a.e. on `(0,L)`. -/
theorem ae_mul_eq_zero_of_intervals {L : ℝ} {W dV : ℝ → ℝ} (hdV : ContinuousOn dV (Icc 0 L))
    (hJ : ∀ p q : ℝ, 0 < p → p < q → q < L → (∀ x ∈ Icc p q, dV x ≠ 0) →
      ∀ p' q' : ℝ, p < p' → p' < q' → q' < q → ∀ᵐ x, x ∈ Icc p' q' → W x = 0) :
    ∀ᵐ x, x ∈ Ioo 0 L → W x * dV x = 0 := by
  have hall : ∀ᵐ x, ∀ i : ℚ × ℚ × ℚ × ℚ,
      (0 < (i.1 : ℝ) ∧ (i.1 : ℝ) < i.2.1 ∧ (i.2.1 : ℝ) < i.2.2.1 ∧ (i.2.2.1 : ℝ) < i.2.2.2 ∧
        (i.2.2.2 : ℝ) < L ∧ ∀ y ∈ Icc (i.1 : ℝ) i.2.2.2, dV y ≠ 0) →
      x ∈ Icc (i.2.1 : ℝ) i.2.2.1 → W x = 0 := by
    rw [ae_all_iff]
    rintro ⟨p, p', q', q⟩
    by_cases hc : 0 < (p : ℝ) ∧ (p : ℝ) < p' ∧ (p' : ℝ) < q' ∧ (q' : ℝ) < q ∧ (q : ℝ) < L ∧
        ∀ y ∈ Icc (p : ℝ) q, dV y ≠ 0
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
      filter_upwards [hJ p q h1 (by linarith) h5 h6 p' q' h2 h3 h4] with x hx _
      exact hx
    · exact Eventually.of_forall fun x h => absurd h hc
  filter_upwards [hall] with x hx hxI
  by_cases h0 : dV x = 0
  · rw [h0, mul_zero]
  have hcont : ContinuousAt dV x := hdV.continuousAt (Icc_mem_nhds hxI.1 hxI.2)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne h0)
  set ρ : ℝ := min ε (min x (L - x)) with hρ_def
  have hρ : 0 < ρ := lt_min hε (lt_min hxI.1 (by linarith [hxI.2]))
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρx : ρ ≤ x := (min_le_right _ _).trans (min_le_left _ _)
  have hρL : ρ ≤ L - x := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show x - ρ < x - ρ / 2 by linarith)
  obtain ⟨p', hp'1, hp'2⟩ := exists_rat_btwn (show (p : ℝ) < x by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x + ρ / 2 < x + ρ by linarith)
  obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn (show x < (q : ℝ) by linarith)
  have hW := hx (p, p', q', q) ⟨by linarith, hp'1, by linarith, hq'2, by linarith,
    fun y hy => hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2])⟩
    ⟨hp'2.le, hq'1.le⟩
  rw [hW, zero_mul]

/-- A sign for a continuous function without zeros on `[p,q]`: there is
`s = ±1` with `s f > 0` on `[p,q]` (intermediate value theorem). -/
theorem exists_sign_pos {p q : ℝ} {f : ℝ → ℝ} (hpq : p ≤ q) (hf : ContinuousOn f (Icc p q))
    (hne : ∀ x ∈ Icc p q, f x ≠ 0) : ∃ s : ℝ, |s| = 1 ∧ ∀ x ∈ Icc p q, 0 < s * f x := by
  have hpmem : p ∈ Icc p q := left_mem_Icc.mpr hpq
  rcases lt_or_gt_of_ne (hne p hpmem) with hneg | hpos
  · refine ⟨-1, by norm_num, fun x hx => ?_⟩
    by_contra hle
    have hfx : 0 ≤ f x := by linarith
    obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hx.1 (hf.mono (Icc_subset_Icc le_rfl hx.2))
      ⟨hneg.le, hfx⟩
    exact hne y ⟨hy.1, hy.2.trans hx.2⟩ hfy
  · refine ⟨1, by norm_num, fun x hx => ?_⟩
    by_contra hle
    have hfx : f x ≤ 0 := by linarith
    obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc' hx.1
      (hf.mono (Icc_subset_Icc le_rfl hx.2)) ⟨hfx, hpos.le⟩
    exact hne y ⟨hy.1, hy.2.trans hx.2⟩ hfy

/-- **Lemma 5.1, TeX lines 3446–3463: `W = 0` where `V_x ≠ 0`.** Let
`[p,q] ⊂ (0,L)` with `V_x ≠ 0` on `[p,q]`, and `p < p' < q' < q`. Along a
sequence with `χ_n → ∞`, assume for each `n` the first integral
`(u_n)_x = χ_n u_n^m/(1+v_n)^β (v_n)_x - F_n` on `[0,L]` (`E:un-eq`) with
`|F_n| ≤ F_b`, `(1+v_n)^{-β} ≥ κ > 0`, `u_n ≥ 0`, `∫_0^L u_n ≤ M`,
`∫_0^L u_n^r ≤ R`, and the analytic inputs `(v_n)_x → V_x` uniformly on
`[0,L]` and `∫_{p'}^{q'} u_n^γ → ∫_{p'}^{q'} W`. If `0 < γ < r`, `m > 0`
and `W ≥ 0`, then `W = 0` a.e. on `[p',q']`. The test function is a smooth
bump equal to one on `[p',q']` and supported in `[p,q]`. -/
theorem weakLimit_ae_zero {L p q p' q' gamma m r beta kappa M Fb R : ℝ}
    {chi : ℕ → ℝ} {u du v dv F : ℕ → ℝ → ℝ} {dV W : ℝ → ℝ}
    (hp : 0 < p) (hpp : p < p') (hpq : p' < q') (hqq : q' < q) (hq : q < L)
    (hγ : 0 < gamma) (hγr : gamma < r) (hm : 0 < m) (hkappa : 0 < kappa)
    (hchi : Tendsto chi atTop atTop)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hdu : ∀ n, ∀ x ∈ Ioo 0 L, HasDerivAt (u n) (du n x) x)
    (hdu_cont : ∀ n, ContinuousOn (du n) (Icc 0 L))
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L)) (hv0 : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ v n x)
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L)) (hF : ∀ n, ContinuousOn (F n) (Icc 0 L))
    (hflux : ∀ n, ∀ x ∈ Icc 0 L,
      du n x = chi n * (u n x ^ m / (1 + v n x) ^ beta * dv n x) - F n x)
    (hFb : ∀ n, ∀ x ∈ Icc 0 L, |F n x| ≤ Fb)
    (hkappa_le : ∀ n, ∀ x ∈ Icc 0 L, kappa ≤ 1 / (1 + v n x) ^ beta)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x ≤ M)
    (hR : ∀ n, ∫ x in (0 : ℝ)..L, u n x ^ r ≤ R)
    (hdvconv : TendstoUniformlyOn dv dV atTop (Icc 0 L))
    (hdV_cont : ContinuousOn dV (Icc 0 L)) (hdV_ne : ∀ x ∈ Icc p q, dV x ≠ 0)
    (hweak : Tendsto (fun n => ∫ x in p'..q', u n x ^ gamma) atTop (𝓝 (∫ x in p'..q', W x)))
    (hW : IntervalIntegrable W volume p' q') (hW0 : ∀ᵐ x, x ∈ Icc p' q' → 0 ≤ W x) :
    ∀ᵐ x, x ∈ Icc p' q' → W x = 0 := by
  have hL : 0 < L := by linarith
  have hpqI : Icc p q ⊆ Icc 0 L := Icc_subset_Icc hp.le hq.le
  -- the sign of `V_x` on `[p,q]` and a uniform lower bound `σ₀`
  obtain ⟨s, hs, hspos⟩ := exists_sign_pos (by linarith) (hdV_cont.mono hpqI) hdV_ne
  obtain ⟨xm, hxm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by linarith))
    ((continuousOn_const.mul hdV_cont).mono hpqI : ContinuousOn (fun x => s * dV x) (Icc p q))
  set σ0 : ℝ := s * dV xm with hσ0_def
  have hσ0 : 0 < σ0 := hspos xm hxm
  -- eventually `s (v_n)_x ≥ σ₀/2` on `[p,q]`
  have hev : ∀ᶠ n in atTop, ∀ x ∈ Icc p q, σ0 / 2 ≤ s * dv n x := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hdvconv (σ0 / 2) (by linarith)] with n hn
    intro x hx
    have h1 := hn x (hpqI hx)
    rw [Real.dist_eq] at h1
    have h2 : σ0 ≤ s * dV x := hmin hx
    have h3 : |s * dv n x - s * dV x| < σ0 / 2 := by
      rw [← mul_sub, abs_mul, hs, one_mul, abs_sub_comm]; exact h1
    have := neg_abs_le (s * dv n x - s * dV x)
    linarith
  -- the test function: a smooth bump, one on `[p',q']`, supported in `(p,q)`
  set c0 : ℝ := (p' + q') / 2 with hc0
  set ρ : ℝ := min (p' - p) (q - q') with hρ_def
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  let bump : ContDiffBump c0 :=
    ⟨(q' - p') / 2, (q' - p') / 2 + ρ, by linarith, by linarith⟩
  set phi : ℝ → ℝ := fun x => bump x with hphi_def
  have hphi_cd : ContDiff ℝ 1 phi := bump.contDiff
  have hphi_der : ∀ x, HasDerivAt phi (deriv phi x) x := fun x =>
    ((hphi_cd.differentiable one_ne_zero) x).hasDerivAt
  have hdphi : Continuous (deriv phi) := hphi_cd.continuous_deriv le_rfl
  have hsupp : ∀ x, phi x ≠ 0 → x ∈ Icc p q := by
    intro x hx
    have hmem : x ∈ Function.support bump := hx
    rw [bump.support_eq, Real.ball_eq_Ioo] at hmem
    have h1 : ρ ≤ p' - p := min_le_left _ _
    have h2 : ρ ≤ q - q' := min_le_right _ _
    constructor
    · have := hmem.1; simp only [bump] at this; linarith
    · have := hmem.2; simp only [bump] at this; linarith
  have hphi_one : ∀ x ∈ Icc p' q', phi x = 1 := by
    intro x hx
    refine bump.one_of_mem_closedBall ?_
    rw [Real.closedBall_eq_Icc]
    simp only [bump]
    constructor <;> linarith [hx.1, hx.2]
  have hphi_zero : ∀ x, x ∉ Icc p q → phi x = 0 := fun x hx => by
    by_contra h; exact hx (hsupp x h)
  have hphi0 : phi 0 = 0 := hphi_zero 0 fun h => by linarith [h.1]
  have hphiL : phi L = 0 := hphi_zero L fun h => by linarith [h.2]
  have hphi_nonneg : ∀ x, 0 ≤ phi x := fun x => bump.nonneg
  have hphi_le : ∀ x, phi x ≤ 1 := fun x => bump.le_one
  -- a bound `D` for `|φ'|` on `[0,L]`
  obtain ⟨xD, -, hD⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hL.le)
    (hdphi.abs.continuousOn : ContinuousOn (fun x => |deriv phi x|) (Icc 0 L))
  set D : ℝ := |deriv phi xD|
  -- the right-hand side of the test-function estimate is bounded
  have hrhs : ∀ n, |∫ x in (0 : ℝ)..L, u n x * deriv phi x| +
      |∫ x in (0 : ℝ)..L, F n x * phi x| ≤ D * M + Fb * L := by
    intro n
    have h1 : |∫ x in (0 : ℝ)..L, u n x * deriv phi x| ≤ D * M := by
      refine (intervalIntegral.abs_integral_le_integral_abs hL.le).trans ?_
      have hle : ∫ x in (0 : ℝ)..L, |u n x * deriv phi x| ≤ ∫ x in (0 : ℝ)..L, D * u n x := by
        refine intervalIntegral.integral_mono_on hL.le
          (((hu n).mul hdphi.continuousOn).abs.intervalIntegrable_of_Icc hL.le)
          (((hu n).intervalIntegrable_of_Icc hL.le).const_mul D) fun x hx => ?_
        rw [abs_mul, abs_of_nonneg (hu0 n x hx), mul_comm]
        exact mul_le_mul_of_nonneg_right (hD hx) (hu0 n x hx)
      rw [intervalIntegral.integral_const_mul] at hle
      have hD0 : 0 ≤ D := abs_nonneg _
      exact hle.trans (mul_le_mul_of_nonneg_left (hmass n) hD0)
    have h2 : |∫ x in (0 : ℝ)..L, F n x * phi x| ≤ Fb * L := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L)
        (C := Fb) (f := fun x => F n x * phi x) (fun x hx => by
          rw [uIoc_of_le hL.le] at hx
          have hx' := Ioc_subset_Icc_self hx
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hphi_nonneg x)]
          calc |F n x| * phi x ≤ Fb * 1 :=
                mul_le_mul (hFb n x hx') (hphi_le x) (hphi_nonneg x)
                  ((abs_nonneg _).trans (hFb n x hx'))
            _ = Fb := mul_one _)
      rw [Real.norm_eq_abs, sub_zero, abs_of_pos hL] at this
      exact this
    linarith
  -- `∫_{p'}^{q'} u_n^m → 0`
  have hm0 : Tendsto (fun n => ∫ x in p'..q', u n x ^ m) atTop (𝓝 0) := by
    refine tendsto_zero_of_mul_le (C := D * M + Fb * L) (mul_pos hkappa (half_pos hσ0)) hchi
      (fun n => intervalIntegral.integral_nonneg hpq.le fun x hx =>
        Real.rpow_nonneg (hu0 n x ⟨by linarith [hx.1], by linarith [hx.2]⟩) _) ?_
    filter_upwards [hev, hchi.eventually_ge_atTop 0] with n hn hchin
    have h := flux_test_bound (p := p') (q := q') (s := s) (sigma := σ0 / 2) (kappa := kappa)
      (beta := beta) hL.le (by linarith) hpq.le (by linarith) hchin hm hs hkappa
      (half_pos hσ0) (hu n) (hu0 n) (hdu n) (hdu_cont n) (hv n) (hv0 n) (hdv n) (hF n)
      hphi_der hdphi hphi0 hphiL (fun x _ => hphi_nonneg x) hphi_one (hflux n) (hkappa_le n)
      (fun x _ hx => hn x (hsupp x hx))
    have := hrhs n
    calc chi n * (kappa * (σ0 / 2)) * ∫ x in p'..q', u n x ^ m
        = chi n * kappa * (σ0 / 2) * ∫ x in p'..q', u n x ^ m := by ring
      _ ≤ _ := h.trans this
  -- `∫_{p'}^{q'} u_n^γ → 0`
  have hsub : Icc p' q' ⊆ Icc 0 L := Icc_subset_Icc (by linarith) (by linarith)
  have hγ0 : Tendsto (fun n => ∫ x in p'..q', u n x ^ gamma) atTop (𝓝 0) := by
    refine tendsto_integral_rpow_zero (R := R) hpq.le u hγ hγr hm (fun n => (hu n).mono hsub)
      (fun n x hx => hu0 n x (hsub hx)) (fun n => ?_) hm0
    refine le_trans ?_ (hR n)
    refine intervalIntegral.integral_mono_interval (by linarith) hpq.le (by linarith) ?_
      (((hu n).rpow_const fun _ _ => Or.inr (hγ.trans hγr).le).intervalIntegrable_of_Icc hL.le)
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx =>
      Real.rpow_nonneg (hu0 n x (Ioc_subset_Icc_self hx)) _)
  have hint0 : ∫ x in p'..q', W x = 0 := tendsto_nhds_unique hweak hγ0
  -- a nonnegative function with zero integral vanishes a.e.
  rw [intervalIntegral.integral_of_le hpq.le] at hint0
  have hW0' : 0 ≤ᵐ[volume.restrict (Ioc p' q')] W :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (hW0.mono fun x hx hxI =>
      hx (Ioc_subset_Icc_self hxI))
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hW0' hW.1).mp hint0
  have hzero' : ∀ᵐ x, x ∈ Ioc p' q' → W x = 0 :=
    (ae_restrict_iff' measurableSet_Ioc).mp hzero
  have hnep : ∀ᵐ x, x ≠ p' := by simp [ae_iff, measure_singleton]
  filter_upwards [hzero', hnep] with x hx hxp hxI
  exact hx ⟨lt_of_le_of_ne hxI.1 (Ne.symm hxp), hxI.2⟩

/-! ### Lemma 5.1 assembled -/

/-- **Lemma 5.1** (TeX `L:minimal-spike-limit`, lines 3407–3477), the
deduction after the analytic inputs. Fix `0 < γ < r`, `m, μ, ν, κ > 0` and
let `χ_n → ∞`. For each `n` assume the first integral
`(u_n)_x = χ_n u_n^m/(1+v_n)^β (v_n)_x - F_n` on `[0,L]` (`E:un-eq`), with
`u_n, v_n ≥ 0`, `|F_n| ≤ F_b`, `(1+v_n)^{-β} ≥ κ`, `∫_0^L u_n ≤ M` and
`∫_0^L u_n^r ≤ R`. The analytic inputs (TeX lines 3423–3432) are:

* `(v_n)_x → V_x` uniformly on `[0,L]`, where `V ≥ 0` is `C¹`;
* `∫_p^q u_n^γ → ∫_p^q W` for all `0 ≤ p ≤ q ≤ L`, where `W ≥ 0`,
  `W ∈ L¹(0,L)` (weak convergence `u_n^γ ⇀ W` tested on intervals);
* the limiting equation `-V_xx + μ V = ν W`, `V_x(0) = V_x(L) = 0`
  (`E:lm2-v-limit`), as `V_x(x) = ∫_0^x (μ V - ν W)` and `V_x(L) = 0`.

Then there is `c ≥ 0` with `V = (ν/μ) c` on `[0,L]`, `W = c` a.e. on
`[0,L]`, and `∫_p^q u_n^γ → c (q - p)` for all `0 ≤ p ≤ q ≤ L`. -/
theorem minimal_spike_limit {L gamma m r beta kappa mu nu M Fb R : ℝ}
    {chi : ℕ → ℝ} {u du v dv F : ℕ → ℝ → ℝ} {V dV W : ℝ → ℝ}
    (hL : 0 < L) (hγ : 0 < gamma) (hγr : gamma < r) (hm : 0 < m) (hkappa : 0 < kappa)
    (hmu : 0 < mu) (hnu : 0 < nu) (hchi : Tendsto chi atTop atTop)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hdu : ∀ n, ∀ x ∈ Ioo 0 L, HasDerivAt (u n) (du n x) x)
    (hdu_cont : ∀ n, ContinuousOn (du n) (Icc 0 L))
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L)) (hv0 : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ v n x)
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L)) (hF : ∀ n, ContinuousOn (F n) (Icc 0 L))
    (hflux : ∀ n, ∀ x ∈ Icc 0 L,
      du n x = chi n * (u n x ^ m / (1 + v n x) ^ beta * dv n x) - F n x)
    (hFb : ∀ n, ∀ x ∈ Icc 0 L, |F n x| ≤ Fb)
    (hkappa_le : ∀ n, ∀ x ∈ Icc 0 L, kappa ≤ 1 / (1 + v n x) ^ beta)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x ≤ M)
    (hR : ∀ n, ∫ x in (0 : ℝ)..L, u n x ^ r ≤ R)
    (hV : ContinuousOn V (Icc 0 L)) (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x)
    (hdV_cont : ContinuousOn dV (Icc 0 L)) (hV0 : ∀ x ∈ Icc 0 L, 0 ≤ V x)
    (hdvconv : TendstoUniformlyOn dv dV atTop (Icc 0 L))
    (hW : IntervalIntegrable W volume 0 L) (hW0 : ∀ᵐ x, x ∈ Icc 0 L → 0 ≤ W x)
    (hweak : ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
      Tendsto (fun n => ∫ x in p..q, u n x ^ gamma) atTop (𝓝 (∫ x in p..q, W x)))
    (heq : ∀ x ∈ Icc 0 L, dV x = ∫ y in (0 : ℝ)..x, (mu * V y - nu * W y))
    (hbcL : dV L = 0) :
    ∃ c, 0 ≤ c ∧ (∀ x ∈ Icc 0 L, V x = nu / mu * c) ∧ (∀ᵐ x, x ∈ Icc 0 L → W x = c) ∧
      ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
        Tendsto (fun n => ∫ x in p..q, u n x ^ gamma) atTop (𝓝 (c * (q - p))) := by
  have hWdV : ∀ᵐ x, x ∈ Ioo 0 L → W x * dV x = 0 := by
    refine ae_mul_eq_zero_of_intervals hdV_cont ?_
    intro p q hp hpq hq hne p' q' hpp hpq' hqq
    have hsub : uIcc p' q' ⊆ uIcc 0 L := by
      rw [uIcc_of_le hpq'.le, uIcc_of_le hL.le]
      exact Icc_subset_Icc (by linarith) (by linarith)
    exact weakLimit_ae_zero (W := W) hp hpp hpq' hqq hq hγ hγr hm hkappa hchi hu hu0 hdu
      hdu_cont hv hv0 hdv hF hflux hFb hkappa_le hmass hR hdvconv hdV_cont hne
      (hweak p' q' (by linarith) hpq'.le (by linarith)) (hW.mono_set hsub)
      (hW0.mono fun x hx hxI => hx ⟨by linarith [hxI.1], by linarith [hxI.2]⟩)
  obtain ⟨c, hc0, hVc, hWc⟩ :=
    limit_eq_const hL hmu hnu hV hdV hdV_cont hV0 hW heq hbcL hWdV
  refine ⟨c, hc0, hVc, hWc, fun p q hp hpq hq => ?_⟩
  have hint : ∫ x in p..q, W x = c * (q - p) := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => c) ?_]
    · rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    filter_upwards [hWc] with x hx hxI
    rw [uIoc_of_le hpq] at hxI
    exact hx ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
  rw [← hint]
  exact hweak p q hp hpq hq

end ChemotaxisBifurcation.SpikeLimit
