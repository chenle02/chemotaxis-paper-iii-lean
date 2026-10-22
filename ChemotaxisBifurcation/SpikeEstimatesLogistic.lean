module
public import ChemotaxisBifurcation.SpikeEstimates

@[expose] public section

/-!
# Logistic spike estimates on `[0,L]` (Lemma 4.1(2)–(3))

This file proves the finite, classical-calculus deductions in the proof of
Lemma 4.1(2)–(3) (TeX `L:spiky-solu-lm1`, lines 2774–2910 of the October 8
manuscript) for the logistic model `a, b > 0` of `E:main-PE` (line 350):

* `E:vx-sup` (line 2836): `‖v_x‖_∞ ≤ 2 ν ∫_0^L u^γ ≤ 2 ν L (u*)^γ =: K`;
* `E:energy-ineq-0` (line 2843): testing the first stationary equation with
  `u` gives `½‖u_x‖₂² + b ∫ u^{α+2} ≤ a ∫ u² + (χ₀² K²/2) ∫ u^{2m}`;
* `E:energy-ineq` (line 2850): Young's inequality, with an explicit constant
  `C(X̄,a,b,α,γ,ν,L,m)`, and `‖u_x‖₂² ≤ 2C`;
* `‖u‖_∞ ≤ u* + √L ‖u_x‖₂ ≤ u* + √(2CL) = B` (line 2859);
* `E:first-integral`, `E:F-bound` (lines 2862–2869) and
  `‖u_x‖_∞ ≤ |χ₀| B^m K + 2 a L u*` (line 2873), hence the `C¹` bound with
  `C₁ = max{B, X̄ B^m K + 2 a L u*}` (line 2875);
* Lemma 4.1(3) (lines 2897–2907): the constant
  `C₂ = L^{1/q} (u*)^γ (ν/μ + 2ν + 2νL)` from the componentwise `L^q` bounds.

All statements are conditional consumers: the solution's derivatives, the
stationary equations, the Neumann data and the part (1) moment bounds
(`IntervalMoments.logistic_interval_bounds`) are hypotheses. In Lemma 4.1(3)
the testing identity with `v^{q-1}` plus Hölder, and Minkowski for
`v_xx = μ v - ν u^γ`, are named hypotheses on the abstract norms `‖v‖_q`,
`‖v_xx‖_q`. The higher-regularity (Schauder) assertion of Lemma 4.1(2) is not
treated.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.SpikeEstimates

open Set MeasureTheory

/-! ### Two elementary tools -/

/-- Integrating a derivative bound: if `F` is continuous on `[0,L]` with
derivative `f` on `(0,L)` and `|f| ≤ w` there, with `w ≥ 0` continuous on
`[0,L]`, then `F x ≤ F y + ∫_0^L w` for all `x, y ∈ [0,L]`. -/
theorem le_add_integral_of_abs_deriv_le {L : ℝ} {F f w : ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 L)) (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt F (f x) x)
    (hw : ContinuousOn w (Icc 0 L)) (hw_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ w x)
    (hbound : ∀ x ∈ Ioo 0 L, |f x| ≤ w x) :
    ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L, F x ≤ F y + ∫ t in (0 : ℝ)..L, w t := by
  intro x hx y hy
  have hL : 0 ≤ L := hx.1.trans hx.2
  have hPc := continuousOn_primitive hL hw
  have hint : interior (Icc (0 : ℝ) L) = Ioo 0 L := interior_Icc
  have hanti : AntitoneOn (fun z => F z - ∫ t in (0 : ℝ)..z, w t) (Icc 0 L) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 L) (hF.sub hPc)
      (f' := fun z => f z - w z) ?_ ?_
    · intro z hz; rw [hint] at hz ⊢
      exact ((hderiv z hz).sub (hasDerivAt_primitive hw hz)).hasDerivWithinAt
    · intro z hz; rw [hint] at hz
      have := hbound z hz; have := le_abs_self (f z); linarith
  have hmono : MonotoneOn (fun z => F z + ∫ t in (0 : ℝ)..z, w t) (Icc 0 L) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 L) (hF.add hPc)
      (f' := fun z => f z + w z) ?_ ?_
    · intro z hz; rw [hint] at hz ⊢
      exact ((hderiv z hz).add (hasDerivAt_primitive hw hz)).hasDerivWithinAt
    · intro z hz; rw [hint] at hz
      have := hbound z hz; have := neg_abs_le (f z); linarith
  obtain ⟨hPx0, hPxL⟩ := primitive_mem_Icc hw hw_nonneg hx
  obtain ⟨hPy0, hPyL⟩ := primitive_mem_Icc hw hw_nonneg hy
  rcases le_total y x with hyx | hxy
  · have h := hanti hy hx hyx
    simp only at h
    linarith
  · have h := hmono hx hy hxy
    simp only at h
    linarith

/-- Cauchy–Schwarz on `[0,L]`: `(∫_0^L |f|)² ≤ L ∫_0^L f²` for `f`
continuous on `[0,L]`, `L > 0`. -/
theorem integral_abs_sq_le {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 L)) :
    (∫ t in (0 : ℝ)..L, |f t|) ^ 2 ≤ L * ∫ t in (0 : ℝ)..L, f t ^ 2 := by
  set I := ∫ t in (0 : ℝ)..L, |f t| with hI_def
  set s := I / L with hs_def
  have hsq : ContinuousOn (fun t => f t ^ 2) (Icc 0 L) := hf.pow 2
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..L, (|f t| - s) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le fun t _ => sq_nonneg _
  have hexp : ∫ t in (0 : ℝ)..L, (|f t| - s) ^ 2 =
      (∫ t in (0 : ℝ)..L, f t ^ 2) - 2 * s * I + s ^ 2 * L := by
    have e : ∀ t, (|f t| - s) ^ 2 = (f t ^ 2 - (2 * s) * |f t|) + s ^ 2 := fun t => by
      rw [sub_sq, sq_abs]; ring
    simp_rw [e]
    have i1 : IntervalIntegrable (fun t => f t ^ 2) volume 0 L := hsq.intervalIntegrable_of_Icc hL.le
    have i2 : IntervalIntegrable (fun t => 2 * s * |f t|) volume 0 L :=
      (hf.abs.intervalIntegrable_of_Icc hL.le).const_mul _
    have i3 : IntervalIntegrable (fun t => f t ^ 2 - 2 * s * |f t|) volume 0 L := i1.sub i2
    rw [intervalIntegral.integral_add i3 intervalIntegrable_const,
      intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hexp] at h0
  have hsI : s * L = I := by rw [hs_def]; field_simp
  nlinarith

/-- Young's inequality in the form used at TeX line 2850: for `0 < r < s`,
`A ≥ 0`, `B > 0`, `t ≥ 0`, `A t^r ≤ B t^s + A (A/B)^{r/(s-r)}`. -/
theorem young_rpow (A B r s t : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hr : 0 < r) (hrs : r < s)
    (ht : 0 ≤ t) : A * t ^ r ≤ B * t ^ s + A * (A / B) ^ (r / (s - r)) := by
  have hsr : 0 < s - r := sub_pos.mpr hrs
  have h1 : 0 ≤ B * t ^ s := mul_nonneg hB.le (Real.rpow_nonneg ht s)
  have h2 : 0 ≤ A * (A / B) ^ (r / (s - r)) :=
    mul_nonneg hA (Real.rpow_nonneg (div_nonneg hA hB.le) _)
  by_cases h : A / B ≤ t ^ (s - r)
  · have hAle : A ≤ B * t ^ (s - r) := by rwa [div_le_iff₀' hB] at h
    have hts : t ^ s = t ^ (s - r) * t ^ r := by
      rw [← Real.rpow_add' ht (by linarith)]; ring_nf
    have := mul_le_mul_of_nonneg_right hAle (Real.rpow_nonneg ht r)
    rw [hts]; nlinarith
  · rw [not_le] at h
    have htr : t ^ r = (t ^ (s - r)) ^ (r / (s - r)) := by
      rw [← Real.rpow_mul ht]; congr 1; field_simp
    have hle : t ^ r ≤ (A / B) ^ (r / (s - r)) := by
      rw [htr]
      exact Real.rpow_le_rpow (Real.rpow_nonneg ht _) h.le (div_nonneg hr.le hsr.le)
    have := mul_le_mul_of_nonneg_left hle hA
    linarith

/-! ### `E:vx-sup` -/

/-- **Lemma 4.1(2), `E:vx-sup`** (TeX lines 2834–2838): from the signal
equation with Neumann data and the part (1) moment bound
`∫_0^L u^{1+α} ≤ L (u*)^{1+α}`, for `0 < γ ≤ 1 + α`,
`|v_x| ≤ 2 ν L (u*)^γ =: K` on `[0,L]`. -/
theorem logistic_gradient_le (L mu nu gamma alpha uStar : ℝ) (u v dv ddv : ℝ → ℝ)
    (hL : 0 < L) (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (halpha : 0 < alpha)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1 + alpha) (huStar : 0 ≤ uStar)
    (hu : ContinuousOn u (Icc 0 L)) (hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hv : ContinuousOn v (Icc 0 L)) (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hdv_cont : ContinuousOn dv (Icc 0 L))
    (hddv : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (hsignal : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha)) :
    ∀ x ∈ Icc 0 L, |dv x| ≤ 2 * nu * L * uStar ^ gamma := by
  have hM := IntervalMoments.logistic_power_integral_le L uStar alpha gamma u hL halpha huStar
    hgamma0 hgamma1 hu hu_nonneg hmoment
  intro x hx
  have h := signal_gradient_le_two L mu nu gamma u v dv ddv hL.le hmu hnu hgamma0.le hu
    hu_nonneg hv hv_nonneg hdv_cont hddv hsignal hbc0 hbcL x hx
  have := mul_le_mul_of_nonneg_left hM (by linarith : (0 : ℝ) ≤ 2 * nu)
  linarith

/-! ### The energy inequality -/

/-- **The energy identity behind `E:energy-ineq-0`** (TeX lines 2840–2845).
Testing the stationary first equation
`u_xx - (χ₀ u^m/(1+v)^β v_x)_x + a u - b u^{1+α} = 0` with `u` and using
`u_x = v_x = 0` at `0, L`:
`∫_0^L (u_x² - J u_x - a u² + b u^{α+2}) = 0`, `J = χ₀ u^m/(1+v)^β v_x`. -/
theorem logistic_energy_identity (L a b alpha chi0 m beta : ℝ) (u v du ddu dv dJ : ℝ → ℝ)
    (hL : 0 ≤ L) (halpha : 0 < alpha)
    (hu : ContinuousOn u (Icc 0 L)) (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hdu_cont : ContinuousOn du (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hJ_cont : ContinuousOn (MinimalFlux.flux chi0 m beta u v dv) (Icc 0 L))
    (hJ : ∀ x ∈ Ioo 0 L, HasDerivAt (MinimalFlux.flux chi0 m beta u v dv) (dJ x) x)
    (hstat : ∀ x ∈ Ioo 0 L, ddu x - dJ x + a * u x - b * u x ^ (1 + alpha) = 0)
    (hbc_u0 : du 0 = 0) (hbc_uL : du L = 0) (hbc_v0 : dv 0 = 0) (hbc_vL : dv L = 0) :
    ∫ x in (0 : ℝ)..L, (du x ^ 2 - MinimalFlux.flux chi0 m beta u v dv x * du x -
      a * u x ^ 2 + b * u x ^ (alpha + 2)) = 0 := by
  set J := MinimalFlux.flux chi0 m beta u v dv with hJ_def
  have hpow : ContinuousOn (fun x => u x ^ (alpha + 2)) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr (by linarith)
  have he : ContinuousOn (fun x => du x ^ 2 - J x * du x - a * u x ^ 2 + b * u x ^ (alpha + 2))
      (Icc 0 L) :=
    (((hdu_cont.pow 2).sub (hJ_cont.mul hdu_cont)).sub ((hu.pow 2).const_smul a)).add
      (hpow.const_smul b)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL (f := fun x => u x * (du x - J x))
    (hu.mul (hdu_cont.sub hJ_cont)) (fun x hx => ?_) (he.intervalIntegrable_of_Icc hL)]
  · have hJ0 : J 0 = 0 := by simp [hJ_def, MinimalFlux.flux, hbc_v0]
    have hJL : J L = 0 := by simp [hJ_def, MinimalFlux.flux, hbc_vL]
    simp [hJ0, hJL, hbc_u0, hbc_uL]
  · have hd := (hdu x hx).mul ((hddu x hx).sub (hJ x hx))
    convert hd using 1
    have hux := hu_pos x (Ioo_subset_Icc_self hx)
    have hp : u x ^ (alpha + 2) = u x * u x ^ (1 + alpha) := by
      rw [show alpha + 2 = 1 + (1 + alpha) by ring, Real.rpow_add hux, Real.rpow_one]
    have hs := hstat x hx
    rw [hp]
    have : ddu x - dJ x = b * u x ^ (1 + alpha) - a * u x := by linarith
    rw [this]; simp only [Pi.sub_apply]; ring

/-- **Lemma 4.1(2), `E:energy-ineq-0`** (TeX lines 2842–2846). Under the
hypotheses of `logistic_energy_identity`, with `v ≥ 0`, `β ≥ 0` and
`|v_x| ≤ K` on `[0,L]`:
`½∫u_x² + b∫u^{α+2} ≤ a∫u² + (χ₀²K²/2)∫u^{2m}`. -/
theorem logistic_energy_ineq (L a b alpha chi0 m beta K : ℝ) (u v du ddu dv dJ : ℝ → ℝ)
    (hL : 0 ≤ L) (halpha : 0 < alpha) (hm : 0 < m) (hbeta : 0 ≤ beta)
    (hu : ContinuousOn u (Icc 0 L)) (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hdu_cont : ContinuousOn du (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hJ_cont : ContinuousOn (MinimalFlux.flux chi0 m beta u v dv) (Icc 0 L))
    (hJ : ∀ x ∈ Ioo 0 L, HasDerivAt (MinimalFlux.flux chi0 m beta u v dv) (dJ x) x)
    (hstat : ∀ x ∈ Ioo 0 L, ddu x - dJ x + a * u x - b * u x ^ (1 + alpha) = 0)
    (hbc_u0 : du 0 = 0) (hbc_uL : du L = 0) (hbc_v0 : dv 0 = 0) (hbc_vL : dv L = 0)
    (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x) (hvx : ∀ x ∈ Icc 0 L, |dv x| ≤ K) :
    (1 / 2) * (∫ x in (0 : ℝ)..L, du x ^ 2) + b * ∫ x in (0 : ℝ)..L, u x ^ (alpha + 2) ≤
      a * (∫ x in (0 : ℝ)..L, u x ^ 2) +
        (chi0 ^ 2 * K ^ 2 / 2) * ∫ x in (0 : ℝ)..L, u x ^ (2 * m) := by
  set J := MinimalFlux.flux chi0 m beta u v dv with hJ_def
  set c := chi0 ^ 2 * K ^ 2 / 2 with hc_def
  have hid := logistic_energy_identity L a b alpha chi0 m beta u v du ddu dv dJ hL halpha hu
    hu_pos hdu hdu_cont hddu hJ_cont hJ hstat hbc_u0 hbc_uL hbc_v0 hbc_vL
  have hpow : ContinuousOn (fun x => u x ^ (alpha + 2)) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr (by linarith)
  have hpow2m : ContinuousOn (fun x => u x ^ (2 * m)) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr (by linarith)
  have he : ContinuousOn (fun x => du x ^ 2 - J x * du x - a * u x ^ 2 + b * u x ^ (alpha + 2))
      (Icc 0 L) :=
    (((hdu_cont.pow 2).sub (hJ_cont.mul hdu_cont)).sub ((hu.pow 2).const_smul a)).add
      (hpow.const_smul b)
  have hl : ContinuousOn (fun x => ((1 / 2) * du x ^ 2 + b * u x ^ (alpha + 2)) -
      (a * u x ^ 2 + c * u x ^ (2 * m))) (Icc 0 L) :=
    (((hdu_cont.pow 2).const_smul (1 / 2 : ℝ)).add (hpow.const_smul b)).sub
      (((hu.pow 2).const_smul a).add (hpow2m.const_smul c))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hL (hl.intervalIntegrable_of_Icc hL)
    (he.intervalIntegrable_of_Icc hL) (fun x hx => by
      have hux := hu_pos x hx
      have hden : 1 ≤ (1 + v x) ^ beta := Real.one_le_rpow (by linarith [hv_nonneg x hx]) hbeta
      have hden0 : 0 < (1 + v x) ^ beta := by linarith
      have hum : 0 ≤ u x ^ m := Real.rpow_nonneg hux.le m
      have hJabs : |J x| ≤ |chi0| * u x ^ m * K := by
        have h := flux_abs_le chi0 m beta K (u x) (v x) (J x) (dv x) hux.le (hv_nonneg x hx)
          hbeta (by simp [hJ_def, MinimalFlux.flux]) (hvx x hx)
        exact h
      have hJsq : J x ^ 2 ≤ chi0 ^ 2 * K ^ 2 * u x ^ (2 * m) := by
        have hK : 0 ≤ |chi0| * u x ^ m * K :=
          (abs_nonneg _).trans hJabs
        have h2 : J x ^ 2 ≤ (|chi0| * u x ^ m * K) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hJabs 2
        have h3 : u x ^ (2 * m) = (u x ^ m) ^ 2 := by
          rw [mul_comm, Real.rpow_mul hux.le, Real.rpow_two]
        rw [h3]
        calc J x ^ 2 ≤ (|chi0| * u x ^ m * K) ^ 2 := h2
          _ = chi0 ^ 2 * K ^ 2 * (u x ^ m) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
      have hyoung : J x * du x ≤ (1 / 2) * du x ^ 2 + (1 / 2) * J x ^ 2 := by
        nlinarith [sq_nonneg (J x - du x)]
      simp only [hc_def]
      nlinarith)
  rw [hid] at hmono
  have i1 : IntervalIntegrable (fun x => (1 / 2) * du x ^ 2) volume 0 L :=
    ((hdu_cont.pow 2).intervalIntegrable_of_Icc hL).const_mul _
  have i2 : IntervalIntegrable (fun x => b * u x ^ (alpha + 2)) volume 0 L :=
    (hpow.intervalIntegrable_of_Icc hL).const_mul _
  have i3 : IntervalIntegrable (fun x => a * u x ^ 2) volume 0 L :=
    ((hu.pow 2).intervalIntegrable_of_Icc hL).const_mul _
  have i4 : IntervalIntegrable (fun x => c * u x ^ (2 * m)) volume 0 L :=
    (hpow2m.intervalIntegrable_of_Icc hL).const_mul _
  rw [intervalIntegral.integral_sub (i1.add i2) (i3.add i4),
    intervalIntegral.integral_add i1 i2, intervalIntegral.integral_add i3 i4,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  linarith

/-- The explicit constant of `E:energy-ineq` (TeX line 2852): with
`K = 2 ν L (u*)^γ` and `c̄ = X̄² K²/2`,
`C = L (a (4a/b)^{2/α} + c̄ (4c̄/b)^{2m/(α+2-2m)})`. It depends only on
`X̄, a, b, α, γ, ν, L, m` (through `u*`). -/
noncomputable def energyConstant (Xbar a b alpha gamma nu L m uStar : ℝ) : ℝ :=
  let K := 2 * nu * L * uStar ^ gamma
  let cbar := Xbar ^ 2 * K ^ 2 / 2
  L * (a * (a / (b / 4)) ^ (2 / (alpha + 2 - 2)) +
    cbar * (cbar / (b / 4)) ^ (2 * m / (alpha + 2 - 2 * m)))

/-- **Lemma 4.1(2), `E:energy-ineq` and `‖u_x‖₂² ≤ 2C`** (TeX lines
2847–2855). If `2m < α + 2`, `|χ₀| ≤ X̄`, `|v_x| ≤ K = 2νL(u*)^γ`, and the
energy inequality `E:energy-ineq-0` holds, then
`∫_0^L u_x² ≤ 2 C` with `C = energyConstant X̄ a b α γ ν L m u*`. -/
theorem logistic_gradient_L2_le (L a b alpha gamma nu chi0 Xbar m uStar : ℝ)
    (u du : ℝ → ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 0 < m) (hm2 : 2 * m < alpha + 2) (hchi : |chi0| ≤ Xbar)
    (hu : ContinuousOn u (Icc 0 L)) (hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (henergy : (1 / 2) * (∫ x in (0 : ℝ)..L, du x ^ 2) +
        b * ∫ x in (0 : ℝ)..L, u x ^ (alpha + 2) ≤
      a * (∫ x in (0 : ℝ)..L, u x ^ 2) +
        (chi0 ^ 2 * (2 * nu * L * uStar ^ gamma) ^ 2 / 2) *
          ∫ x in (0 : ℝ)..L, u x ^ (2 * m)) :
    ∫ x in (0 : ℝ)..L, du x ^ 2 ≤ 2 * energyConstant Xbar a b alpha gamma nu L m uStar := by
  set K := 2 * nu * L * uStar ^ gamma with hK_def
  set cbar := Xbar ^ 2 * K ^ 2 / 2 with hcbar_def
  have hcbar : 0 ≤ cbar := by positivity
  have hchi2 : chi0 ^ 2 ≤ Xbar ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hchi 2
  have hpow : ContinuousOn (fun x => u x ^ (alpha + 2)) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr (by linarith)
  have hpow2m : ContinuousOn (fun x => u x ^ (2 * m)) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr (by linarith)
  have h2m0 : 0 ≤ ∫ x in (0 : ℝ)..L, u x ^ (2 * m) :=
    intervalIntegral.integral_nonneg hL fun x hx => Real.rpow_nonneg (hu_nonneg x hx) _
  have hP0 : 0 ≤ ∫ x in (0 : ℝ)..L, u x ^ (alpha + 2) :=
    intervalIntegral.integral_nonneg hL fun x hx => Real.rpow_nonneg (hu_nonneg x hx) _
  have hc_le : (chi0 ^ 2 * K ^ 2 / 2) * ∫ x in (0 : ℝ)..L, u x ^ (2 * m) ≤
      cbar * ∫ x in (0 : ℝ)..L, u x ^ (2 * m) := by
    apply mul_le_mul_of_nonneg_right _ h2m0
    rw [hcbar_def]
    have := mul_le_mul_of_nonneg_right hchi2 (sq_nonneg K)
    linarith
  -- integrated Young
  set Ca := a * (a / (b / 4)) ^ (2 / (alpha + 2 - 2)) with hCa
  set Cc := cbar * (cbar / (b / 4)) ^ (2 * m / (alpha + 2 - 2 * m)) with hCc
  have hb4 : 0 < b / 4 := by linarith
  have j1 : IntervalIntegrable (fun x => a * u x ^ 2) volume 0 L :=
    ((hu.pow 2).intervalIntegrable_of_Icc hL).const_mul _
  have j2 : IntervalIntegrable (fun x => cbar * u x ^ (2 * m)) volume 0 L :=
    (hpow2m.intervalIntegrable_of_Icc hL).const_mul _
  have j3 : IntervalIntegrable (fun x => (b / 2) * u x ^ (alpha + 2)) volume 0 L :=
    (hpow.intervalIntegrable_of_Icc hL).const_mul _
  have hyoung := intervalIntegral.integral_mono_on (μ := volume) hL (j1.add j2)
    (j3.add (intervalIntegrable_const (c := Ca + Cc)))
    (fun x hx => by
      have t := hu_nonneg x hx
      have y1 := young_rpow a (b / 4) 2 (alpha + 2) (u x) ha hb4 (by norm_num) (by linarith) t
      have y2 := young_rpow cbar (b / 4) (2 * m) (alpha + 2) (u x) hcbar hb4 (by linarith) hm2 t
      rw [Real.rpow_two] at y1
      show a * u x ^ 2 + cbar * u x ^ (2 * m) ≤ (b / 2) * u x ^ (alpha + 2) + (Ca + Cc)
      rw [hCa, hCc]
      linarith)
  rw [intervalIntegral.integral_add j1 j2,
    intervalIntegral.integral_add j3 intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
    sub_zero] at hyoung
  have hC : energyConstant Xbar a b alpha gamma nu L m uStar = L * (Ca + Cc) := by
    simp only [energyConstant, hCa, hCc, hcbar_def, hK_def]
  rw [hC]
  have hsq0 : 0 ≤ ∫ x in (0 : ℝ)..L, du x ^ 2 := by
    rcases eq_or_lt_of_le hL with h | h
    · subst h; simp
    · exact intervalIntegral.integral_nonneg hL fun x _ => sq_nonneg _
  nlinarith

/-! ### The `C¹` bound -/

/-- **Lemma 4.1(2), `‖u‖_∞ ≤ u* + √L‖u_x‖₂ ≤ u* + √(2CL) = B`** (TeX lines
2856–2860). Here `u` is continuous on `[0,L]` with continuous derivative
`u_x`, `∫_0^L u ≤ L u*` (part (1)) and `∫_0^L u_x² ≤ 2C`. -/
theorem logistic_sup_le (L uStar C : ℝ) (u du : ℝ → ℝ) (hL : 0 < L)
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hdu_cont : ContinuousOn du (Icc 0 L))
    (hmean : ∫ x in (0 : ℝ)..L, u x ≤ L * uStar)
    (hL2 : ∫ x in (0 : ℝ)..L, du x ^ 2 ≤ 2 * C) :
    ∀ x ∈ Icc 0 L, u x ≤ uStar + Real.sqrt (2 * C * L) := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hu
  have hlow := IntervalMoments.le_integral_of_le hL.le hu (fun z hz => hmin hz)
  have huy : u y ≤ uStar := le_of_mul_le_mul_left (hlow.trans hmean) hL
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..L, |du t| :=
    intervalIntegral.integral_nonneg hL.le fun t _ => abs_nonneg _
  have hcs := integral_abs_sq_le hL hdu_cont
  have hI : ∫ t in (0 : ℝ)..L, |du t| ≤ Real.sqrt (2 * C * L) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  intro x hx
  have h := le_add_integral_of_abs_deriv_le hu hdu hdu_cont.abs (fun _ _ => abs_nonneg _)
    (fun _ _ => le_rfl) x hx y hy
  linarith

/-- **Lemma 4.1(2), `E:first-integral`** (TeX lines 2861–2865): integrating
the stationary first equation from `0`,
`u_x = χ₀ u^m/(1+v)^β v_x - F`, `F(x) = ∫_0^x (a u - b u^{1+α})`. -/
theorem logistic_first_integral (L a b alpha chi0 m beta : ℝ) (u v du ddu dv dJ : ℝ → ℝ)
    (hL : 0 ≤ L) (halpha : 0 < alpha) (hu : ContinuousOn u (Icc 0 L))
    (hdu_cont : ContinuousOn du (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hJ_cont : ContinuousOn (MinimalFlux.flux chi0 m beta u v dv) (Icc 0 L))
    (hJ : ∀ x ∈ Ioo 0 L, HasDerivAt (MinimalFlux.flux chi0 m beta u v dv) (dJ x) x)
    (hstat : ∀ x ∈ Ioo 0 L, ddu x - dJ x + a * u x - b * u x ^ (1 + alpha) = 0)
    (hbc_u0 : du 0 = 0) (hbc_v0 : dv 0 = 0) :
    ∀ x ∈ Icc 0 L, du x = chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x -
      ∫ y in (0 : ℝ)..x, (a * u y - b * u y ^ (1 + alpha)) := by
  have hg : ContinuousOn (fun y => a * u y - b * u y ^ (1 + alpha)) (Icc 0 L) :=
    (hu.const_smul a).sub ((hu.rpow_const fun _ _ => Or.inr (by linarith)).const_smul b)
  have h := MinimalFlux.eq_left_of_hasDerivAt_zero
    (F := fun x => du x - MinimalFlux.flux chi0 m beta u v dv x +
      ∫ y in (0 : ℝ)..x, (a * u y - b * u y ^ (1 + alpha)))
    ((hdu_cont.sub hJ_cont).add (continuousOn_primitive hL hg))
    (fun x hx => by
      have hd := ((hddu x hx).sub (hJ x hx)).add (hasDerivAt_primitive hg hx)
      convert hd using 1
      linarith [hstat x hx])
  intro x hx
  have hx' := h x hx
  simp only [MinimalFlux.flux, intervalIntegral.integral_same, hbc_u0, hbc_v0, mul_zero,
    sub_zero, add_zero] at hx'
  linarith

/-- **Lemma 4.1(2), `E:F-bound`** (TeX lines 2866–2869):
`|F(x)| ≤ a∫_0^L u + b∫_0^L u^{1+α} ≤ 2 a L u*`, using the mass identity
`a∫u = b∫u^{1+α}` (`E:mass-identity`) and `∫u ≤ L u*` (part (1)). -/
theorem logistic_F_bound (L a b alpha uStar : ℝ) (u : ℝ → ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (halpha : 0 < alpha) (hu : ContinuousOn u (Icc 0 L)) (hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hmassid : a * ∫ x in (0 : ℝ)..L, u x = b * ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha))
    (hmean : ∫ x in (0 : ℝ)..L, u x ≤ L * uStar) :
    ∀ x ∈ Icc 0 L,
      |∫ y in (0 : ℝ)..x, (a * u y - b * u y ^ (1 + alpha))| ≤
        a * (∫ y in (0 : ℝ)..L, u y) + b * ∫ y in (0 : ℝ)..L, u y ^ (1 + alpha) ∧
      |∫ y in (0 : ℝ)..x, (a * u y - b * u y ^ (1 + alpha))| ≤ 2 * a * L * uStar := by
  intro x hx
  have hL : 0 ≤ L := hx.1.trans hx.2
  have hw : ContinuousOn (fun y => u y ^ (1 + alpha)) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr (by linarith)
  have hsub : uIcc 0 x ⊆ Icc 0 L := uIcc_subset_Icc ⟨le_rfl, hL⟩ hx
  rw [intervalIntegral.integral_sub (((hu.mono hsub).intervalIntegrable).const_mul a)
    (((hw.mono hsub).intervalIntegrable).const_mul b), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  obtain ⟨h1, h2⟩ := primitive_mem_Icc hu hu_nonneg hx
  obtain ⟨h3, h4⟩ := primitive_mem_Icc hw (fun y hy => Real.rpow_nonneg (hu_nonneg y hy) _) hx
  have a1 := mul_nonneg ha h1
  have a2 := mul_le_mul_of_nonneg_left h2 ha
  have a3 := mul_nonneg hb h3
  have a4 := mul_le_mul_of_nonneg_left h4 hb
  have hfirst : |a * (∫ y in (0 : ℝ)..x, u y) - b * ∫ y in (0 : ℝ)..x, u y ^ (1 + alpha)| ≤
      a * (∫ y in (0 : ℝ)..L, u y) + b * ∫ y in (0 : ℝ)..L, u y ^ (1 + alpha) := by
    rw [abs_le]; constructor <;> linarith
  refine ⟨hfirst, ?_⟩
  have := mul_le_mul_of_nonneg_left hmean ha
  linarith

/-- **Lemma 4.1(2), the `C¹` bound** (TeX lines 2856–2876). Assume the first
integral `u_x = χ₀ u^m/(1+v)^β v_x - F` on `[0,L]` with `|F| ≤ 2aLu*`,
`v ≥ 0`, `β ≥ 0`, `m > 0`, `|v_x| ≤ K`, `0 < u ≤ B` and `|χ₀| ≤ X̄`. Then
`|u_x| ≤ |χ₀| B^m K + 2aLu*`, and both `u` and `|u_x|` are bounded by
`C₁ = max{B, X̄ B^m K + 2aLu*}`. -/
theorem logistic_C1_bound (L a uStar chi0 Xbar m beta K B : ℝ) (u v du dv F : ℝ → ℝ)
    (hm : 0 < m) (hbeta : 0 ≤ beta) (hK : 0 ≤ K) (hchi : |chi0| ≤ Xbar)
    (hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x) (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hfirst : ∀ x ∈ Icc 0 L, du x = chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x - F x)
    (hF : ∀ x ∈ Icc 0 L, |F x| ≤ 2 * a * L * uStar)
    (hvx : ∀ x ∈ Icc 0 L, |dv x| ≤ K) (huB : ∀ x ∈ Icc 0 L, u x ≤ B) :
    ∀ x ∈ Icc 0 L,
      |du x| ≤ |chi0| * B ^ m * K + 2 * a * L * uStar ∧
      u x ≤ max B (Xbar * B ^ m * K + 2 * a * L * uStar) ∧
      |du x| ≤ max B (Xbar * B ^ m * K + 2 * a * L * uStar) := by
  intro x hx
  have hJ := flux_abs_le chi0 m beta K (u x) (v x) _ (dv x) (hu_nonneg x hx) (hv_nonneg x hx)
    hbeta rfl (hvx x hx)
  have hBm : u x ^ m ≤ B ^ m := Real.rpow_le_rpow (hu_nonneg x hx) (huB x hx) hm.le
  have hJB : |chi0| * u x ^ m * K ≤ |chi0| * B ^ m * K :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBm (abs_nonneg _)) hK
  have hdu : |du x| ≤ |chi0| * B ^ m * K + 2 * a * L * uStar := by
    rw [hfirst x hx]
    calc |chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x - F x|
        ≤ |chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x| + |F x| := abs_sub _ _
      _ ≤ |chi0| * B ^ m * K + 2 * a * L * uStar := by linarith [hF x hx]
  have hB0 : 0 ≤ B := (hu_nonneg x hx).trans (huB x hx)
  have hX : |chi0| * B ^ m * K ≤ Xbar * B ^ m * K :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchi (Real.rpow_nonneg hB0 m)) hK
  refine ⟨hdu, (huB x hx).trans (le_max_left _ _), ?_⟩
  exact (hdu.trans (by linarith)).trans (le_max_right _ _)

/-- **Lemma 4.1(2), the `C¹` bound `E:bound-u-eq3` assembled** (TeX lines
2799–2812 and 2829–2876). For `a, b, α > 0`, `0 < γ ≤ 1 + α`,
`0 < m < (α+2)/2`, `β ≥ 0`, `|χ₀| ≤ X̄`: a positive stationary solution, given
through its derivatives, the two stationary equations on `(0,L)`, the
Neumann data, and the part (1) consequences
`a∫u = b∫u^{1+α}`, `∫u ≤ Lu*`, `∫u^{1+α} ≤ L(u*)^{1+α}`, satisfies
`u ≤ C₁` and `|u_x| ≤ C₁` on `[0,L]`, where
`K = 2νL(u*)^γ`, `C = energyConstant X̄ a b α γ ν L m u*`,
`B = u* + √(2CL)` and `C₁ = max{B, X̄ B^m K + 2aLu*}`. The constant does not
involve `μ`, `β` or `χ₀`. -/
theorem logistic_C1_chain (L a b alpha gamma mu nu chi0 Xbar m beta uStar : ℝ)
    (u v du ddu dv ddv dJ : ℝ → ℝ)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1 + alpha) (hm0 : 0 < m)
    (hm2 : 2 * m < alpha + 2) (hbeta : 0 ≤ beta) (hmu : 0 ≤ mu) (hnu : 0 ≤ nu)
    (huStar : 0 ≤ uStar) (hchi : |chi0| ≤ Xbar)
    (hu : ContinuousOn u (Icc 0 L)) (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hdu_cont : ContinuousOn du (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hv : ContinuousOn v (Icc 0 L)) (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hdv_cont : ContinuousOn dv (Icc 0 L))
    (hddv : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (hsignal : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hJ_cont : ContinuousOn (MinimalFlux.flux chi0 m beta u v dv) (Icc 0 L))
    (hJ : ∀ x ∈ Ioo 0 L, HasDerivAt (MinimalFlux.flux chi0 m beta u v dv) (dJ x) x)
    (hstat : ∀ x ∈ Ioo 0 L, ddu x - dJ x + a * u x - b * u x ^ (1 + alpha) = 0)
    (hbc_u0 : du 0 = 0) (hbc_uL : du L = 0) (hbc_v0 : dv 0 = 0) (hbc_vL : dv L = 0)
    (hmassid : a * ∫ x in (0 : ℝ)..L, u x = b * ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha))
    (hmean : ∫ x in (0 : ℝ)..L, u x ≤ L * uStar)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha)) :
    ∀ x ∈ Icc 0 L,
      u x ≤ max (uStar + Real.sqrt (2 * energyConstant Xbar a b alpha gamma nu L m uStar * L))
        (Xbar * (uStar + Real.sqrt (2 * energyConstant Xbar a b alpha gamma nu L m uStar * L)) ^ m *
          (2 * nu * L * uStar ^ gamma) + 2 * a * L * uStar) ∧
      |du x| ≤ max (uStar + Real.sqrt (2 * energyConstant Xbar a b alpha gamma nu L m uStar * L))
        (Xbar * (uStar + Real.sqrt (2 * energyConstant Xbar a b alpha gamma nu L m uStar * L)) ^ m *
          (2 * nu * L * uStar ^ gamma) + 2 * a * L * uStar) := by
  have hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x := fun x hx => (hu_pos x hx).le
  have hK := logistic_gradient_le L mu nu gamma alpha uStar u v dv ddv hL hmu hnu halpha hgamma0
    hgamma1 huStar hu hu_nonneg hv hv_nonneg hdv_cont hddv hsignal hbc_v0 hbc_vL hmoment
  have hE := logistic_energy_ineq L a b alpha chi0 m beta (2 * nu * L * uStar ^ gamma) u v du ddu
    dv dJ hL.le halpha hm0 hbeta hu hu_pos hdu hdu_cont hddu hJ_cont hJ hstat hbc_u0 hbc_uL
    hbc_v0 hbc_vL hv_nonneg hK
  have hL2 := logistic_gradient_L2_le L a b alpha gamma nu chi0 Xbar m uStar u du hL.le ha.le hb
    halpha hm0 hm2 hchi hu hu_nonneg hE
  have hB := logistic_sup_le L uStar _ u du hL hu hdu hdu_cont hmean hL2
  have hfirst := logistic_first_integral L a b alpha chi0 m beta u v du ddu dv dJ hL.le halpha hu
    hdu_cont hddu hJ_cont hJ hstat hbc_u0 hbc_v0
  have hF := logistic_F_bound L a b alpha uStar u ha.le hb.le halpha hu hu_nonneg hmassid hmean
  have hK0 : 0 ≤ 2 * nu * L * uStar ^ gamma := (abs_nonneg _).trans (hK 0 ⟨le_rfl, hL.le⟩)
  intro x hx
  have h := logistic_C1_bound L a uStar chi0 Xbar m beta (2 * nu * L * uStar ^ gamma) _ u v du dv
    (fun y => ∫ t in (0 : ℝ)..y, (a * u t - b * u t ^ (1 + alpha))) hm0 hbeta hK0 hchi hu_nonneg
    hv_nonneg hfirst (fun y hy => (hF y hy).2) hK hB x hx
  exact ⟨h.2.1, h.2.2⟩

/-! ### Lemma 4.1(3) -/

/-- **Lemma 4.1(3)**, TeX lines 2897–2907. Let `q > 1` with `γ q = 1 + α`.
The analytic inputs are named hypotheses on the abstract norms
`nv = ‖v‖_q ≥ 0` and `nvxx = ‖v_xx‖_q`: the tested signal equation with
Hölder, `μ nv^q ≤ ν ‖u^γ‖_q nv^{q-1}` (line 2900, after dropping the
nonnegative gradient term), and Minkowski for `v_xx = μ v - ν u^γ`,
`nvxx ≤ μ nv + ν ‖u^γ‖_q`. The `L^q` norms of `u^γ` and `v_x` are the
actual integrals. With the part (1) moment bound and `|v_x| ≤ K = 2νL(u*)^γ`
(`E:vx-sup`), the conclusion is
`‖v‖_q + ‖v_x‖_q + ‖v_xx‖_q ≤ C₂ = L^{1/q}(u*)^γ(ν/μ + 2ν + 2νL)`. -/
theorem logistic_W2q_bound (L mu nu gamma alpha uStar q nv nvxx : ℝ) (u dv : ℝ → ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hnu : 0 ≤ nu)
    (huStar : 0 ≤ uStar) (hq : 1 < q) (hgq : gamma * q = 1 + alpha) (hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hdv_cont : ContinuousOn dv (Icc 0 L))
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha))
    (hvx : ∀ x ∈ Icc 0 L, |dv x| ≤ 2 * nu * L * uStar ^ gamma)
    (hnv : 0 ≤ nv)
    (htest : mu * nv ^ q ≤
      nu * (∫ x in (0 : ℝ)..L, (u x ^ gamma) ^ q) ^ (1 / q) * nv ^ (q - 1))
    (hminkowski : nvxx ≤ mu * nv + nu * (∫ x in (0 : ℝ)..L, (u x ^ gamma) ^ q) ^ (1 / q)) :
    nv + (∫ x in (0 : ℝ)..L, |dv x| ^ q) ^ (1 / q) + nvxx ≤
      L ^ (1 / q) * uStar ^ gamma * (nu / mu + 2 * nu + 2 * nu * L) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 ≤ 1 / q := one_div_nonneg.mpr hq0.le
  set nug := (∫ x in (0 : ℝ)..L, (u x ^ gamma) ^ q) ^ (1 / q) with hnug_def
  set Lq := L ^ (1 / q) with hLq_def
  have hLq : 0 ≤ Lq := Real.rpow_nonneg hL.le _
  -- `‖u^γ‖_q ≤ L^{1/q} (u*)^γ`
  have hpowq : ∫ x in (0 : ℝ)..L, (u x ^ gamma) ^ q = ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hL.le] at hx
    simp only
    rw [← Real.rpow_mul (hu_nonneg x hx), hgq]
  have hug0 : 0 ≤ ∫ x in (0 : ℝ)..L, (u x ^ gamma) ^ q :=
    intervalIntegral.integral_nonneg hL.le fun x hx =>
      Real.rpow_nonneg (Real.rpow_nonneg (hu_nonneg x hx) _) _
  have hus : (uStar ^ (1 + alpha)) ^ (1 / q) = uStar ^ gamma := by
    rw [← Real.rpow_mul huStar, ← hgq]; field_simp
  have hnug : nug ≤ Lq * uStar ^ gamma := by
    rw [hnug_def, hpowq, hLq_def, ← hus, ← Real.mul_rpow hL.le (Real.rpow_nonneg huStar _)]
    exact Real.rpow_le_rpow (by rw [← hpowq]; exact hug0) hmoment hq1
  have hnug0 : 0 ≤ nug := Real.rpow_nonneg hug0 _
  -- `‖v‖_q ≤ (ν/μ) ‖u^γ‖_q`
  have hnv_le : nv ≤ nu / mu * nug := by
    rcases eq_or_lt_of_le hnv with h | h
    · rw [← h]; exact mul_nonneg (div_nonneg hnu hmu.le) hnug0
    · have hsplit : nv ^ q = nv ^ (q - 1) * nv := by
        rw [← Real.rpow_add_one h.ne']; ring_nf
      have hpos : 0 < nv ^ (q - 1) := Real.rpow_pos_of_pos h _
      rw [hsplit] at htest
      have h2 : mu * nv ≤ nu * nug := by
        have : nv ^ (q - 1) * (mu * nv) ≤ nv ^ (q - 1) * (nu * nug) := by nlinarith
        exact le_of_mul_le_mul_left this hpos
      rw [div_mul_eq_mul_div, le_div_iff₀ hmu]
      linarith
  -- `‖v_x‖_q ≤ L^{1/q} K`
  set K := 2 * nu * L * uStar ^ gamma with hK_def
  have hK : 0 ≤ K := (abs_nonneg _).trans (hvx 0 ⟨le_rfl, hL.le⟩)
  have hdvq : ContinuousOn (fun x => |dv x| ^ q) (Icc 0 L) :=
    hdv_cont.abs.rpow_const fun _ _ => Or.inr hq0.le
  have hint := IntervalMoments.integral_le_of_le hL.le hdvq
    (fun x hx => Real.rpow_le_rpow (abs_nonneg _) (hvx x hx) hq0.le)
  have hvxq : (∫ x in (0 : ℝ)..L, |dv x| ^ q) ^ (1 / q) ≤ Lq * K := by
    have h0 : 0 ≤ ∫ x in (0 : ℝ)..L, |dv x| ^ q :=
      intervalIntegral.integral_nonneg hL.le fun x _ => Real.rpow_nonneg (abs_nonneg _) _
    calc (∫ x in (0 : ℝ)..L, |dv x| ^ q) ^ (1 / q) ≤ (L * K ^ q) ^ (1 / q) :=
          Real.rpow_le_rpow h0 hint hq1
      _ = Lq * K := by
          rw [Real.mul_rpow hL.le (Real.rpow_nonneg hK _), ← Real.rpow_mul hK,
            mul_one_div_cancel hq0.ne', Real.rpow_one]
  -- assemble
  have hus0 : 0 ≤ uStar ^ gamma := Real.rpow_nonneg huStar _
  have e1 : nu / mu * nug ≤ nu / mu * (Lq * uStar ^ gamma) :=
    mul_le_mul_of_nonneg_left hnug (div_nonneg hnu hmu.le)
  have e2 : mu * nv ≤ nu * nug := by
    have := mul_le_mul_of_nonneg_left hnv_le hmu.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hmu.ne'] at this
  have e3 : nu * nug ≤ nu * (Lq * uStar ^ gamma) := mul_le_mul_of_nonneg_left hnug hnu
  have e4 : Lq * K = Lq * uStar ^ gamma * (2 * nu * L) := by rw [hK_def]; ring
  have e5 : Lq * uStar ^ gamma * (nu / mu + 2 * nu + 2 * nu * L) =
      nu / mu * (Lq * uStar ^ gamma) + 2 * (nu * (Lq * uStar ^ gamma)) +
        Lq * uStar ^ gamma * (2 * nu * L) := by ring
  rw [e5]
  linarith

end ChemotaxisBifurcation.SpikeEstimates
