module
public import ChemotaxisBifurcation.IntervalMoments
public import ChemotaxisBifurcation.MinimalFlux
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Signal and spike estimates on `[0,L]` (Lemma 4.2(3)–(5))

This file proves the finite, classical-calculus content of
Lemma 4.2 (TeX `L:minimal-spike-bounds`, lines 2913–3020 of the
October 8 manuscript):

* part (3): integrating the signal equation `0 = v_xx - μ v + ν u^γ`
  (TeX `E:main-PE`, line 354) with `v_x(0) = v_x(L) = 0` gives
  `μ ∫_0^L v = ν M_γ`, `v_x(x) = μ ∫_0^x v - ν ∫_0^x u^γ`, and the bounds
  `‖v_x‖_∞ ≤ 2 ν M_γ`, `‖v‖_∞ ≤ ν M_γ/(μL) + 2 ν M_γ L`,
  `‖v_xx‖_{L¹} ≤ 2 ν M_γ` (TeX lines 2968–2984);
* part (4): for `0 < m < 2` the bounds `‖u‖_∞ ≤ U` and
  `‖u_x‖_∞ ≤ 2|χ₀| ν M_γ U^m` (TeX lines 2930–2937, 2987–3000);
* part (5): for `m = 1`, `‖u‖_∞ ≤ u* e^{2 X̄ ν M_γ L}` (TeX lines 3001–3010).

Everything is a conditional consumer. The solution's derivatives
(`dv = v_x`, `ddv = v_xx`, `du = u_x`), the signal equation, the Neumann
values, the flux identity (proved separately in `MinimalFlux`) and the
prescribed mass are explicit hypotheses. Existence and regularity of the
solution, and the Schauder part of Lemma 4.2(5), are not proved here.

The signal-equation results do not use `a = b = 0`; they also serve
Lemma 4.1 (TeX `E:vx-sup`, line 2836), see `SpikeEstimatesLogistic`.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.SpikeEstimates

open Set MeasureTheory
open scoped Interval

/-! ### Elementary calculus on `[0,L]` -/

/-- Mean value bound: a function continuous on `[0,L]` whose derivative on
`(0,L)` is bounded by `K` in absolute value is `K`-Lipschitz on `[0,L]`. -/
theorem abs_sub_le_of_abs_deriv_le {L K : ℝ} {F f : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt F (f x) x) (hbound : ∀ x ∈ Ioo 0 L, |f x| ≤ K) :
    ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L, |F x - F y| ≤ K * |x - y| := by
  have key : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L, y < x → |F x - F y| ≤ K * |x - y| := by
    intro x hx y hy hyx
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F f hyx
      (hF.mono (Icc_subset_Icc hy.1 hx.2))
      (fun z hz => hderiv z ⟨hy.1.trans_lt hz.1, hz.2.trans_le hx.2⟩)
    have hpos : 0 < x - y := sub_pos.mpr hyx
    have hcI : c ∈ Ioo 0 L := ⟨hy.1.trans_lt hc.1, hc.2.trans_le hx.2⟩
    have heq : F x - F y = f c * (x - y) := by
      rw [hslope]; field_simp
    rw [heq, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right (hbound c hcI) hpos.le
  intro x hx y hy
  rcases lt_trichotomy y x with h | h | h
  · exact key x hx y hy h
  · subst h
    simp
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact key y hy x hx h

/-- FTC for the primitive `x ↦ ∫_0^x g` at an interior point of `[0,L]`. -/
theorem hasDerivAt_primitive {L : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 L)) {x : ℝ}
    (hx : x ∈ Ioo 0 L) : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, g t) (g x) x := by
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hx.1.le.trans hx.2.le⟩
  exact intervalIntegral.integral_hasDerivAt_right
    ((hg.mono (uIcc_subset_Icc h0 (Ioo_subset_Icc_self hx))).intervalIntegrable)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hg.mono Ioo_subset_Icc_self) x hx)
    (hg.continuousAt (Icc_mem_nhds hx.1 hx.2))

/-- The primitive `x ↦ ∫_0^x g` of a function continuous on `[0,L]` is
continuous on `[0,L]`. -/
theorem continuousOn_primitive {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 L)) :
    ContinuousOn (fun y => ∫ t in (0 : ℝ)..y, g t) (Icc 0 L) := by
  have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := L)
    (f := g) (by rw [uIcc_of_le hL]; exact hg.integrableOn_Icc)
  rwa [uIcc_of_le hL] at h

/-- For `g ≥ 0` on `[0,L]` and `x ∈ [0,L]`: `0 ≤ ∫_0^x g ≤ ∫_0^L g`. -/
theorem primitive_mem_Icc {L : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 L))
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ g x) {x : ℝ} (hx : x ∈ Icc 0 L) :
    0 ≤ ∫ t in (0 : ℝ)..x, g t ∧ ∫ t in (0 : ℝ)..x, g t ≤ ∫ t in (0 : ℝ)..L, g t := by
  have hL : 0 ≤ L := hx.1.trans hx.2
  refine ⟨intervalIntegral.integral_nonneg hx.1 fun t ht => hnonneg t ⟨ht.1, ht.2.trans hx.2⟩, ?_⟩
  have h0x : IntervalIntegrable g volume 0 x :=
    (hg.mono (uIcc_subset_Icc ⟨le_rfl, hL⟩ hx)).intervalIntegrable
  have hxL : IntervalIntegrable g volume x L :=
    (hg.mono (uIcc_subset_Icc hx ⟨hL, le_rfl⟩)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals h0x hxL]
  have : 0 ≤ ∫ t in x..L, g t :=
    intervalIntegral.integral_nonneg hx.2 fun t ht => hnonneg t ⟨hx.1.trans ht.1, ht.2⟩
  linarith

/-! ### Lemma 4.2(3): the signal equation -/

/-- **Lemma 4.2(3), first display** (TeX lines 2970–2974). If `v_x` is
continuous on `[0,L]` with derivative `v_xx` on `(0,L)`, the signal equation
`v_xx - μ v + ν u^γ = 0` holds on `(0,L)` and `v_x(0) = 0`, then
`v_x(x) = μ ∫_0^x v - ν ∫_0^x u^γ` on `[0,L]`. -/
theorem signal_flux_eq (L mu nu gamma : ℝ) (u v dv ddv : ℝ → ℝ) (hL : 0 ≤ L)
    (hgamma : 0 ≤ gamma) (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hdv_cont : ContinuousOn dv (Icc 0 L))
    (hddv : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (hsignal : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) :
    ∀ x ∈ Icc 0 L,
      dv x = mu * (∫ y in (0 : ℝ)..x, v y) - nu * ∫ y in (0 : ℝ)..x, u y ^ gamma := by
  have hw : ContinuousOn (fun x => u x ^ gamma) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr hgamma
  have h := MinimalFlux.eq_left_of_hasDerivAt_zero
    (F := fun x => dv x - (mu * (∫ y in (0 : ℝ)..x, v y) - nu * ∫ y in (0 : ℝ)..x, u y ^ gamma))
    (hdv_cont.sub (((continuousOn_primitive hL hv).const_smul mu).sub
      ((continuousOn_primitive hL hw).const_smul nu)))
    (fun x hx => by
      have hd := (hddv x hx).sub (((hasDerivAt_primitive hv hx).const_mul mu).sub
        ((hasDerivAt_primitive hw hx).const_mul nu))
      convert hd using 1
      linarith [hsignal x hx])
  intro x hx
  have hx' := h x hx
  simp only [intervalIntegral.integral_same, mul_zero, sub_zero, hbc0] at hx'
  linarith

/-- **Lemma 4.2(3), the mass identity** `μ ∫_0^L v = ν M_γ` (TeX line 2972):
the case `x = L` of `signal_flux_eq` with `v_x(L) = 0`. -/
theorem signal_mass_eq (L mu nu gamma : ℝ) (u v dv ddv : ℝ → ℝ) (hL : 0 ≤ L)
    (hgamma : 0 ≤ gamma) (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hdv_cont : ContinuousOn dv (Icc 0 L))
    (hddv : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (hsignal : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0) :
    mu * (∫ y in (0 : ℝ)..L, v y) = nu * ∫ y in (0 : ℝ)..L, u y ^ gamma := by
  have h := signal_flux_eq L mu nu gamma u v dv ddv hL hgamma hu hv hdv_cont hddv hsignal hbc0
    L ⟨hL, le_rfl⟩
  rw [hbcL] at h
  linarith

/-- **Lemma 4.2(3), the gradient bound** (TeX line 2977), in the sharper form
`|v_x| ≤ ν M_γ`: both terms of `v_x(x) = μ∫_0^x v - ν∫_0^x u^γ` lie in
`[0, ν M_γ]` because `u, v ≥ 0`. -/
theorem signal_gradient_le (L mu nu gamma : ℝ) (u v dv ddv : ℝ → ℝ) (hL : 0 ≤ L)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hv : ContinuousOn v (Icc 0 L)) (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hdv_cont : ContinuousOn dv (Icc 0 L))
    (hddv : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (hsignal : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0) :
    ∀ x ∈ Icc 0 L, |dv x| ≤ nu * ∫ y in (0 : ℝ)..L, u y ^ gamma := by
  have hw : ContinuousOn (fun x => u x ^ gamma) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr hgamma
  have hmass := signal_mass_eq L mu nu gamma u v dv ddv hL hgamma hu hv hdv_cont hddv hsignal
    hbc0 hbcL
  intro x hx
  rw [signal_flux_eq L mu nu gamma u v dv ddv hL hgamma hu hv hdv_cont hddv hsignal hbc0 x hx]
  obtain ⟨hv0, hvL⟩ := primitive_mem_Icc hv hv_nonneg hx
  obtain ⟨hw0, hwL⟩ := primitive_mem_Icc hw (fun y hy => Real.rpow_nonneg (hu_nonneg y hy) _) hx
  have a1 := mul_nonneg hmu hv0
  have a2 := mul_le_mul_of_nonneg_left hvL hmu
  have a3 := mul_nonneg hnu hw0
  have a4 := mul_le_mul_of_nonneg_left hwL hnu
  rw [abs_le]
  constructor <;> linarith

/-- **Lemma 4.2(3)**, `‖v_x‖_∞ ≤ 2 ν M_γ` with the manuscript's constant
(TeX line 2977). -/
theorem signal_gradient_le_two (L mu nu gamma : ℝ) (u v dv ddv : ℝ → ℝ) (hL : 0 ≤ L)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hv : ContinuousOn v (Icc 0 L)) (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hdv_cont : ContinuousOn dv (Icc 0 L))
    (hddv : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (hsignal : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0) :
    ∀ x ∈ Icc 0 L, |dv x| ≤ 2 * nu * ∫ y in (0 : ℝ)..L, u y ^ gamma := by
  intro x hx
  have h := signal_gradient_le L mu nu gamma u v dv ddv hL hmu hnu hgamma hu hu_nonneg hv
    hv_nonneg hdv_cont hddv hsignal hbc0 hbcL x hx
  have hM : 0 ≤ nu * ∫ y in (0 : ℝ)..L, u y ^ gamma :=
    mul_nonneg hnu (intervalIntegral.integral_nonneg hL fun y hy =>
      Real.rpow_nonneg (hu_nonneg y hy) _)
  linarith

/-- **Lemma 4.2(3)**, the sup bound for `v` (TeX lines 2979–2980):
`v ≤ ν M_γ/(μL) + 2 ν M_γ L` on `[0,L]` (the proof gives `ν M_γ L` in place of
`2 ν M_γ L`). Here `v` is continuous on `[0,L]` with derivative `v_x` on
`(0,L)`. -/
theorem signal_sup_le (L mu nu gamma : ℝ) (u v dv ddv : ℝ → ℝ) (hL : 0 < L)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hv : ContinuousOn v (Icc 0 L)) (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hdv : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x)
    (hdv_cont : ContinuousOn dv (Icc 0 L))
    (hddv : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (hsignal : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0) :
    ∀ x ∈ Icc 0 L,
      v x ≤ nu * (∫ y in (0 : ℝ)..L, u y ^ gamma) / (mu * L) +
        nu * (∫ y in (0 : ℝ)..L, u y ^ gamma) * L ∧
      v x ≤ nu * (∫ y in (0 : ℝ)..L, u y ^ gamma) / (mu * L) +
        2 * nu * (∫ y in (0 : ℝ)..L, u y ^ gamma) * L := by
  set M := ∫ y in (0 : ℝ)..L, u y ^ gamma with hM_def
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg hL.le fun y hy =>
    Real.rpow_nonneg (hu_nonneg y hy) _
  have hgrad := signal_gradient_le L mu nu gamma u v dv ddv hL.le hmu.le hnu hgamma hu hu_nonneg
    hv hv_nonneg hdv_cont hddv hsignal hbc0 hbcL
  have hmass := signal_mass_eq L mu nu gamma u v dv ddv hL.le hgamma hu hv hdv_cont hddv hsignal
    hbc0 hbcL
  obtain ⟨xm, hxm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hv
  have hlow := IntervalMoments.le_integral_of_le hL.le hv (fun z hz => hmin hz)
  have hvm : v xm ≤ nu * M / (mu * L) := by
    rw [le_div_iff₀ (mul_pos hmu hL)]
    nlinarith
  have hlip := abs_sub_le_of_abs_deriv_le hv hdv
    (fun z hz => hgrad z (Ioo_subset_Icc_self hz))
  intro x hx
  have h1 := hlip x hx xm hxm
  have hdist : |x - xm| ≤ L := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hxm.1, hxm.2]
  have h2 : nu * M * |x - xm| ≤ nu * M * L :=
    mul_le_mul_of_nonneg_left hdist (mul_nonneg hnu hM0)
  have h3 : v x - v xm ≤ nu * M * L := (le_abs_self _).trans (h1.trans h2)
  have h4 : 0 ≤ nu * M * L := mul_nonneg (mul_nonneg hnu hM0) hL.le
  constructor <;> nlinarith

/-- **Lemma 4.2(3)**, the `L¹` bound for `v_xx` (TeX line 2982): `v_xx` is
interval integrable on `[0,L]` and `∫_0^L |v_xx| ≤ μ ∫_0^L v + ν M_γ = 2 ν M_γ`. -/
theorem signal_second_L1_le (L mu nu gamma : ℝ) (u v dv ddv : ℝ → ℝ) (hL : 0 ≤ L)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hv : ContinuousOn v (Icc 0 L)) (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hdv_cont : ContinuousOn dv (Icc 0 L))
    (hddv : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (hsignal : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0) :
    IntervalIntegrable ddv volume 0 L ∧
      ∫ x in (0 : ℝ)..L, |ddv x| ≤ 2 * nu * ∫ y in (0 : ℝ)..L, u y ^ gamma := by
  have hw : ContinuousOn (fun x => u x ^ gamma) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr hgamma
  set g : ℝ → ℝ := fun x => mu * v x - nu * u x ^ gamma with hg_def
  have hgc : ContinuousOn g (Icc 0 L) := (hv.const_smul mu).sub (hw.const_smul nu)
  have hEq : EqOn ddv g (Ioo 0 L) := fun x hx => by
    simp only [hg_def]; linarith [hsignal x hx]
  have hint : IntervalIntegrable ddv volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (hgc.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun hEq.symm measurableSet_Ioo
  refine ⟨hint, ?_⟩
  have hcongr : ∫ x in (0 : ℝ)..L, |ddv x| = ∫ x in (0 : ℝ)..L, |g x| := by
    rw [intervalIntegral.integral_of_le hL, intervalIntegral.integral_of_le hL,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [hEq hx]
  rw [hcongr]
  have hmono : ∫ x in (0 : ℝ)..L, |g x| ≤ ∫ x in (0 : ℝ)..L, (mu * v x + nu * u x ^ gamma) :=
    intervalIntegral.integral_mono_on hL (hgc.abs.intervalIntegrable_of_Icc hL)
      (((hv.const_smul mu).add (hw.const_smul nu)).intervalIntegrable_of_Icc hL)
      (fun x hx => by
        have h1 := mul_nonneg hmu (hv_nonneg x hx)
        have h2 := mul_nonneg hnu (Real.rpow_nonneg (hu_nonneg x hx) gamma)
        simp only [hg_def]
        rw [abs_le]; constructor <;> linarith)
  rw [intervalIntegral.integral_add ((hv.intervalIntegrable_of_Icc hL).const_mul mu)
    ((hw.intervalIntegrable_of_Icc hL).const_mul nu), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    signal_mass_eq L mu nu gamma u v dv ddv hL hgamma hu hv hdv_cont hddv hsignal hbc0 hbcL]
    at hmono
  linarith

/-- **Lemma 4.2(3)**, the statement (TeX lines 2927–2928):
`‖v‖_{W^{1,∞}} + ‖v‖_{W^{2,1}} ≤ C M_γ` with the explicit constant
`C = ν (1/(μL) + 2L + 2 + 1/μ + 2L + 2)`, depending only on `μ, ν, L`.
The sup norms are represented by arbitrary points `x, y ∈ [0,L]`; the
`L¹` norms are `∫_0^L |v|`, `∫_0^L |v_x|`, `∫_0^L |v_xx|`. -/
theorem signal_sobolev_le (L mu nu gamma : ℝ) (u v dv ddv : ℝ → ℝ) (hL : 0 < L)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hv : ContinuousOn v (Icc 0 L)) (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hdv : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x)
    (hdv_cont : ContinuousOn dv (Icc 0 L))
    (hddv : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (hsignal : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0) :
    ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L,
      (|v x| + |dv y|) + ((∫ t in (0 : ℝ)..L, |v t|) + (∫ t in (0 : ℝ)..L, |dv t|) +
        ∫ t in (0 : ℝ)..L, |ddv t|) ≤
      nu * (1 / (mu * L) + 2 * L + 2 + 1 / mu + 2 * L + 2) *
        ∫ t in (0 : ℝ)..L, u t ^ gamma := by
  set M := ∫ t in (0 : ℝ)..L, u t ^ gamma with hM_def
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg hL.le fun y hy =>
    Real.rpow_nonneg (hu_nonneg y hy) _
  have hgrad := signal_gradient_le_two L mu nu gamma u v dv ddv hL.le hmu.le hnu hgamma hu
    hu_nonneg hv hv_nonneg hdv_cont hddv hsignal hbc0 hbcL
  have hsup := signal_sup_le L mu nu gamma u v dv ddv hL hmu hnu hgamma hu hu_nonneg hv
    hv_nonneg hdv hdv_cont hddv hsignal hbc0 hbcL
  have hmass := signal_mass_eq L mu nu gamma u v dv ddv hL.le hgamma hu hv hdv_cont hddv
    hsignal hbc0 hbcL
  have hsec := (signal_second_L1_le L mu nu gamma u v dv ddv hL.le hmu.le hnu hgamma hu
    hu_nonneg hv hv_nonneg hdv_cont hddv hsignal hbc0 hbcL).2
  have hv1 : ∫ t in (0 : ℝ)..L, |v t| = nu * M / mu := by
    have : ∫ t in (0 : ℝ)..L, |v t| = ∫ t in (0 : ℝ)..L, v t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hL.le] at ht
      exact abs_of_nonneg (hv_nonneg t ht)
    rw [this, eq_div_iff hmu.ne', mul_comm, hmass]
  have hdv1 : ∫ t in (0 : ℝ)..L, |dv t| ≤ L * (2 * nu * M) :=
    IntervalMoments.integral_le_of_le hL.le hdv_cont.abs hgrad
  intro x hx y hy
  have h1 := (hsup x hx).2
  have h2 := hgrad y hy
  rw [abs_of_nonneg (hv_nonneg x hx), hv1]
  have e1 : nu * M / (mu * L) = nu * (1 / (mu * L)) * M := by ring
  have e2 : nu * M / mu = nu * (1 / mu) * M := by ring
  rw [e1] at h1
  rw [e2]
  nlinarith

/-! ### Lemma 4.2(4)–(5): sup bounds for `u` -/

/-- The chemotactic sensitivity factor is at most `u^m`: for `v ≥ 0`, `β ≥ 0`,
`1/(1+v)^β ≤ 1` (TeX line 2989). -/
theorem sensitivity_le (m beta ux vx : ℝ) (hu : 0 ≤ ux) (hv : 0 ≤ vx) (hbeta : 0 ≤ beta) :
    ux ^ m / (1 + vx) ^ beta ≤ ux ^ m :=
  div_le_self (Real.rpow_nonneg hu m) (Real.one_le_rpow (by linarith) hbeta)

/-- Pointwise flux bound: from `u_x = χ₀ u^m/(1+v)^β v_x` and `|v_x| ≤ K`,
`|u_x| ≤ |χ₀| u^m K`. -/
theorem flux_abs_le (chi0 m beta K ux vx dux dvx : ℝ) (hu : 0 ≤ ux) (hv : 0 ≤ vx)
    (hbeta : 0 ≤ beta) (hflux : dux = chi0 * (ux ^ m / (1 + vx) ^ beta) * dvx)
    (hK : |dvx| ≤ K) : |dux| ≤ |chi0| * ux ^ m * K := by
  have h1 := sensitivity_le m beta ux vx hu hv hbeta
  have h0 : 0 ≤ ux ^ m / (1 + vx) ^ beta :=
    div_nonneg (Real.rpow_nonneg hu m) (Real.rpow_nonneg (by linarith) beta)
  rw [hflux, abs_mul, abs_mul, abs_of_nonneg h0, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul h1 hK (abs_nonneg _) (Real.rpow_nonneg hu m)) (abs_nonneg _)

/-- A point of `[0,L]` where a continuous density with `∫_0^L u = L u*` is at
most `u*` (its minimum point). This replaces the point `y` with `u(y) = u*`
used in TeX lines 2993 and 3005; only `u(y) ≤ u*` is needed. -/
theorem exists_le_mean (L uStar : ℝ) (u : ℝ → ℝ) (hL : 0 < L) (hu : ContinuousOn u (Icc 0 L))
    (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) : ∃ y ∈ Icc 0 L, u y ≤ uStar := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hu
  refine ⟨y, hy, ?_⟩
  have h := IntervalMoments.le_integral_of_le hL.le hu (fun z hz => hmin hz)
  rw [hmass] at h
  exact le_of_mul_le_mul_left h hL

/-- **Lemma 4.2(4)**, TeX `L:minimal-spike-bounds`, lines 2930–2937 and
2987–3000. Let `0 < m < 2`, `β ≥ 0`. Assume `u > 0` is continuous on `[0,L]`
with derivative `u_x` on `(0,L)`, `v ≥ 0`, the flux identity
`u_x = χ₀ u^m/(1+v)^β v_x` on `[0,L]` (Lemma 4.2(1), `MinimalFlux`), the
gradient bound `|v_x| ≤ 2 ν M` of part (3) (with `M = M_γ`, see
`signal_gradient_le_two`), and the mass `∫_0^L u = L u*`. Then, with
`U = ((u*)^(2-m) + 2(2-m)|χ₀| ν L u* M)^(1/(2-m))`, for all `x ∈ [0,L]`:
`u(x)^(2-m) ≤ (u*)^(2-m) + 2(2-m)|χ₀| ν L u* M`, `u(x) ≤ U` and
`|u_x(x)| ≤ 2|χ₀| ν M U^m`. -/
theorem minimal_sup_bounds (L uStar chi0 m beta nu M : ℝ) (u v du dv : ℝ → ℝ)
    (hL : 0 < L) (hm0 : 0 < m) (hm2 : m < 2) (hbeta : 0 ≤ beta)
    (hu : ContinuousOn u (Icc 0 L)) (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hflux : ∀ x ∈ Icc 0 L, du x = chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x)
    (hvx : ∀ x ∈ Icc 0 L, |dv x| ≤ 2 * nu * M)
    (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) :
    ∀ x ∈ Icc 0 L,
      u x ^ (2 - m) ≤ uStar ^ (2 - m) + 2 * (2 - m) * |chi0| * nu * L * uStar * M ∧
      u x ≤ (uStar ^ (2 - m) + 2 * (2 - m) * |chi0| * nu * L * uStar * M) ^ (1 / (2 - m)) ∧
      |du x| ≤ 2 * |chi0| * nu * M *
        ((uStar ^ (2 - m) + 2 * (2 - m) * |chi0| * nu * L * uStar * M) ^ (1 / (2 - m))) ^ m := by
  set p : ℝ := 2 - m with hp_def
  have hp : 0 < p := by rw [hp_def]; linarith
  set c : ℝ := 2 * p * |chi0| * nu * M with hc_def
  have hnuM : 0 ≤ nu * M := by
    have := (abs_nonneg _).trans (hvx 0 ⟨le_rfl, hL.le⟩); linarith
  have hc : 0 ≤ c := by
    have : c = 2 * p * |chi0| * (nu * M) := by rw [hc_def]; ring
    rw [this]; exact mul_nonneg (mul_nonneg (by linarith) (abs_nonneg _)) hnuM
  -- derivative of `u^p` and its bound `|(u^p)_x| ≤ c u`
  set d : ℝ → ℝ := fun x => du x * p * u x ^ (p - 1) with hd_def
  have hd : ∀ x ∈ Ioo 0 L, HasDerivAt (fun y => u y ^ p) (d x) x := fun x hx =>
    (hdu x hx).rpow_const (Or.inl (hu_pos x (Ioo_subset_Icc_self hx)).ne')
  have hdb : ∀ x ∈ Ioo 0 L, |d x| ≤ c * u x := by
    intro x hx
    have hxI := Ioo_subset_Icc_self hx
    have hux := hu_pos x hxI
    have hf := flux_abs_le chi0 m beta (2 * nu * M) (u x) (v x) (du x) (dv x) hux.le
      (hv_nonneg x hxI) hbeta (hflux x hxI) (hvx x hxI)
    have hpow : u x ^ (p - 1) * u x ^ m = u x := by
      rw [← Real.rpow_add hux, hp_def, show (2 - m - 1 + m : ℝ) = 1 by ring, Real.rpow_one]
    have hq : 0 ≤ u x ^ (p - 1) := Real.rpow_nonneg hux.le _
    rw [hd_def]
    simp only
    rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_nonneg hq]
    calc |du x| * p * u x ^ (p - 1)
        ≤ (|chi0| * u x ^ m * (2 * nu * M)) * p * u x ^ (p - 1) := by
          gcongr
      _ = c * (u x ^ (p - 1) * u x ^ m) := by rw [hc_def]; ring
      _ = c * u x := by rw [hpow]
  have hupc : ContinuousOn (fun y => u y ^ p) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr hp.le
  have hPc := continuousOn_primitive hL.le hu
  have hint : interior (Icc (0 : ℝ) L) = Ioo 0 L := interior_Icc
  have hanti : AntitoneOn (fun y => u y ^ p - c * ∫ t in (0 : ℝ)..y, u t) (Icc 0 L) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 L)
      (hupc.sub (hPc.const_smul c)) (f' := fun x => d x - c * u x) ?_ ?_
    · intro x hx; rw [hint] at hx ⊢
      exact ((hd x hx).sub ((hasDerivAt_primitive hu hx).const_mul c)).hasDerivWithinAt
    · intro x hx; rw [hint] at hx
      have := hdb x hx; have := le_abs_self (d x); linarith
  have hmono : MonotoneOn (fun y => u y ^ p + c * ∫ t in (0 : ℝ)..y, u t) (Icc 0 L) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 L)
      (hupc.add (hPc.const_smul c)) (f' := fun x => d x + c * u x) ?_ ?_
    · intro x hx; rw [hint] at hx ⊢
      exact ((hd x hx).add ((hasDerivAt_primitive hu hx).const_mul c)).hasDerivWithinAt
    · intro x hx; rw [hint] at hx
      have := hdb x hx; have := neg_abs_le (d x); linarith
  obtain ⟨y, hy, huy⟩ := exists_le_mean L uStar u hL hu hmass
  have hustar : 0 ≤ uStar := (hu_pos y hy).le.trans huy
  have hupy : u y ^ p ≤ uStar ^ p := Real.rpow_le_rpow (hu_pos y hy).le huy hp.le
  have hu_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x := fun x hx => (hu_pos x hx).le
  have hfirst : ∀ x ∈ Icc 0 L, u x ^ p ≤ uStar ^ p + c * (L * uStar) := by
    intro x hx
    obtain ⟨hPx0, hPxL⟩ := primitive_mem_Icc hu hu_nonneg hx
    obtain ⟨hPy0, hPyL⟩ := primitive_mem_Icc hu hu_nonneg hy
    rw [hmass] at hPxL hPyL
    rcases le_total y x with hyx | hxy
    · have h := hanti hy hx hyx
      simp only at h
      have := mul_le_mul_of_nonneg_left (sub_le_self _ hPy0 |>.trans hPxL) hc
      nlinarith [mul_le_mul_of_nonneg_left hPxL hc, mul_nonneg hc hPy0]
    · have h := hmono hx hy hxy
      simp only at h
      nlinarith [mul_le_mul_of_nonneg_left hPyL hc, mul_nonneg hc hPx0]
  have hR : ∀ x ∈ Icc 0 L, u x ^ p ≤ uStar ^ p + 2 * p * |chi0| * nu * L * uStar * M := by
    intro x hx
    have := hfirst x hx
    have e : c * (L * uStar) = 2 * p * |chi0| * nu * L * uStar * M := by rw [hc_def]; ring
    linarith
  have hU : ∀ x ∈ Icc 0 L,
      u x ≤ (uStar ^ p + 2 * p * |chi0| * nu * L * uStar * M) ^ (1 / p) := by
    intro x hx
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (hu_nonneg x hx) p) (hR x hx)
      (one_div_nonneg.mpr hp.le)
    rw [one_div] at h ⊢
    rwa [Real.rpow_rpow_inv (hu_nonneg x hx) hp.ne'] at h
  intro x hx
  refine ⟨hR x hx, hU x hx, ?_⟩
  have hf := flux_abs_le chi0 m beta (2 * nu * M) (u x) (v x) (du x) (dv x) (hu_nonneg x hx)
    (hv_nonneg x hx) hbeta (hflux x hx) (hvx x hx)
  have hum := Real.rpow_le_rpow (hu_nonneg x hx) (hU x hx) hm0.le
  have h2 : 0 ≤ |chi0| * (2 * nu * M) := mul_nonneg (abs_nonneg _) (by linarith)
  calc |du x| ≤ |chi0| * u x ^ m * (2 * nu * M) := hf
    _ = (|chi0| * (2 * nu * M)) * u x ^ m := by ring
    _ ≤ (|chi0| * (2 * nu * M)) *
        ((uStar ^ p + 2 * p * |chi0| * nu * L * uStar * M) ^ (1 / p)) ^ m :=
          mul_le_mul_of_nonneg_left hum h2
    _ = _ := by ring

/-- **Lemma 4.2(5), the sup bound for `m = 1`**, TeX lines 3001–3010:
`‖u‖_∞ ≤ u* e^{2 X̄ ν M_γ L}` for `|χ₀| ≤ X̄` (the paper's case is
`0 ≤ χ₀ ≤ X̄`). The inputs are those of
`MinimalFlux.minimal_exp_representation`, `v ≥ 0`, `β ≥ 0`, the part (3)
bound `|v_x| ≤ 2 ν M` and the mass `∫_0^L u = L u*`. -/
theorem minimal_exp_sup_bound (L uStar chi0 Xbar beta nu M : ℝ) (u v du dv : ℝ → ℝ)
    (hL : 0 < L) (hbeta : 0 ≤ beta) (hchi : |chi0| ≤ Xbar)
    (hu_cont : ContinuousOn u (Icc 0 L)) (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hflux : ∀ x ∈ Ioo 0 L, du x = chi0 * (u x / (1 + v x) ^ beta) * dv x)
    (hg_cont : ContinuousOn (fun y => chi0 * dv y / (1 + v y) ^ beta) (Icc 0 L))
    (hv_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hvx : ∀ x ∈ Icc 0 L, |dv x| ≤ 2 * nu * M)
    (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) :
    ∀ x ∈ Icc 0 L, u x ≤ uStar * Real.exp (2 * Xbar * nu * M * L) := by
  have hnuM : 0 ≤ nu * M := by
    have := (abs_nonneg _).trans (hvx 0 ⟨le_rfl, hL.le⟩); linarith
  have hX : 0 ≤ Xbar := (abs_nonneg _).trans hchi
  have hC : 0 ≤ Xbar * (2 * nu * M) := mul_nonneg hX (by linarith)
  have hrep := MinimalFlux.minimal_exp_representation L chi0 beta u v du dv hu_cont hu_pos hdu
    hflux hg_cont
  obtain ⟨y, hy, huy⟩ := exists_le_mean L uStar u hL hu_cont hmass
  intro x hx
  have hgb : ∀ t ∈ Ι y x, ‖chi0 * dv t / (1 + v t) ^ beta‖ ≤ Xbar * (2 * nu * M) := by
    intro t ht
    have htI : t ∈ Icc 0 L := uIcc_subset_Icc hy hx (uIoc_subset_uIcc ht)
    have hden : 1 ≤ (1 + v t) ^ beta := Real.one_le_rpow (by linarith [hv_nonneg t htI]) hbeta
    rw [Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos (by linarith [hv_nonneg t htI] : (0 : ℝ) < 1 + v t) beta)]
    calc |chi0| * |dv t| / (1 + v t) ^ beta ≤ |chi0| * |dv t| :=
          div_le_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hden
      _ ≤ Xbar * (2 * nu * M) := mul_le_mul hchi (hvx t htI) (abs_nonneg _) hX
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hgb
  rw [Real.norm_eq_abs] at hI
  have hdist : |x - y| ≤ L := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hexp : (∫ t in y..x, chi0 * dv t / (1 + v t) ^ beta) ≤ 2 * Xbar * nu * M * L := by
    have := mul_le_mul_of_nonneg_left hdist hC
    have := le_abs_self (∫ t in y..x, chi0 * dv t / (1 + v t) ^ beta)
    nlinarith
  rw [hrep y hy x hx]
  exact mul_le_mul huy (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
    ((hu_pos y hy).le.trans huy)

end ChemotaxisBifurcation.SpikeEstimates
