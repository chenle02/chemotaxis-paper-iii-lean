module
public import ChemotaxisBifurcation.StationaryMassBounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Interval moments for stationary densities (Lemma 4.1(1), Lemma 4.2(2))

`StationaryMassBounds` proves Jensen and strict Jensen on an abstract finite
measure. This file applies them on the actual reference measure of `[0,L]`
(Lebesgue measure restricted to `Icc 0 L`, total mass `L`) to densities that
are continuous and positive on `[0,L]`, and states the conclusions with the
manuscript's integrals `∫_0^L`.

The passage from continuous nonconstancy to a.e. nonconstancy is proved here,
as are the strict minimum/maximum comparisons with `u*`. Each theorem keeps
the PDE input it consumes as a hypothesis: the logistic mass identity
(TeX `E:mass-identity`) in the non-minimal model, and the prescribed mass
`∫_0^L u = L u*` in the minimal model. Stationarity, the boundary conditions
and the regularity of the solution are not proved here.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.IntervalMoments

open MeasureTheory Set

/-- The reference measure of `[0,L]`: Lebesgue measure restricted to `Icc 0 L`. -/
noncomputable abbrev intervalMeasure (L : ℝ) : Measure ℝ := volume.restrict (Icc 0 L)

theorem intervalMeasure_real_univ {L : ℝ} (hL : 0 ≤ L) :
    (intervalMeasure L).real univ = L := by
  simp [Measure.real, hL]

theorem intervalMeasure_neZero {L : ℝ} (hL : 0 < L) : NeZero (intervalMeasure L) := by
  refine ⟨fun h => ?_⟩
  have h1 := intervalMeasure_real_univ hL.le
  rw [h] at h1
  simp at h1
  exact hL.ne h1

/-- Integrals against the reference measure are the manuscript's `∫_0^L`. -/
theorem integral_eq_intervalIntegral {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℝ) :
    ∫ x, f x ∂intervalMeasure L = ∫ x in (0 : ℝ)..L, f x := by
  rw [intervalIntegral.integral_of_le hL, integral_Icc_eq_integral_Ioc]

theorem integrable_of_continuousOn {L : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 L)) :
    Integrable f (intervalMeasure L) :=
  hf.integrableOn_Icc

/-- A continuous function on `[0,L]`, `L > 0`, that is a.e. equal to a
constant is that constant at every point of `[0,L]`. -/
theorem eqOn_of_ae_eq_const {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (c : ℝ)
    (hf : ContinuousOn f (Icc 0 L)) (h : f =ᵐ[intervalMeasure L] Function.const ℝ c) :
    ∀ x ∈ Icc 0 L, f x = c :=
  fun _ hx => Measure.eqOn_Icc_of_ae_eq volume hL.ne h hf continuousOn_const hx

/-- Continuous nonconstancy on `[0,L]` gives a.e. nonconstancy for the
reference measure, the hypothesis strict Jensen needs. -/
theorem not_ae_eq_const {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 L))
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, f x ≠ f y) (c : ℝ) :
    ¬ f =ᵐ[intervalMeasure L] Function.const ℝ c := by
  intro h
  obtain ⟨x, hx, y, hy, hxy⟩ := hnonconst
  have he := eqOn_of_ae_eq_const hL c hf h
  exact hxy ((he x hx).trans (he y hy).symm)

/-- A continuous nonnegative function on `[0,L]` with zero integral vanishes
on all of `[0,L]`. -/
theorem eq_zero_of_integral_eq_zero {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 L)) (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ g x)
    (hint : ∫ x in (0 : ℝ)..L, g x = 0) :
    ∀ x ∈ Icc 0 L, g x = 0 := by
  rw [← integral_eq_intervalIntegral hL.le] at hint
  have hae : g =ᵐ[intervalMeasure L] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Icc hnonneg)
      (integrable_of_continuousOn hg)).mp hint
  exact eqOn_of_ae_eq_const hL 0 hg hae

/-- The integral over `[0,L]` of a continuous function bounded below by `c`
on `[0,L]` is at least `L c`. -/
theorem le_integral_of_le {L c : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 L)) (h : ∀ x ∈ Icc 0 L, c ≤ f x) :
    L * c ≤ ∫ x in (0 : ℝ)..L, f x := by
  have := intervalIntegral.integral_mono_on hL (intervalIntegrable_const (μ := volume))
    (hf.intervalIntegrable_of_Icc hL) h
  simpa using this

/-- The integral over `[0,L]` of a continuous function bounded above by `c`
on `[0,L]` is at most `L c`. -/
theorem integral_le_of_le {L c : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 L)) (h : ∀ x ∈ Icc 0 L, f x ≤ c) :
    ∫ x in (0 : ℝ)..L, f x ≤ L * c := by
  have := intervalIntegral.integral_mono_on hL (hf.intervalIntegrable_of_Icc hL)
    (intervalIntegrable_const (μ := volume)) h
  simpa using this

/-- Strict Jensen on `[0,L]`, in the manuscript's form
`(∫_0^L u)^p < L^(p-1) ∫_0^L u^p`, for continuous nonnegative nonconstant `u`. -/
theorem strict_power_integral {L p : ℝ} (hL : 0 < L) (hp : 1 < p) {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Icc 0 L)) (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y) :
    (∫ x in (0 : ℝ)..L, u x) ^ p < L ^ (p - 1) * ∫ x in (0 : ℝ)..L, u x ^ p := by
  have hpow : ContinuousOn (fun x => u x ^ p) (Icc 0 L) :=
    hcont.rpow_const fun _ _ => Or.inr (by linarith)
  have h := StationaryMassBounds.strict_power_average (intervalMeasure L) u p hp
    (ae_restrict_of_forall_mem measurableSet_Icc hnonneg)
    (integrable_of_continuousOn hcont) (integrable_of_continuousOn hpow)
    (not_ae_eq_const hL hcont hnonconst _)
  rw [average_eq, average_eq, intervalMeasure_real_univ hL.le,
    integral_eq_intervalIntegral hL.le, integral_eq_intervalIntegral hL.le,
    smul_eq_mul, smul_eq_mul] at h
  have hI : 0 ≤ ∫ x in (0 : ℝ)..L, u x :=
    intervalIntegral.integral_nonneg hL.le hnonneg
  have hLinv : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
  have key : (∫ x in (0 : ℝ)..L, u x) ^ p =
      L ^ p * (L⁻¹ * ∫ x in (0 : ℝ)..L, u x) ^ p := by
    rw [Real.mul_rpow hLinv hI, ← mul_assoc, ← Real.mul_rpow hL.le hLinv,
      mul_inv_cancel₀ hL.ne', Real.one_rpow, one_mul]
  calc (∫ x in (0 : ℝ)..L, u x) ^ p
      = L ^ p * (L⁻¹ * ∫ x in (0 : ℝ)..L, u x) ^ p := key
    _ < L ^ p * (L⁻¹ * ∫ x in (0 : ℝ)..L, u x ^ p) :=
        mul_lt_mul_of_pos_left h (Real.rpow_pos_of_pos hL p)
    _ = L ^ (p - 1) * ∫ x in (0 : ℝ)..L, u x ^ p := by
        rw [Real.rpow_sub_one hL.ne']
        field_simp

/-- A continuous function on `[0,L]` that lies above `c` there and has
integral `L c` is identically `c` on `[0,L]`. -/
theorem eqOn_const_of_le_of_integral_eq {L c : ℝ} (hL : 0 < L) {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Icc 0 L)) (hle : ∀ x ∈ Icc 0 L, c ≤ u x)
    (hint : ∫ x in (0 : ℝ)..L, u x = L * c) :
    ∀ x ∈ Icc 0 L, u x = c := by
  have hzero := eq_zero_of_integral_eq_zero hL (g := fun x => u x - c)
    (hcont.sub continuousOn_const) (fun x hx => sub_nonneg.mpr (hle x hx)) (by
      rw [intervalIntegral.integral_sub (hcont.intervalIntegrable_of_Icc hL.le)
        intervalIntegrable_const, hint, intervalIntegral.integral_const, smul_eq_mul]
      ring)
  exact fun x hx => sub_eq_zero.mp (hzero x hx)

/-- The mirror statement: below `c` with integral `L c` forces `u = c`. -/
theorem eqOn_const_of_ge_of_integral_eq {L c : ℝ} (hL : 0 < L) {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Icc 0 L)) (hge : ∀ x ∈ Icc 0 L, u x ≤ c)
    (hint : ∫ x in (0 : ℝ)..L, u x = L * c) :
    ∀ x ∈ Icc 0 L, u x = c := by
  have h := eqOn_const_of_le_of_integral_eq hL (c := -c) (u := fun x => -u x) hcont.neg
    (fun x hx => neg_le_neg (hge x hx)) (by
      rw [intervalIntegral.integral_neg, hint]; ring)
  exact fun x hx => neg_injective (h x hx)

/-- **Lemma 4.1(1)**, TeX `L:spiky-solu-lm1`, display `E:bound-u-eq1-2`.

For `a, b, α > 0` and `u* = (a/b)^(1/α)`, a continuous, positive and
nonconstant density on `[0,L]` that satisfies the logistic mass identity
`a ∫_0^L u = b ∫_0^L u^(1+α)` (TeX `E:mass-identity`, the PDE input) obeys
`0 < min u < u* < max u`, `∫_0^L u < L u*` and
`∫_0^L u^(1+α) < L (u*)^(1+α)`. -/
theorem logistic_interval_bounds
    (a b alpha L : ℝ) (u : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y)
    (hmass : a * ∫ x in (0 : ℝ)..L, u x = b * ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha)) :
    (∃ x₀ ∈ Icc 0 L, IsMinOn u (Icc 0 L) x₀ ∧ 0 < u x₀ ∧
        u x₀ < (a / b) ^ (1 / alpha)) ∧
      (∃ x₁ ∈ Icc 0 L, IsMaxOn u (Icc 0 L) x₁ ∧ (a / b) ^ (1 / alpha) < u x₁) ∧
      ∫ x in (0 : ℝ)..L, u x < L * (a / b) ^ (1 / alpha) ∧
      ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) < L * ((a / b) ^ (1 / alpha)) ^ (1 + alpha) := by
  set uStar := (a / b) ^ (1 / alpha) with huStar_def
  have hab : 0 < a / b := div_pos ha hb
  have huStar : 0 < uStar := Real.rpow_pos_of_pos hab _
  have hequil : uStar ^ alpha = a / b := by
    rw [huStar_def, one_div, Real.rpow_inv_rpow hab.le halpha.ne']
  have hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x := fun x hx => (hpos x hx).le
  have hI : 0 < ∫ x in (0 : ℝ)..L, u x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable_of_Icc hL.le)
      (fun x hx => hpos x (Ioo_subset_Icc_self hx)) hL
  have hstrict := strict_power_integral hL (by linarith : (1 : ℝ) < 1 + alpha) hcont hnonneg
    hnonconst
  rw [add_sub_cancel_left] at hstrict
  obtain ⟨hImean, hJ⟩ := StationaryMassBounds.logistic_moment_bounds a b L alpha uStar _ _
    hb hL halpha huStar hI hequil hmass hstrict
  refine ⟨?_, ?_, hImean, hJ⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hcont
    refine ⟨x₀, hx₀, hmin, hpos x₀ hx₀, ?_⟩
    by_contra hge
    rw [not_lt] at hge
    have := le_integral_of_le hL.le hcont (fun x hx => hge.trans (hmin hx))
    linarith
  · obtain ⟨x₁, hx₁, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hL.le) hcont
    refine ⟨x₁, hx₁, hmax, ?_⟩
    by_contra hle
    rw [not_lt] at hle
    have hle' : ∀ x ∈ Icc 0 L, u x ≤ uStar := fun x hx => (hmax hx).trans hle
    have hg_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x * (uStar ^ alpha - u x ^ alpha) := fun x hx =>
      mul_nonneg (hnonneg x hx)
        (sub_nonneg.mpr (Real.rpow_le_rpow (hnonneg x hx) (hle' x hx) halpha.le))
    have hg_cont : ContinuousOn (fun x => u x * (uStar ^ alpha - u x ^ alpha)) (Icc 0 L) :=
      hcont.mul (continuousOn_const.sub (hcont.rpow_const fun _ _ => Or.inr halpha.le))
    have hpowc : ContinuousOn (fun x => u x ^ (1 + alpha)) (Icc 0 L) :=
      hcont.rpow_const fun _ _ => Or.inr (by linarith)
    have hg_int : ∫ x in (0 : ℝ)..L, u x * (uStar ^ alpha - u x ^ alpha) = 0 := by
      have e1 : ∫ x in (0 : ℝ)..L, u x * (uStar ^ alpha - u x ^ alpha) =
          ∫ x in (0 : ℝ)..L, (uStar ^ alpha * u x - u x ^ (1 + alpha)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hL.le] at hx
        simp only [Real.rpow_add (hpos x hx), Real.rpow_one]
        ring
      rw [e1, intervalIntegral.integral_sub
        ((hcont.intervalIntegrable_of_Icc hL.le).const_mul _)
        (hpowc.intervalIntegrable_of_Icc hL.le), intervalIntegral.integral_const_mul, hequil]
      have : a / b * ∫ x in (0 : ℝ)..L, u x = ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) := by
        field_simp
        linarith
      linarith
    have hzero := eq_zero_of_integral_eq_zero hL hg_cont hg_nonneg hg_int
    have hconst : ∀ x ∈ Icc 0 L, u x = uStar := by
      intro x hx
      have h0 := hzero x hx
      have hfac : uStar ^ alpha - u x ^ alpha = 0 :=
        (mul_eq_zero.mp h0).resolve_left (hpos x hx).ne'
      by_contra hne
      have hlt : u x < uStar := lt_of_le_of_ne (hle' x hx) hne
      have := Real.rpow_lt_rpow (hnonneg x hx) hlt halpha
      linarith
    obtain ⟨x, hx, y, hy, hxy⟩ := hnonconst
    exact hxy ((hconst x hx).trans (hconst y hy).symm)

/-- **Lemma 4.2(2)**, TeX `L:minimal-spike-bounds`.

In the minimal model the PDE input is the prescribed mass
`∫_0^L u = L u*`. A continuous, positive and nonconstant density on `[0,L]`
with that mass obeys `0 < min u < u* < max u` and `∫_0^L u² > L (u*)²`. -/
theorem minimal_interval_bounds
    (L uStar : ℝ) (u : ℝ → ℝ) (hL : 0 < L)
    (hcont : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y)
    (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) :
    (∃ x₀ ∈ Icc 0 L, IsMinOn u (Icc 0 L) x₀ ∧ 0 < u x₀ ∧ u x₀ < uStar) ∧
      (∃ x₁ ∈ Icc 0 L, IsMaxOn u (Icc 0 L) x₁ ∧ uStar < u x₁) ∧
      L * uStar ^ 2 < ∫ x in (0 : ℝ)..L, u x ^ 2 := by
  have hnc := hnonconst
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hcont
    refine ⟨x₀, hx₀, hmin, hpos x₀ hx₀, ?_⟩
    by_contra hge
    rw [not_lt] at hge
    have hc := eqOn_const_of_le_of_integral_eq hL hcont (fun z hz => hge.trans (hmin hz)) hmass
    exact hxy ((hc x hx).trans (hc y hy).symm)
  · obtain ⟨x₁, hx₁, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hL.le) hcont
    refine ⟨x₁, hx₁, hmax, ?_⟩
    by_contra hle
    rw [not_lt] at hle
    have hc := eqOn_const_of_ge_of_integral_eq hL hcont (fun z hz => (hmax hz).trans hle) hmass
    exact hxy ((hc x hx).trans (hc y hy).symm)
  · have h := strict_power_integral hL (by norm_num : (1 : ℝ) < 2) hcont
      (fun z hz => (hpos z hz).le) hnonconst
    simp only [Real.rpow_two] at h
    norm_num at h
    rw [hmass] at h
    have h' : L * (L * uStar ^ 2) < L * ∫ x in (0 : ℝ)..L, u x ^ 2 := by
      nlinarith
    exact lt_of_mul_lt_mul_left h' hL.le

/-- The Jensen step of Lemma 4.2 (TeX lines 3002 and 3331–3334): with the
prescribed mass `∫_0^L u = L u*` and `0 ≤ γ ≤ 1`, `∫_0^L u^γ ≤ L (u*)^γ`. -/
theorem minimal_power_integral_le
    (L uStar gamma : ℝ) (u : ℝ → ℝ) (hL : 0 < L)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hcont : ContinuousOn u (Icc 0 L)) (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) :
    ∫ x in (0 : ℝ)..L, u x ^ gamma ≤ L * uStar ^ gamma := by
  have := intervalMeasure_neZero hL
  have h := StationaryMassBounds.fixed_mass_power_integral (intervalMeasure L) u L gamma uStar
    hL (intervalMeasure_real_univ hL.le) hgamma0 hgamma1
    (ae_restrict_of_forall_mem measurableSet_Icc hnonneg)
    (integrable_of_continuousOn hcont)
    (integrable_of_continuousOn (hcont.rpow_const fun _ _ => Or.inr hgamma0))
    (by rw [integral_eq_intervalIntegral hL.le]; exact hmass)
  rwa [integral_eq_intervalIntegral hL.le] at h

/-- The first estimate in the proof of Lemma 4.1(2) (TeX lines 2832–2833):
for `0 < γ ≤ 1 + α`, the moment bound `∫_0^L u^(1+α) ≤ L (u*)^(1+α)` of
part (1) gives `∫_0^L u^γ ≤ L (u*)^γ`. This is Jensen for the concave power
`t ↦ t^(γ/(1+α))` applied to `u^(1+α)`. -/
theorem logistic_power_integral_le
    (L uStar alpha gamma : ℝ) (u : ℝ → ℝ) (hL : 0 < L) (halpha : 0 < alpha)
    (huStar : 0 ≤ uStar) (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1 + alpha)
    (hcont : ContinuousOn u (Icc 0 L)) (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha)) :
    ∫ x in (0 : ℝ)..L, u x ^ gamma ≤ L * uStar ^ gamma := by
  have := intervalMeasure_neZero hL
  have hp : 0 < 1 + alpha := by linarith
  set s := gamma / (1 + alpha) with hs_def
  have hs0 : 0 ≤ s := div_nonneg hgamma0.le hp.le
  have hs1 : s ≤ 1 := (div_le_one hp).mpr hgamma1
  have hsp : (1 + alpha) * s = gamma := by rw [hs_def]; field_simp
  set w : ℝ → ℝ := fun x => u x ^ (1 + alpha) with hw_def
  have hwcont : ContinuousOn w (Icc 0 L) := hcont.rpow_const fun _ _ => Or.inr hp.le
  have hwnonneg : ∀ x ∈ Icc 0 L, 0 ≤ w x := fun x hx => Real.rpow_nonneg (hnonneg x hx) _
  have hws : ∀ x ∈ Icc 0 L, w x ^ s = u x ^ gamma := fun x hx => by
    rw [hw_def, ← Real.rpow_mul (hnonneg x hx), hsp]
  have hwscont : ContinuousOn (fun x => w x ^ s) (Icc 0 L) :=
    hwcont.rpow_const fun _ _ => Or.inr hs0
  have hjensen := (Real.concaveOn_rpow hs0 hs1).le_map_average
    (Real.continuous_rpow_const hs0).continuousOn isClosed_Ici
    (ae_restrict_of_forall_mem measurableSet_Icc hwnonneg)
    (integrable_of_continuousOn hwcont) (integrable_of_continuousOn hwscont)
  have hLinv : 0 < L⁻¹ := inv_pos.mpr hL
  simp only [average_eq, intervalMeasure_real_univ hL.le, smul_eq_mul] at hjensen
  rw [integral_eq_intervalIntegral hL.le, integral_eq_intervalIntegral hL.le] at hjensen
  have hJ0 : 0 ≤ ∫ x in (0 : ℝ)..L, w x := intervalIntegral.integral_nonneg hL.le hwnonneg
  have hmean : L⁻¹ * ∫ x in (0 : ℝ)..L, w x ≤ uStar ^ (1 + alpha) := by
    rw [inv_mul_le_iff₀ hL]
    exact hmoment
  have hpow := Real.rpow_le_rpow (mul_nonneg hLinv.le hJ0) hmean hs0
  rw [← Real.rpow_mul huStar, hsp] at hpow
  have hcongr : ∫ x in (0 : ℝ)..L, w x ^ s = ∫ x in (0 : ℝ)..L, u x ^ gamma := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hL.le] at hx
    exact hws x hx
  have h := hjensen.trans hpow
  rw [hcongr, inv_mul_le_iff₀ hL] at h
  exact h

end ChemotaxisBifurcation.IntervalMoments
