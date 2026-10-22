module
public import ChemotaxisBifurcation.SpikeLimit
public import ChemotaxisBifurcation.IntervalMoments
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Topology.MetricSpace.Sequences

@[expose] public section

/-!
# Spike-like stationary solutions (Theorem 1.4)

This file proves the deductions in the proof of Theorem 1.4 (TeX
`T:spiky-solu-thm`, statement lines 962–985, proof lines 3480–3556 of the
October 8 manuscript) once the analytic inputs are granted.

The analytic input is one hypothesis, `hcompact` in
`spike_gradient_blowup`: along every subsequence with gradients bounded on a
subinterval `[a,b]` and uniformly bounded values, a further subsequence
converges uniformly on `[a,b]` (Arzelà–Ascoli, TeX line 3527) and
`u_n^γ ⇀ c` weakly in `L^q` for a constant `c` (Lemma 5.1, TeX lines
3519–3526; its deduction is `SpikeLimit.minimal_spike_limit`), the weak
convergence being tested on intervals. The positivity, mass bound, maximum
points and derivatives of each `u_n` are hypotheses as well.

What is proved here:

* the sup bound `max u_n ≤ L u*/|I| + K |I|` from a gradient bound on `I`
  (`E:unif-bound-u-n`, TeX lines 3497–3502);
* the identification `U^γ = c` on `I`, `U(x*) = ℓ`, `c = ℓ^γ`
  (TeX lines 3527–3533), and the contradiction with `∫ u_n ≤ L u*` and
  `ℓ > u*` (TeX lines 3534–3539). The manuscript passes through
  `u_n^γ → ℓ^γ` in `L¹`; here the contradiction is reached directly from
  `∫ u_n^γ → L ℓ^γ`, by Jensen (`γ ≤ 1`) or by `u_n^γ ≤ h_n^{γ-1} u_n`
  (`γ > 1`);
* the subsequence bookkeeping of TeX lines 3486–3516 (compactness of `[0,L]`
  for `x_n → x*`, Bolzano–Weierstrass for `h_n → ℓ`), giving
  `E:spiky-thm-eq2` in the form "for every `δ > 0` and `K`, eventually
  `|u_x| > K` somewhere in `I`";
* `E:spiky-thm-eq3`'s constant bound `0 ≤ c ≤ (u*)^γ` (TeX lines 3546–3553)
  and the exponent arithmetic `q = (1+α)/γ > 1`, `1 + α > max{1, γ}`;
* the relabeling remark (TeX lines 3554–3555): further subsequences keep
  `E:spiky-thm-eq2`.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.SpikeLimit

open Set Filter Topology MeasureTheory
open scoped Interval

/-! ### The sup bound from a local gradient bound -/

/-- **Theorem 1.4, `E:unif-bound-u-n`** (TeX lines 3497–3502). Let `u ≥ 0`
be continuous on `[0,L]` with `∫_0^L u ≤ L u*`, let `[a,b] ⊆ [0,L]`,
`a < b`, and let `|u_x| ≤ K` on `(a,b)`. Then every `x₀ ∈ [a,b]` satisfies
`u(x₀) ≤ L u*/(b-a) + K (b-a)`. -/
theorem le_of_local_gradient_bound {L a b K uStar : ℝ} {u du : ℝ → ℝ} {x₀ : ℝ}
    (hab : a < b) (habL : Icc a b ⊆ Icc 0 L) (hu : ContinuousOn u (Icc 0 L))
    (hu0 : ∀ y ∈ Icc 0 L, 0 ≤ u y) (hdu : ∀ y ∈ Ioo a b, HasDerivAt u (du y) y)
    (hK : ∀ y ∈ Ioo a b, |du y| ≤ K) (hx₀ : x₀ ∈ Icc a b)
    (hmass : ∫ y in (0 : ℝ)..L, u y ≤ L * uStar) :
    u x₀ ≤ L * uStar / (b - a) + K * (b - a) := by
  have hL : 0 ≤ L := (habL (left_mem_Icc.mpr hab.le)).1.trans (habL (left_mem_Icc.mpr hab.le)).2
  have hcab : ContinuousOn u (Icc a b) := hu.mono habL
  -- Lipschitz bound on `[a,b]`
  have hlip : ∀ y ∈ Icc a b, u x₀ - u y ≤ K * (b - a) := by
    intro y hy
    have key : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, t < s → |u s - u t| ≤ K * (s - t) := by
      intro s hs t ht hts
      obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope u du hts
        (hcab.mono (Icc_subset_Icc ht.1 hs.2))
        (fun z hz => hdu z ⟨ht.1.trans_lt hz.1, hz.2.trans_le hs.2⟩)
      have hpos : 0 < s - t := sub_pos.mpr hts
      have heq : u s - u t = du c * (s - t) := by rw [hslope]; field_simp
      rw [heq, abs_mul, abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_right (hK c ⟨ht.1.trans_lt hc.1, hc.2.trans_le hs.2⟩) hpos.le
    have hK0 : 0 ≤ K := by
      have := hK ((a + b) / 2) ⟨by linarith, by linarith⟩
      exact (abs_nonneg _).trans this
    rcases lt_trichotomy y x₀ with h | h | h
    · have := key x₀ hx₀ y hy h
      have := le_abs_self (u x₀ - u y)
      nlinarith [hy.1, hx₀.2]
    · rw [h, sub_self]; exact mul_nonneg hK0 (by linarith)
    · have := key y hy x₀ hx₀ h
      have := neg_abs_le (u y - u x₀)
      nlinarith [hx₀.1, hy.2]
  -- integrate over `[a,b]`
  have hint : (b - a) * (u x₀ - K * (b - a)) ≤ ∫ y in a..b, u y := by
    have h := intervalIntegral.integral_mono_on hab.le
      (intervalIntegrable_const (μ := volume) (c := u x₀ - K * (b - a)))
      (hcab.intervalIntegrable_of_Icc hab.le) (fun y hy => by linarith [hlip y hy])
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h
  have hsub : ∫ y in a..b, u y ≤ ∫ y in (0 : ℝ)..L, u y := by
    refine intervalIntegral.integral_mono_interval (habL (left_mem_Icc.mpr hab.le)).1 hab.le
      (habL (right_mem_Icc.mpr hab.le)).2 ?_ (hu.intervalIntegrable_of_Icc hL)
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Eventually.of_forall fun y hy => hu0 y (Ioc_subset_Icc_self hy))
  have hba : 0 < b - a := sub_pos.mpr hab
  rw [div_add' _ _ _ hba.ne', le_div_iff₀ hba]
  nlinarith

/-! ### Power moments under the mass bound -/

/-- The concavity step for `0 < γ ≤ 1` (Jensen): if `u ≥ 0` is continuous on
`[0,L]` and `∫_0^L u ≤ L u*` with `u* > 0`, then `∫_0^L u^γ ≤ L (u*)^γ`. -/
theorem power_integral_le_of_le_one {L uStar gamma : ℝ} {u : ℝ → ℝ} (hL : 0 ≤ L)
    (huStar : 0 < uStar) (hγ : 0 < gamma) (hγ1 : gamma ≤ 1)
    (hu : ContinuousOn u (Icc 0 L)) (hu0 : ∀ y ∈ Icc 0 L, 0 ≤ u y)
    (hmass : ∫ y in (0 : ℝ)..L, u y ≤ L * uStar) :
    ∫ y in (0 : ℝ)..L, u y ^ gamma ≤ L * uStar ^ gamma := by
  set A : ℝ := uStar ^ gamma
  have hA : 0 ≤ A := Real.rpow_nonneg huStar.le _
  -- tangent line of the concave power at `u*`
  have htan : ∀ y ∈ Icc 0 L, u y ^ gamma ≤ A + gamma * A * (u y / uStar - 1) := by
    intro y hy
    have hs : -1 ≤ u y / uStar - 1 := by
      have := div_nonneg (hu0 y hy) huStar.le; linarith
    have h := rpow_one_add_le_one_add_mul_self hs hγ.le hγ1
    rw [add_sub_cancel] at h
    have heq : u y ^ gamma = A * (u y / uStar) ^ gamma := by
      rw [Real.div_rpow (hu0 y hy) huStar.le]
      field_simp [(Real.rpow_pos_of_pos huStar gamma).ne']
      rfl
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left h hA]
  have hcu : IntervalIntegrable u volume 0 L := hu.intervalIntegrable_of_Icc hL
  have hmono := intervalIntegral.integral_mono_on hL
    ((hu.rpow_const fun _ _ => Or.inr hγ.le).intervalIntegrable_of_Icc hL)
    ((intervalIntegrable_const).add
      (((hcu.div_const uStar).sub intervalIntegrable_const).const_mul (gamma * A))) htan
  rw [intervalIntegral.integral_add intervalIntegrable_const
      (((hcu.div_const uStar).sub intervalIntegrable_const).const_mul (gamma * A)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hcu.div_const uStar) intervalIntegrable_const,
    intervalIntegral.integral_div, intervalIntegral.integral_const,
    intervalIntegral.integral_const] at hmono
  simp only [sub_zero, smul_eq_mul, mul_one] at hmono
  have hle : (∫ y in (0 : ℝ)..L, u y) / uStar - L ≤ 0 := by
    rw [sub_nonpos, div_le_iff₀ huStar]; linarith
  have hγA : 0 ≤ gamma * A := mul_nonneg hγ.le hA
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hγA hle]

/-- The step for `γ ≥ 1`: if `0 ≤ u ≤ h` on `[0,L]` and `∫_0^L u ≤ L u*`, then
`∫_0^L u^γ ≤ h^{γ-1} L u*`, since `u^γ ≤ h^{γ-1} u`. -/
theorem power_integral_le_of_one_le {L uStar gamma h : ℝ} {u : ℝ → ℝ} (hL : 0 ≤ L)
    (hγ1 : 1 ≤ gamma) (hu : ContinuousOn u (Icc 0 L)) (hu0 : ∀ y ∈ Icc 0 L, 0 ≤ u y)
    (huh : ∀ y ∈ Icc 0 L, u y ≤ h) (hmass : ∫ y in (0 : ℝ)..L, u y ≤ L * uStar) :
    ∫ y in (0 : ℝ)..L, u y ^ gamma ≤ h ^ (gamma - 1) * (L * uStar) := by
  have hpt : ∀ y ∈ Icc 0 L, u y ^ gamma ≤ h ^ (gamma - 1) * u y := by
    intro y hy
    rcases eq_or_lt_of_le (hu0 y hy) with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith)]
      exact le_of_eq (by ring)
    have hsplit : u y ^ gamma = u y ^ (gamma - 1) * u y := by
      rw [Real.rpow_sub_one hpos.ne']; field_simp
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hpos.le (huh y hy) (by linarith)) hpos.le
  have hmono := intervalIntegral.integral_mono_on hL
    ((hu.rpow_const fun _ _ => Or.inr (by linarith)).intervalIntegrable_of_Icc hL)
    ((hu.intervalIntegrable_of_Icc (μ := volume) hL).const_mul (h ^ (gamma - 1))) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have hh0 : 0 ≤ h := (hu0 0 (left_mem_Icc.mpr hL)).trans (huh 0 (left_mem_Icc.mpr hL))
  exact hmono.trans (mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hh0 _))

/-! ### The contradiction (TeX lines 3527–3539) -/

/-- A continuous `g` on `[a,b]`, `a < b`, with `∫_a^q g = c (q-a)` for every
`q ∈ [a,b]` equals `c` on `[a,b]`. -/
theorem eqOn_const_of_integral_eq {a b c : ℝ} {g : ℝ → ℝ} (hab : a < b)
    (hg : ContinuousOn g (Icc a b))
    (hint : ∀ q ∈ Icc a b, ∫ y in a..q, g y = c * (q - a)) :
    ∀ y ∈ Icc a b, g y = c := by
  have hIoo : EqOn g (fun _ => c) (Ioo a b) := by
    intro y hy
    have hcont : ContinuousAt g y := hg.continuousAt (Icc_mem_nhds hy.1 hy.2)
    have hmeas : StronglyMeasurableAtFilter g (𝓝 y) volume :=
      (hg.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo y hy
    have hd := intervalIntegral.integral_hasDerivAt_right
      ((hg.mono (Icc_subset_Icc le_rfl hy.2.le)).intervalIntegrable_of_Icc hy.1.le) hmeas hcont
    have hd' : HasDerivAt (fun q => ∫ y in a..q, g y) c y := by
      have h1 : HasDerivAt (fun q => c * (q - a)) c y := by
        simpa using ((hasDerivAt_id y).sub_const a).const_mul c
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hy.1 hy.2] with q hq
      exact hint q (Ioo_subset_Icc_self hq)
    exact hd.unique hd'
  have h := hIoo.of_subset_closure hg continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])
  exact fun y hy => h hy

/-- **Theorem 1.4, the contradiction in the proof of `E:spiky-thm-eq2`**
(TeX lines 3527–3539). Along one sequence, let `u_n ≥ 0` be continuous on
`[0,L]` with `∫_0^L u_n ≤ L u*`, `u* > 0`, maximum points `x_n → x*`
and maxima `h_n = u_n(x_n) → ℓ > u*`. Let `[a,b] ⊆ [0,L]`, `a < b`, contain
`x_n` eventually. Assume the analytic inputs: `u_n → U` uniformly on
`[a,b]` with `U` continuous (Arzelà–Ascoli), and `∫_p^q u_n^γ → c (q-p)`
for `0 ≤ p ≤ q ≤ L` (Lemma 5.1, `u_n^γ ⇀ c`), `γ > 0`. This is
impossible. -/
theorem blowup_contradiction {L uStar gamma ell xstar a b c : ℝ} {u : ℕ → ℝ → ℝ}
    {x : ℕ → ℝ} {U : ℝ → ℝ} (hL : 0 < L) (huStar : 0 < uStar) (hγ : 0 < gamma)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ y ∈ Icc 0 L, 0 ≤ u n y)
    (hmass : ∀ n, ∫ y in (0 : ℝ)..L, u n y ≤ L * uStar)
    (hmax : ∀ n, IsMaxOn (u n) (Icc 0 L) (x n))
    (hxlim : Tendsto x atTop (𝓝 xstar)) (hell : Tendsto (fun n => u n (x n)) atTop (𝓝 ell))
    (hell_gt : uStar < ell) (hab : a < b) (habL : Icc a b ⊆ Icc 0 L)
    (hxab : ∀ᶠ n in atTop, x n ∈ Icc a b) (hU : ContinuousOn U (Icc a b))
    (hconv : TendstoUniformlyOn u U atTop (Icc a b))
    (hweak : ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
      Tendsto (fun n => ∫ y in p..q, u n y ^ gamma) atTop (𝓝 (c * (q - p)))) :
    False := by
  have hxs : xstar ∈ Icc a b := isClosed_Icc.mem_of_tendsto hxlim hxab
  -- `U(x*) = ℓ`
  have hUx : U xstar = ell := by
    have := hconv.tendsto_comp (hU xstar hxs) (tendsto_nhdsWithin_iff.mpr ⟨hxlim, hxab⟩)
    exact tendsto_nhds_unique this hell
  have hU0 : ∀ y ∈ Icc a b, 0 ≤ U y := fun y hy =>
    ge_of_tendsto' (hconv.tendsto_at hy) fun n => hu0 n y (habL hy)
  -- eventually `u_n ≤ ℓ + 1` on `[0,L]`
  have hbd : ∀ᶠ n in atTop, ∀ y ∈ Icc 0 L, u n y ≤ ell + 1 := by
    filter_upwards [hell.eventually (gt_mem_nhds (show ell < ell + 1 by linarith))]
      with n hn y hy
    exact (hmax n hy).trans hn.le
  have hell0 : 0 < ell := huStar.trans hell_gt
  -- `∫_a^q U^γ = c (q-a)` by dominated convergence
  have hUint : ∀ q ∈ Icc a b, ∫ y in a..q, U y ^ gamma = c * (q - a) := by
    intro q hq
    have hsub : uIoc a q ⊆ Icc 0 L := by
      rw [uIoc_of_le hq.1]
      exact Ioc_subset_Icc_self.trans (habL.trans' (Icc_subset_Icc le_rfl hq.2))
    have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (F := fun n y => u n y ^ gamma) (f := fun y => U y ^ gamma) (a := a) (b := q)
      (μ := volume) (l := atTop) (fun _ => (ell + 1) ^ gamma)
      (Eventually.of_forall fun n => (((hu n).rpow_const fun _ _ => Or.inr hγ.le).mono
        hsub).aestronglyMeasurable measurableSet_uIoc)
      (hbd.mono fun n hn => Eventually.of_forall fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hu0 n y (hsub hy)) _)]
        exact Real.rpow_le_rpow (hu0 n y (hsub hy)) (hn y (hsub hy)) hγ.le)
      intervalIntegrable_const
      (Eventually.of_forall fun y hy => by
        rw [uIoc_of_le hq.1] at hy
        have hy' : y ∈ Icc a b := ⟨hy.1.le, hy.2.trans hq.2⟩
        exact (hconv.tendsto_at hy').rpow_const (Or.inr hγ.le))
    have hw := hweak a q (habL (left_mem_Icc.mpr hab.le)).1 hq.1
      (hq.2.trans (habL (right_mem_Icc.mpr hab.le)).2)
    exact tendsto_nhds_unique hlim hw
  -- `U^γ = c` on `[a,b]`, hence `c = ℓ^γ`
  have hUc := eqOn_const_of_integral_eq hab
    ((hU.rpow_const fun _ _ => Or.inr hγ.le) : ContinuousOn (fun y => U y ^ gamma) (Icc a b))
    hUint
  have hc : c = ell ^ gamma := by rw [← hUc xstar hxs, hUx]
  -- `∫_0^L u_n^γ → c L`
  have hglob : Tendsto (fun n => ∫ y in (0 : ℝ)..L, u n y ^ gamma) atTop (𝓝 (c * L)) := by
    simpa using hweak 0 L le_rfl hL.le le_rfl
  rcases le_or_gt gamma 1 with hγ1 | hγ1
  · -- Jensen: `c L ≤ L (u*)^γ < L ℓ^γ`
    have hle : c * L ≤ L * uStar ^ gamma :=
      le_of_tendsto' hglob fun n =>
        power_integral_le_of_le_one hL.le huStar hγ hγ1 (hu n) (hu0 n) (hmass n)
    have hlt : uStar ^ gamma < ell ^ gamma := Real.rpow_lt_rpow huStar.le hell_gt hγ
    rw [hc] at hle
    nlinarith
  · -- `c L ≤ ℓ^{γ-1} L u* < L ℓ^γ`
    have hbound : ∀ n, ∫ y in (0 : ℝ)..L, u n y ^ gamma ≤
        u n (x n) ^ (gamma - 1) * (L * uStar) := fun n =>
      power_integral_le_of_one_le hL.le hγ1.le (hu n) (hu0 n) (fun y hy => hmax n hy) (hmass n)
    have hrhs : Tendsto (fun n => u n (x n) ^ (gamma - 1) * (L * uStar)) atTop
        (𝓝 (ell ^ (gamma - 1) * (L * uStar))) :=
      (hell.rpow_const (Or.inl hell0.ne')).mul_const _
    have hle : c * L ≤ ell ^ (gamma - 1) * (L * uStar) :=
      le_of_tendsto_of_tendsto' hglob hrhs hbound
    have hsplit : ell ^ gamma = ell ^ (gamma - 1) * ell := by
      rw [Real.rpow_sub_one hell0.ne']; field_simp
    have hpos : 0 < ell ^ (gamma - 1) := Real.rpow_pos_of_pos hell0 _
    rw [hc, hsplit] at hle
    have : ell ^ (gamma - 1) * (L * uStar) < ell ^ (gamma - 1) * ell * L := by
      have := mul_lt_mul_of_pos_left hell_gt (mul_pos hpos hL)
      nlinarith
    linarith

/-! ### `E:spiky-thm-eq2` with its subsequence bookkeeping -/

/-- **Theorem 1.4, `E:spiky-thm-eq2`** (statement TeX lines 962–975, proof
lines 3483–3539). Let `u_n ≥ 0` be continuous on `[0,L]` with derivatives
`(u_n)_x` on `(0,L)`, `∫_0^L u_n ≤ L u*` (`u* > 0`), maximum points `x_n`,
and `liminf max u_n > u*` (stated as: eventually `max u_n ≥ ℓ₀ > u*`).
The analytic input `hcompact` is Arzelà–Ascoli together with Lemma 5.1:
along any subsequence whose gradients are eventually bounded on `[a,b]` and
whose values are eventually bounded, a further subsequence converges
uniformly on `[a,b]` to a continuous `U`, and `u^γ ⇀ c` (tested on
intervals) for a constant `c`. Then there are a subsequence `φ` and a point
`x* ∈ [0,L]` with `x_{φ k} → x*` such that for every `δ > 0` and `K`,
eventually `|(u_{φ k})_x| > K` at some point of
`(x* - δ, x* + δ) ∩ (0,L)`. -/
theorem spike_gradient_blowup {L uStar gamma : ℝ} {u du : ℕ → ℝ → ℝ} {x : ℕ → ℝ}
    (hL : 0 < L) (huStar : 0 < uStar) (hγ : 0 < gamma)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ y ∈ Icc 0 L, 0 ≤ u n y)
    (hdu : ∀ n, ∀ y ∈ Ioo 0 L, HasDerivAt (u n) (du n y) y)
    (hmass : ∀ n, ∫ y in (0 : ℝ)..L, u n y ≤ L * uStar)
    (hx : ∀ n, x n ∈ Icc 0 L) (hmax : ∀ n, IsMaxOn (u n) (Icc 0 L) (x n))
    (hliminf : ∃ l₀, uStar < l₀ ∧ ∀ᶠ n in atTop, l₀ ≤ u n (x n))
    (hcompact : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ a b K B : ℝ, a < b → Icc a b ⊆ Icc 0 L →
      (∀ᶠ n in atTop, ∀ y ∈ Ioo a b, |du (φ n) y| ≤ K) →
      (∀ᶠ n in atTop, ∀ y ∈ Icc 0 L, u (φ n) y ≤ B) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (U : ℝ → ℝ) (c : ℝ), ContinuousOn U (Icc a b) ∧
        TendstoUniformlyOn (fun k => u (φ (ψ k))) U atTop (Icc a b) ∧
        ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
          Tendsto (fun k => ∫ y in p..q, u (φ (ψ k)) y ^ gamma) atTop (𝓝 (c * (q - p)))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ xstar ∈ Icc 0 L, Tendsto (fun k => x (φ k)) atTop (𝓝 xstar) ∧
      ∀ δ > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
        ∃ y ∈ Ioo (max 0 (xstar - δ)) (min L (xstar + δ)), K < |du (φ k) y| := by
  obtain ⟨xstar, hxs, φ0, hφ0, hφ0lim⟩ := isCompact_Icc.tendsto_subseq hx
  refine ⟨φ0, hφ0, xstar, hxs, hφ0lim, fun δ hδ K => ?_⟩
  by_contra hnot
  rw [not_eventually] at hnot
  obtain ⟨φ1, hφ1, hbd⟩ := extraction_of_frequently_atTop hnot
  set a : ℝ := max 0 (xstar - δ) with ha_def
  set b : ℝ := min L (xstar + δ) with hb_def
  have hab : a < b :=
    max_lt (lt_min hL (by linarith [hxs.1])) (lt_min (by linarith [hxs.2]) (by linarith))
  have habL : Icc a b ⊆ Icc 0 L := Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hIoo : Ioo a b ⊆ Ioo 0 L := Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hK : ∀ k, ∀ y ∈ Ioo a b, |du (φ0 (φ1 k)) y| ≤ K :=
    fun k y hy => not_lt.mp fun h => hbd k ⟨y, hy, h⟩
  have hxlim01 : Tendsto (fun k => x (φ0 (φ1 k))) atTop (𝓝 xstar) :=
    hφ0lim.comp hφ1.tendsto_atTop
  have hxab01 : ∀ᶠ k in atTop, x (φ0 (φ1 k)) ∈ Icc a b := by
    filter_upwards [hxlim01.eventually (Metric.ball_mem_nhds xstar hδ)] with k hk
    rw [Real.dist_eq, abs_lt] at hk
    have := hx (φ0 (φ1 k))
    exact ⟨max_le this.1 (by linarith), le_min this.2 (by linarith)⟩
  set B0 : ℝ := L * uStar / (b - a) + K * (b - a)
  have hsup : ∀ᶠ k in atTop, ∀ y ∈ Icc 0 L, u (φ0 (φ1 k)) y ≤ B0 := by
    filter_upwards [hxab01] with k hk y hy
    exact (hmax _ hy).trans (le_of_local_gradient_bound hab habL (hu _) (hu0 _)
      (fun z hz => hdu _ z (hIoo hz)) (hK k) hk (hmass _))
  -- Bolzano–Weierstrass for the maxima `h_n`
  obtain ⟨ell, -, φ2, hφ2, hell⟩ := tendsto_subseq_of_frequently_bounded
    (s := Icc 0 B0) (Metric.isBounded_Icc 0 B0)
    (x := fun k => u (φ0 (φ1 k)) (x (φ0 (φ1 k))))
    (hsup.frequently.mono fun k hk => ⟨hu0 _ _ (hx _), hk _ (hx _)⟩)
  obtain ⟨l₀, hl₀, hl₀ev⟩ := hliminf
  have hφ : StrictMono fun k => φ0 (φ1 (φ2 k)) := hφ0.comp (hφ1.comp hφ2)
  have hell_ge : l₀ ≤ ell := ge_of_tendsto hell (hφ.tendsto_atTop.eventually hl₀ev)
  obtain ⟨ψ, hψ, U, c, hU, hconv, hweak⟩ := hcompact (fun k => φ0 (φ1 (φ2 k))) hφ a b K B0
    hab habL (Eventually.of_forall fun k => hK (φ2 k)) (hφ2.tendsto_atTop.eventually hsup)
  exact blowup_contradiction (u := fun k => u (φ0 (φ1 (φ2 (ψ k)))))
    (x := fun k => x (φ0 (φ1 (φ2 (ψ k))))) (U := U) (c := c) (ell := ell) (xstar := xstar)
    hL huStar hγ (fun _ => hu _) (fun _ => hu0 _) (fun _ => hmass _) (fun _ => hmax _)
    (hxlim01.comp (hφ2.comp hψ).tendsto_atTop) (hell.comp hψ.tendsto_atTop)
    (by linarith) hab habL ((hφ2.comp hψ).tendsto_atTop.eventually hxab01) hU hconv hweak

/-- **The relabeling remark** (TeX lines 3554–3555): the conclusion of
`E:spiky-thm-eq2` survives passing to a further subsequence. -/
theorem gradient_blowup_subseq {L xstar : ℝ} {du : ℕ → ℝ → ℝ} {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ)
    (h : ∀ δ > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
      ∃ y ∈ Ioo (max 0 (xstar - δ)) (min L (xstar + δ)), K < |du k y|) :
    ∀ δ > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
      ∃ y ∈ Ioo (max 0 (xstar - δ)) (min L (xstar + δ)), K < |du (ψ k) y| :=
  fun δ hδ K => hψ.tendsto_atTop.eventually (h δ hδ K)

/-! ### `E:spiky-thm-eq3` in the non-minimal model -/

/-- **Theorem 1.4, the exponents of `E:spiky-thm-eq3`** (TeX lines 979–985,
3544–3549): for `α > 0` and `0 < γ < 1 + α`, the exponent `r = 1 + α`
supplied by Lemma 4.1(1) satisfies `r > max{1, γ}`, and
`q = (1+α)/γ > 1`, so Lemma 5.1 applies. -/
theorem exponent_admissible {alpha gamma : ℝ} (halpha : 0 < alpha) (hγ : 0 < gamma)
    (hγα : gamma < 1 + alpha) : max 1 gamma < 1 + alpha ∧ 1 < (1 + alpha) / gamma :=
  ⟨max_lt (by linarith) hγα, by rw [one_lt_div hγ]; exact hγα⟩

/-- **Theorem 1.4, the bound `0 ≤ c ≤ (u*)^γ` in `E:spiky-thm-eq3`** (TeX
lines 3546–3553). If `u_n ≥ 0` are continuous with the Lemma 4.1(1) moment
bound `∫_0^L u_n^{1+α} ≤ L (u*)^{1+α}` and `∫_0^L u_n^γ → c L`, where
`0 < γ ≤ 1 + α`, then `0 ≤ c ≤ (u*)^γ` (Jensen, `IntervalMoments`). -/
theorem spike_limit_constant_le {L uStar alpha gamma c : ℝ} {u : ℕ → ℝ → ℝ} (hL : 0 < L)
    (halpha : 0 < alpha) (huStar : 0 ≤ uStar) (hγ : 0 < gamma) (hγα : gamma ≤ 1 + alpha)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ y ∈ Icc 0 L, 0 ≤ u n y)
    (hmoment : ∀ n, ∫ y in (0 : ℝ)..L, u n y ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha))
    (hweak : Tendsto (fun n => ∫ y in (0 : ℝ)..L, u n y ^ gamma) atTop (𝓝 (c * L))) :
    0 ≤ c ∧ c ≤ uStar ^ gamma := by
  have hle : c * L ≤ L * uStar ^ gamma := le_of_tendsto' hweak fun n =>
    IntervalMoments.logistic_power_integral_le L uStar alpha gamma (u n) hL halpha huStar hγ
      hγα (hu n) (hu0 n) (hmoment n)
  have hge : 0 ≤ c * L := ge_of_tendsto' hweak fun n =>
    intervalIntegral.integral_nonneg hL.le fun y hy => Real.rpow_nonneg (hu0 n y hy) _
  constructor
  · exact nonneg_of_mul_nonneg_left hge hL
  · rw [mul_comm L] at hle
    exact le_of_mul_le_mul_right hle hL

/-- **Theorem 1.4, both conclusions on one subsequence, non-minimal model**
(TeX lines 3541–3556). Under the hypotheses of `spike_gradient_blowup`, the
Lemma 4.1(1) moment bound and `0 < γ < 1 + α`, with the analytic input
`hlemma` (Lemma 5.1 for `r = 1 + α`: along any subsequence a further
subsequence has `∫_0^L u^γ → c L` for a constant `c`), there are one
subsequence `φ`, a point `x*` and a constant `0 ≤ c ≤ (u*)^γ` such that
`∫_0^L u_{φ k}^γ → c L` and `E:spiky-thm-eq2` holds along `φ`. -/
theorem spike_limit_nonminimal {L uStar alpha gamma : ℝ} {u du : ℕ → ℝ → ℝ} {x : ℕ → ℝ}
    (hL : 0 < L) (huStar : 0 < uStar) (halpha : 0 < alpha) (hγ : 0 < gamma)
    (hγα : gamma < 1 + alpha)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ y ∈ Icc 0 L, 0 ≤ u n y)
    (hdu : ∀ n, ∀ y ∈ Ioo 0 L, HasDerivAt (u n) (du n y) y)
    (hmass : ∀ n, ∫ y in (0 : ℝ)..L, u n y ≤ L * uStar)
    (hmoment : ∀ n, ∫ y in (0 : ℝ)..L, u n y ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha))
    (hx : ∀ n, x n ∈ Icc 0 L) (hmax : ∀ n, IsMaxOn (u n) (Icc 0 L) (x n))
    (hliminf : ∃ l₀, uStar < l₀ ∧ ∀ᶠ n in atTop, l₀ ≤ u n (x n))
    (hcompact : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ a b K B : ℝ, a < b → Icc a b ⊆ Icc 0 L →
      (∀ᶠ n in atTop, ∀ y ∈ Ioo a b, |du (φ n) y| ≤ K) →
      (∀ᶠ n in atTop, ∀ y ∈ Icc 0 L, u (φ n) y ≤ B) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (U : ℝ → ℝ) (c : ℝ), ContinuousOn U (Icc a b) ∧
        TendstoUniformlyOn (fun k => u (φ (ψ k))) U atTop (Icc a b) ∧
        ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
          Tendsto (fun k => ∫ y in p..q, u (φ (ψ k)) y ^ gamma) atTop (𝓝 (c * (q - p))))
    (hlemma : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ c : ℝ,
      Tendsto (fun k => ∫ y in (0 : ℝ)..L, u (φ (ψ k)) y ^ gamma) atTop (𝓝 (c * L))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ xstar ∈ Icc 0 L, ∃ c, 0 ≤ c ∧ c ≤ uStar ^ gamma ∧
      Tendsto (fun k => ∫ y in (0 : ℝ)..L, u (φ k) y ^ gamma) atTop (𝓝 (c * L)) ∧
      ∀ δ > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
        ∃ y ∈ Ioo (max 0 (xstar - δ)) (min L (xstar + δ)), K < |du (φ k) y| := by
  obtain ⟨φ, hφ, xstar, hxs, -, hblow⟩ := spike_gradient_blowup hL huStar hγ hu hu0 hdu hmass
    hx hmax hliminf hcompact
  obtain ⟨ψ, hψ, c, hc⟩ := hlemma φ hφ
  obtain ⟨hc0, hc1⟩ := spike_limit_constant_le hL halpha huStar.le hγ hγα.le
    (fun _ => hu _) (fun _ => hu0 _) (fun _ => hmoment _) hc
  exact ⟨fun k => φ (ψ k), hφ.comp hψ, xstar, hxs, c, hc0, hc1, hc,
    gradient_blowup_subseq (du := fun k => du (φ k)) hψ hblow⟩

/-! ### A full-sequence corollary (ledger, not the October 8 TeX) -/

/-- **Full-sequence limit from a unique subsequential limit.** In the minimal
model with `γ = 1` and fixed mass `∫_0^L u_n = L u*`, if every subsequence
has a further subsequence with `∫_p^q u → c (q - p)` for some constant `c`
(Lemma 5.1's conclusion), then `c = u*` is forced by the mass, and the whole
sequence satisfies `∫_p^q u_n → u* (q - p)`. This is the "full-sequence
conclusion at `γ = 1`" named in the ledger's source assessment for
`paper3/L:minimal-spike-limit`; it is not a clause of the October 8 TeX. -/
theorem minimal_full_sequence {L uStar : ℝ} {u : ℕ → ℝ → ℝ} (hL : 0 < L)
    (hmass : ∀ n, ∫ y in (0 : ℝ)..L, u n y = L * uStar)
    (hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ, ∃ c : ℝ,
      ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
        Tendsto (fun k => ∫ y in p..q, u (ns (ms k)) y) atTop (𝓝 (c * (q - p)))) :
    ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
      Tendsto (fun n => ∫ y in p..q, u n y) atTop (𝓝 (uStar * (q - p))) := by
  intro p q hp hpq hq
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, c, hc⟩ := hsub ns hns
  have hcL : c = uStar := by
    have h := hc 0 L le_rfl hL.le le_rfl
    simp only [hmass, sub_zero] at h
    have := tendsto_nhds_unique tendsto_const_nhds h
    exact (mul_right_cancel₀ hL.ne' (by linarith)).symm
  exact ⟨ms, hcL ▸ hc p q hp hpq hq⟩

end ChemotaxisBifurcation.SpikeLimit
