module
public import ChemotaxisBifurcation.SignalDerivatives
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation
open Set Filter
open scoped Topology

private theorem source_contDiffAt (nu gamma u : ℝ) (hu : 0 < u) (n : ℕ) :
    ContDiffAt ℝ n (fun y : ℝ => nu * y ^ gamma) u :=
  contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hu))

private theorem source_iter_one (nu gamma u : ℝ) (hu : 0 < u) :
    iteratedDeriv 1 (fun y : ℝ => nu * y ^ gamma) u =
      signalSourceFirst nu gamma u := by
  simpa using signalSource_deriv_eq_first nu gamma u hu

private theorem source_iter_two (nu gamma u : ℝ) (hu : 0 < u) :
    iteratedDeriv 2 (fun y : ℝ => nu * y ^ gamma) u =
      signalSourceSecond nu gamma u := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ]
  have he : iteratedDeriv 1 (fun y : ℝ => nu * y ^ gamma) =ᶠ[𝓝 u]
      signalSourceFirst nu gamma := by
    filter_upwards [Ioi_mem_nhds hu] with y hy
    exact source_iter_one nu gamma y hy
  rw [he.deriv_eq, (signalSourceFirst_hasDerivAt nu gamma u hu).deriv]
  rfl

private theorem source_iter_three (nu gamma u : ℝ) (hu : 0 < u) :
    iteratedDeriv 3 (fun y : ℝ => nu * y ^ gamma) u =
      nu * gamma * (gamma - 1) * (gamma - 2) * u ^ (gamma - 3) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  have he : iteratedDeriv 2 (fun y : ℝ => nu * y ^ gamma) =ᶠ[𝓝 u]
      signalSourceSecond nu gamma := by
    filter_upwards [Ioi_mem_nhds hu] with y hy
    exact source_iter_two nu gamma y hy
  rw [he.deriv_eq, (signalSourceSecond_hasDerivAt nu gamma u hu).deriv]

private theorem source_taylor_three (p : PhysicalParams) (hu : 0 < p.uStar)
    (x : ℝ) (hne : p.uStar ≠ x) :
    taylorWithinEval (fun y : ℝ => p.nu * y ^ p.gamma) 3
      (uIcc p.uStar x) p.uStar x =
      p.nu * p.uStar ^ p.gamma + (rawTaylorData p 0).Cprime * (x - p.uStar) +
        (rawTaylorData p 0).Csecond * (x - p.uStar)^2 +
        (rawTaylorData p 0).Cthird * (x - p.uStar)^3 := by
  have hd (n : ℕ) := iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_uIcc hne) (source_contDiffAt p.nu p.gamma p.uStar hu n)
    (left_mem_uIcc : p.uStar ∈ uIcc p.uStar x)
  rw [taylorWithinEval_succ _ 2, taylorWithinEval_succ _ 1,
    taylorWithinEval_succ _ 0]
  simp only [taylor_within_zero_eval, hd]
  rw [source_iter_one p.nu p.gamma p.uStar hu,
    source_iter_two p.nu p.gamma p.uStar hu,
    source_iter_three p.nu p.gamma p.uStar hu]
  simp [rawTaylorData, signalSourceFirst, signalSourceSecond, Nat.factorial]
  ring

/-- The actual positive-base real-power source has a two-sided quartic remainder.
The constant is derived using continuity on a compact positive interval. -/
theorem signalSource_quartic_remainder (p : PhysicalParams) (hu : 0 < p.uStar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ p.uStar / 2 →
      |p.nu * (p.uStar + s) ^ p.gamma - p.nu * p.uStar ^ p.gamma -
        (rawTaylorData p 0).Cprime * s - (rawTaylorData p 0).Csecond * s^2 -
        (rawTaylorData p 0).Cthird * s^3| ≤ C * |s|^4 := by
  let f : ℝ → ℝ := fun y => p.nu * y ^ p.gamma
  let K : Set ℝ := Icc (p.uStar / 2) (3 * p.uStar / 2)
  have hab : p.uStar / 2 < 3 * p.uStar / 2 := by linarith
  have hpos : ∀ y ∈ K, 0 < y := by intro y hy; dsimp [K] at hy; linarith [hy.1]
  have hc : ContDiffOn ℝ 4 f K := by
    intro y hy
    exact (source_contDiffAt p.nu p.gamma y (hpos y hy) 4).contDiffWithinAt
  have hd : ContinuousOn (iteratedDeriv 4 f) K := by
    have h := hc.continuousOn_iteratedDerivWithin (m := 4) (by norm_num)
      (uniqueDiffOn_Icc hab)
    apply h.congr
    intro y hy
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      (source_contDiffAt p.nu p.gamma y (hpos y hy) 4) hy).symm
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  refine ⟨max B 0 / 24, by positivity, ?_⟩
  intro s hs
  by_cases hz : s = 0
  · simp [hz]
  have hne : p.uStar ≠ p.uStar + s := by intro h; apply hz; linarith
  have hxK : p.uStar + s ∈ K := by
    dsimp [K]
    obtain ⟨hl, hr⟩ := abs_le.mp hs
    constructor <;> linarith
  have huK : p.uStar ∈ K := by
    change p.uStar / 2 ≤ p.uStar ∧ p.uStar ≤ 3 * p.uStar / 2
    constructor <;> linarith
  have hsub : uIcc p.uStar (p.uStar + s) ⊆ K :=
    uIcc_subset_Icc huK hxK
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 3) hne (hc.mono hsub)
  have hyK : y ∈ K := hsub (Ioo_subset_Icc_self hy)
  have hbound : |iteratedDeriv 4 f y| ≤ max B 0 :=
    (hB y hyK).trans (le_max_left _ _)
  have ht := source_taylor_three p hu (p.uStar + s) hne
  change f (p.uStar + s) - _ = _ at he
  rw [ht] at he
  simp only [add_sub_cancel_left] at he
  have he' : p.nu * (p.uStar + s) ^ p.gamma - p.nu * p.uStar ^ p.gamma -
      (rawTaylorData p 0).Cprime * s - (rawTaylorData p 0).Csecond * s^2 -
      (rawTaylorData p 0).Cthird * s^3 = iteratedDeriv 4 f y * s^4 / 24 := by
    dsimp [f] at he
    norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at he
    convert he using 1; ring
  rw [he', abs_div, abs_mul, abs_pow]
  norm_num
  calc
    |iteratedDeriv 4 f y| * |s| ^ 4 / 24 ≤ max B 0 * |s| ^ 4 / 24 := by gcongr
    _ = max B 0 / 24 * |s| ^ 4 := by ring

/-- Uniform quartic source bound for an actual perturbation field, obtained
from the scalar real-power theorem; no Taylor-remainder assumption occurs. -/
theorem signalSource_field_quartic_bound (p : PhysicalParams) (hu : 0 < p.uStar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L N : ℝ) (U : ℝ → ℝ),
      N ≤ p.uStar / 2 → (∀ x ∈ Icc 0 L, |U x| ≤ N) → ∀ x ∈ Icc 0 L,
      |p.nu * (p.uStar + U x) ^ p.gamma - p.nu * p.uStar ^ p.gamma -
        (rawTaylorData p 0).Cprime * U x -
        (rawTaylorData p 0).Csecond * (U x)^2 -
        (rawTaylorData p 0).Cthird * (U x)^3| ≤ C * N^4 := by
  obtain ⟨C, hC, hrem⟩ := signalSource_quartic_remainder p hu
  refine ⟨C, hC, ?_⟩
  intro L N U hN hU x hx
  exact (hrem (U x) ((hU x hx).trans hN)).trans (by gcongr; exact hU x hx)

end ChemotaxisBifurcation
