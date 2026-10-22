module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
Reuses the MIT Paper III finite-verification development.

# Fixed-mode and finite-cutoff threshold consistency

Current anchor: Theorem 1.4 (page 11), with proof in Section 5 of the corrected
September 26 manuscript. This module proves fixed-mode convergence, the minimal
model minimum, and convergence over any fixed finite mode set. The logistic
minimum additionally requires a uniform cutoff; the conditional theorem below
keeps that input explicit until a cutoff-construction bridge is supplied.
-/

public import Mathlib

@[expose] public section

namespace ChemotaxisBifurcation.Semidiscrete

open Filter
open scoped Topology

/-- Continuum Neumann eigenvalue `lambda_n = (n*pi/L)^2`. -/
noncomputable def continuumLam (L : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.pi / L) ^ 2

/-- The small angle `n*pi/(2*N)` in the three-point eigenvalue. -/
noncomputable def discArg (n N : ℕ) : ℝ :=
  (n : ℝ) * Real.pi / (2 * (N : ℝ))

/-- Manuscript the discrete eigenvalue formula, with mesh width `h = L/N`. -/
noncomputable def discLam (L : ℝ) (n N : ℕ) : ℝ :=
  4 / (L / (N : ℝ)) ^ 2 * Real.sin (discArg n N) ^ 2

/-- The discrete eigenvalue is the continuum eigenvalue times `sinc^2`.
This is the exact algebraic bridge from the discrete eigenvalue formula to the limit proof. -/
theorem discLam_eq_continuum_mul_sinc_sq (L : ℝ) (n N : ℕ)
    (hL : L ≠ 0) (hn : 0 < n) (hN : 0 < N) :
    discLam L n N = continuumLam L n * Real.sinc (discArg n N) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have harg : discArg n N ≠ 0 := by
    unfold discArg
    exact div_ne_zero (mul_ne_zero hn0 Real.pi_ne_zero) (mul_ne_zero two_ne_zero hN0)
  rw [Real.sinc_of_ne_zero harg]
  unfold discLam continuumLam discArg
  field_simp
  ring

/-- For a fixed mode, the discrete angle tends to zero as the mesh is refined. -/
theorem discArg_tendsto_zero (n : ℕ) :
    Tendsto (discArg n) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => ((n : ℝ) * Real.pi / 2) / (N : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  funext N
  unfold discArg
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The fixed-mode discrete Neumann eigenvalue converges to the continuum one. -/
theorem discLam_tendsto_continuum (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    Tendsto (discLam L n) atTop (𝓝 (continuumLam L n)) := by
  have harg := discArg_tendsto_zero n
  have hsinc : Tendsto (fun N : ℕ => Real.sinc (discArg n N)) atTop (𝓝 1) := by
    change Tendsto (Real.sinc ∘ discArg n) atTop (𝓝 1)
    simpa only [Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp harg
  have hnormalized : Tendsto
      (fun N : ℕ => continuumLam L n * Real.sinc (discArg n N) ^ 2)
      atTop (𝓝 (continuumLam L n)) := by
    simpa using tendsto_const_nhds.mul (hsinc.pow 2)
  apply hnormalized.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (discLam_eq_continuum_mul_sinc_sq L n N (ne_of_gt hL) hn hN).symm

/-- Fixed-mode threshold map used in the modal threshold formulas. The constant
`K` collects the positive prefactor independent of the eigenvalue, while `q`
is `a*alpha`. -/
noncomputable def modeThreshold (K q mu lam : ℝ) : ℝ :=
  K * ((lam + q) * (mu + lam) / lam)

/-- Fixed-mode consistency: the semidiscrete threshold of each fixed positive mode
converges to its continuum threshold. -/
theorem modeThreshold_disc_tendsto (L : ℝ) (n : ℕ) (K q mu : ℝ)
    (hL : 0 < L) (hn : 0 < n) :
    Tendsto (fun N : ℕ => modeThreshold K q mu (discLam L n N))
      atTop (𝓝 (modeThreshold K q mu (continuumLam L n))) := by
  have hlam : continuumLam L n ≠ 0 := by
    unfold continuumLam
    positivity
  have hcontinuous : ContinuousAt (modeThreshold K q mu) (continuumLam L n) := by
    unfold modeThreshold
    fun_prop
  exact hcontinuous.tendsto.comp (discLam_tendsto_continuum L n hL hn)

/-- For a represented discrete mode `1 ≤ n ≤ N`, its sine angle lies in the
monotonicity interval `[0, pi/2]`. -/
theorem discArg_mem_Icc (n N : ℕ) (hN : 0 < N) (hnN : n ≤ N) :
    discArg n N ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnr : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  constructor
  · unfold discArg
    positivity
  · unfold discArg
    rw [div_le_iff₀ (by positivity : 0 < 2 * (N : ℝ))]
    nlinarith [Real.pi_pos]

/-- The first positive discrete angle is no larger than any represented
positive-mode angle. -/
theorem discArg_one_le (n N : ℕ) (hN : 0 < N) (hn : 1 ≤ n) :
    discArg 1 N ≤ discArg n N := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnr : ((1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold discArg
  apply div_le_div_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right hnr Real.pi_pos.le
  · positivity

/-- Among the modes represented on an `N`-interval mesh, the first positive
mode has the smallest discrete eigenvalue. -/
theorem discLam_one_le (L : ℝ) (n N : ℕ)
    (hL : 0 < L) (hN : 0 < N) (hn : 1 ≤ n) (hnN : n ≤ N) :
    discLam L 1 N ≤ discLam L n N := by
  have harg1 := discArg_mem_Icc 1 N hN (hn.trans hnN)
  have hargn := discArg_mem_Icc n N hN hnN
  have hargle := discArg_one_le n N hN hn
  have hsinle : Real.sin (discArg 1 N) ≤ Real.sin (discArg n N) :=
    Real.strictMonoOn_sin.monotoneOn
      ⟨(neg_nonpos.mpr (by positivity)).trans harg1.1, harg1.2⟩
      ⟨(neg_nonpos.mpr (by positivity)).trans hargn.1, hargn.2⟩ hargle
  have hsin1 : 0 ≤ Real.sin (discArg 1 N) :=
    Real.sin_nonneg_of_nonneg_of_le_pi harg1.1
      (harg1.2.trans (by linarith [Real.pi_pos]))
  have hsquare : Real.sin (discArg 1 N) ^ 2 ≤
      Real.sin (discArg n N) ^ 2 :=
    pow_le_pow_left₀ hsin1 hsinle 2
  unfold discLam
  exact mul_le_mul_of_nonneg_left hsquare (by positivity)

/-- Minimal-model discrete threshold, where the rational mode factor reduces
to `mu + lambda_n^disc`. -/
noncomputable def minimalDiscThreshold
    (K mu L : ℝ) (n N : ℕ) : ℝ :=
  K * (mu + discLam L n N)

/-- The first positive mode minimizes the minimal-model discrete thresholds on
every represented mesh. -/
theorem minimalDiscThreshold_one_le (K mu L : ℝ) (n N : ℕ)
    (hK : 0 ≤ K) (hL : 0 < L) (hN : 0 < N)
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    minimalDiscThreshold K mu L 1 N ≤
      minimalDiscThreshold K mu L n N := by
  unfold minimalDiscThreshold
  exact mul_le_mul_of_nonneg_left
    (by simpa [add_comm] using
      add_le_add_left (discLam_one_le L n N hL hN hn hnN) mu) hK

/-- Literal finite-minimum formulation of the preceding theorem. -/
theorem minimalDiscThreshold_isLeast (K mu L : ℝ) (N : ℕ)
    (hK : 0 ≤ K) (hL : 0 < L) (hN : 0 < N) :
    IsLeast
      {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
        x = minimalDiscThreshold K mu L n N}
      (minimalDiscThreshold K mu L 1 N) := by
  constructor
  · exact ⟨1, le_rfl, hN, rfl⟩
  · rintro x ⟨n, hn, hnN, rfl⟩
    exact minimalDiscThreshold_one_le K mu L n N hK hL hN hn hnN

/-- The minimum minimal-model discrete threshold converges to its continuum
counterpart; by `minimalDiscThreshold_isLeast`, the left side is literally the
mesh-dependent minimum in the current manuscript. -/
theorem minimalDiscThreshold_tendsto (K mu L : ℝ) (hL : 0 < L) :
    Tendsto (minimalDiscThreshold K mu L 1) atTop
      (𝓝 (K * (mu + continuumLam L 1))) := by
  unfold minimalDiscThreshold
  exact tendsto_const_nhds.mul
    (tendsto_const_nhds.add (discLam_tendsto_continuum L 1 hL Nat.one_pos))

/-- Sine concavity supplies the uniform quadratic lower eigenvalue bound used
in the manuscript's cutoff argument. -/
theorem discLam_lower_bound (L : ℝ) (n N : ℕ)
    (hL : 0 < L) (hN : 0 < N) (hnN : n ≤ N) :
    4 * (n : ℝ) ^ 2 / L ^ 2 ≤ discLam L n N := by
  have ha := discArg_mem_Icc n N hN hnN
  have hs := Real.mul_le_sin ha.1 ha.2
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : 2 / Real.pi * discArg n N = (n : ℝ) / (N : ℝ) := by
    unfold discArg
    field_simp
  rw [hid] at hs
  have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) / (N : ℝ)) hs 2
  have hp := mul_le_mul_of_nonneg_left hs2
    (by positivity : 0 ≤ 4 / (L / (N : ℝ)) ^ 2)
  unfold discLam
  calc
    4 * (n : ℝ) ^ 2 / L ^ 2 =
        4 / (L / (N : ℝ)) ^ 2 * ((n : ℝ) / (N : ℝ)) ^ 2 := by
      field_simp [hL.ne', hN0] <;> ring
    _ ≤ 4 / (L / (N : ℝ)) ^ 2 * Real.sin (discArg n N) ^ 2 := hp

/-- The threshold dominates its eigenvalue times the positive prefactor. -/
theorem threshold_lower_bound (K q mu lam : ℝ)
    (hK : 0 ≤ K) (hq : 0 ≤ q) (hmu : 0 ≤ mu) (hlam : 0 < lam) :
    K * lam ≤ modeThreshold K q mu lam := by
  unfold modeThreshold
  apply mul_le_mul_of_nonneg_left _ hK
  apply (le_div_iff₀ hlam).mpr
  nlinarith [mul_nonneg hq hmu]

/-- Existing mathlib continuity of finite infima gives uniform finite-mode
minimum convergence without a new minimum-convergence implementation. -/
theorem finite_mode_minimum_tendsto (S : Finset ℕ) (hne : S.Nonempty)
    (hpos : ∀ n ∈ S, 0 < n) (K q mu L : ℝ) (hL : 0 < L) :
    Tendsto (fun N => S.inf' hne (fun n => modeThreshold K q mu (discLam L n N)))
      atTop (𝓝 (S.inf' hne (fun n => modeThreshold K q mu (continuumLam L n)))) := by
  apply Filter.Tendsto.finset_inf'_nhds_apply hne
  intro n hn
  exact modeThreshold_disc_tendsto L n K q mu hL (hpos n hn)

/-- Once a common finite minimizing set has been established, the discrete
critical threshold converges to the continuum minimum. -/
theorem critical_threshold_tendsto_of_finite_cutoff
    (S : Finset ℕ) (hne : S.Nonempty) (hpos : ∀ n ∈ S, 0 < n)
    (K q mu L : ℝ) (hL : 0 < L) (critical : ℕ → ℝ) (limit : ℝ)
    (hcutoff : ∀ᶠ N in atTop,
      critical N = S.inf' hne (fun n => modeThreshold K q mu (discLam L n N)))
    (hlimit : limit = S.inf' hne (fun n => modeThreshold K q mu (continuumLam L n))) :
    Tendsto critical atTop (𝓝 limit) := by
  rw [hlimit]
  exact (finite_mode_minimum_tendsto S hne hpos K q mu L hL).congr'
    (hcutoff.mono fun _ h => h.symm)

end ChemotaxisBifurcation.Semidiscrete
