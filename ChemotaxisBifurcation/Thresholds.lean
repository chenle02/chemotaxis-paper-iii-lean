module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
Reused from the Paper III finite-verification subtree; historical numbering
is not evidence of current manuscript coverage.

# Modal threshold algebra and existence of a minimizing mode

The equilibrium-construction part of the legacy module is deliberately not
imported: this companion carries positive uStar/vStar as model data.
-/

public import ChemotaxisBifurcation.Semidiscrete

@[expose] public section

namespace ChemotaxisBifurcation.Thresholds

open Filter
open scoped Topology

noncomputable def modeFactor (q mu lam : ℝ) : ℝ :=
  (lam + q) * (mu + lam) / lam

/-- The sharp AM--GM lower bound for the continuous modal factor. -/
theorem modeFactor_lower_bound (q mu lam : ℝ)
    (hq : 0 ≤ q) (hmu : 0 ≤ mu) (hlam : 0 < lam) :
    (Real.sqrt q + Real.sqrt mu) ^ 2 ≤ modeFactor q mu lam := by
  have hq_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  have hmu_sq : (Real.sqrt mu) ^ 2 = mu := Real.sq_sqrt hmu
  have hid :
      (modeFactor q mu lam - (Real.sqrt q + Real.sqrt mu) ^ 2) * lam
        = (lam - Real.sqrt q * Real.sqrt mu) ^ 2 := by
    unfold modeFactor
    field_simp
    nlinarith
  have hprod :
      0 ≤ (modeFactor q mu lam - (Real.sqrt q + Real.sqrt mu) ^ 2) * lam := by
    rw [hid]
    positivity
  have hdiff :
      0 ≤ modeFactor q mu lam - (Real.sqrt q + Real.sqrt mu) ^ 2 :=
    nonneg_of_mul_nonneg_left hprod hlam
  linarith

/-- For positive `q` and `mu`, the continuous lower bound is attained at
`lam = sqrt (q * mu)`. -/
theorem modeFactor_eq_lower_bound (q mu : ℝ)
    (hq : 0 < q) (hmu : 0 < mu) :
    modeFactor q mu (Real.sqrt (q * mu))
      = (Real.sqrt q + Real.sqrt mu) ^ 2 := by
  have hqm : 0 ≤ q * mu := (mul_pos hq hmu).le
  have hlam : Real.sqrt (q * mu) ≠ 0 := (Real.sqrt_pos.2 (mul_pos hq hmu)).ne'
  have hsqrt_mul : Real.sqrt (q * mu) = Real.sqrt q * Real.sqrt mu := by
    rw [Real.sqrt_mul hq.le]
  have hq_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  have hmu_sq : (Real.sqrt mu) ^ 2 = mu := Real.sq_sqrt hmu.le
  unfold modeFactor
  rw [hsqrt_mul]
  field_simp
  nlinarith

/-- In the minimal case `q = 0`, the modal factor reduces to `mu + lam`. -/
theorem modeFactor_zero_eq (mu lam : ℝ) (hlam : lam ≠ 0) :
    modeFactor 0 mu lam = mu + lam := by
  unfold modeFactor
  field_simp
  ring

/-- Minimal-model endpoint of the continuous lower bound: `mu` is exactly the infimum of
the modal factor over positive continuous eigenvalues, although it is not
attained. -/
theorem modeFactor_zero_isGLB (mu : ℝ) :
    IsGLB (Set.range fun lam : {x : ℝ // 0 < x} =>
      modeFactor 0 mu lam.1) mu := by
  constructor
  · rintro y ⟨lam, rfl⟩
    change mu ≤ modeFactor 0 mu lam.1
    rw [modeFactor_zero_eq mu lam.1 lam.2.ne']
    exact le_add_of_nonneg_right lam.2.le
  · intro lower hlower
    by_contra hnot
    have hmu_lt : mu < lower := lt_of_not_ge hnot
    let lam : {x : ℝ // 0 < x} :=
      ⟨(lower - mu) / 2, by linarith⟩
    have hbound := hlower ⟨lam, rfl⟩
    change lower ≤ modeFactor 0 mu lam.1 at hbound
    rw [modeFactor_zero_eq mu lam.1 lam.2.ne'] at hbound
    dsimp [lam] at hbound
    linarith

/-- The full modal threshold, with all beta dependence isolated in the common
positive factor `K`. -/
noncomputable def modeThreshold (K q mu lam : ℝ) : ℝ :=
  K * modeFactor q mu lam

/-- The sharp threshold lower bound, pointwise in every positive Neumann eigenvalue. -/
theorem modeThreshold_lower_bound (K q mu lam : ℝ)
    (hK : 0 ≤ K) (hq : 0 ≤ q) (hmu : 0 ≤ mu) (hlam : 0 < lam) :
    K * (Real.sqrt q + Real.sqrt mu) ^ 2
      ≤ modeThreshold K q mu lam := by
  unfold modeThreshold
  exact mul_le_mul_of_nonneg_left (modeFactor_lower_bound q mu lam hq hmu hlam) hK

/-- A common positive threshold prefactor preserves every pairwise modal
comparison.  This is the beta-independence of the minimizing mode in the manuscript. -/
theorem modeThreshold_le_iff (K q mu lam₁ lam₂ : ℝ) (hK : 0 < K) :
    modeThreshold K q mu lam₁ ≤ modeThreshold K q mu lam₂
      ↔ modeFactor q mu lam₁ ≤ modeFactor q mu lam₂ := by
  unfold modeThreshold
  exact mul_le_mul_iff_right₀ hK

/-- Consequently, the predicate saying that a selected mode minimizes all
modal thresholds is independent of the positive common prefactor. -/
theorem isMinMode_iff {ι : Type*} (K q mu : ℝ) (lam : ι → ℝ) (i₀ : ι)
    (hK : 0 < K) :
    (∀ i, modeThreshold K q mu (lam i₀) ≤ modeThreshold K q mu (lam i))
      ↔ (∀ i, modeFactor q mu (lam i₀) ≤ modeFactor q mu (lam i)) := by
  constructor
  · intro h i
    exact (modeThreshold_le_iff K q mu (lam i₀) (lam i) hK).mp (h i)
  · intro h i
    exact (modeThreshold_le_iff K q mu (lam i₀) (lam i) hK).mpr (h i)

/-- The common physical threshold prefactor.  The arguments stand for
`1 + v*`, `nu`, `gamma`, `u*`, `m + gamma - 1`, and `beta`. -/
noncomputable def thresholdPrefactor
    (w nu gamma u exponent beta : ℝ) : ℝ :=
  w ^ beta / (nu * gamma * u ^ exponent)

/-- The threshold prefactor is positive under the manuscript's primitive
positivity assumptions. -/
theorem thresholdPrefactor_pos (w nu gamma u exponent beta : ℝ)
    (hw : 0 < w) (hnu : 0 < nu) (hgamma : 0 < gamma) (hu : 0 < u) :
    0 < thresholdPrefactor w nu gamma u exponent beta := by
  unfold thresholdPrefactor
  positivity

/-- The minimizing-mode predicate is identical for any two values of `beta`.
This is the manuscript's beta-independence assertion in its literal form. -/
theorem isMinMode_beta_iff {ι : Type*}
    (w nu gamma u exponent q mu beta₁ beta₂ : ℝ)
    (lam : ι → ℝ) (i₀ : ι)
    (hw : 0 < w) (hnu : 0 < nu) (hgamma : 0 < gamma) (hu : 0 < u) :
    (∀ i,
        modeThreshold (thresholdPrefactor w nu gamma u exponent beta₁) q mu (lam i₀)
          ≤ modeThreshold (thresholdPrefactor w nu gamma u exponent beta₁) q mu (lam i))
      ↔ (∀ i,
        modeThreshold (thresholdPrefactor w nu gamma u exponent beta₂) q mu (lam i₀)
          ≤ modeThreshold (thresholdPrefactor w nu gamma u exponent beta₂) q mu (lam i)) := by
  rw [isMinMode_iff _ _ _ _ _
      (thresholdPrefactor_pos w nu gamma u exponent beta₁ hw hnu hgamma hu)]
  rw [isMinMode_iff _ _ _ _ _
      (thresholdPrefactor_pos w nu gamma u exponent beta₂ hw hnu hgamma hu)]

/-- Every positive-mode continuum Neumann eigenvalue is positive. -/
theorem continuumLam_pos (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    0 < ChemotaxisBifurcation.Semidiscrete.continuumLam L n := by
  unfold ChemotaxisBifurcation.Semidiscrete.continuumLam
  positivity

/-- The continuum Neumann eigenvalues along the positive modes diverge. -/
theorem continuumLam_succ_tendsto_atTop (L : ℝ) (hL : 0 < L) :
    Tendsto (fun n : ℕ => ChemotaxisBifurcation.Semidiscrete.continuumLam L (n + 1))
      atTop atTop := by
  have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hscaled : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * Real.pi / L)
      atTop atTop :=
    by
      simpa [mul_comm] using
        (hnat.const_mul_atTop Real.pi_pos).atTop_div_const hL
  simpa [ChemotaxisBifurcation.Semidiscrete.continuumLam, pow_two] using
    hscaled.atTop_mul_atTop₀ hscaled

/-- The beta-free modal factor dominates the eigenvalue itself. -/
theorem lam_le_modeFactor (q mu lam : ℝ)
    (hq : 0 ≤ q) (hmu : 0 ≤ mu) (hlam : 0 < lam) :
    lam ≤ modeFactor q mu lam := by
  have hqm : 0 ≤ q * mu / lam := div_nonneg (mul_nonneg hq hmu) hlam.le
  have hid : modeFactor q mu lam = lam + q + mu + q * mu / lam := by
    unfold modeFactor
    field_simp
    ring
  rw [hid]
  linarith

/-- Every positive-mode beta-free threshold factor is positive. -/
theorem modeFactor_pos (q mu lam : ℝ)
    (hq : 0 ≤ q) (hmu : 0 ≤ mu) (hlam : 0 < lam) :
    0 < modeFactor q mu lam :=
  hlam.trans_le (lam_le_modeFactor q mu lam hq hmu hlam)

/-- Every positive-mode threshold is positive when its common prefactor is
positive. -/
theorem modeThreshold_pos (K q mu lam : ℝ)
    (hK : 0 < K) (hq : 0 ≤ q) (hmu : 0 ≤ mu) (hlam : 0 < lam) :
    0 < modeThreshold K q mu lam := by
  unfold modeThreshold
  exact mul_pos hK (modeFactor_pos q mu lam hq hmu hlam)

/-- The positive-mode modal thresholds diverge to infinity. -/
theorem modeThreshold_succ_tendsto_atTop (L K q mu : ℝ)
    (hL : 0 < L) (hK : 0 < K) (hq : 0 ≤ q) (hmu : 0 ≤ mu) :
    Tendsto
      (fun n : ℕ => modeThreshold K q mu
        (ChemotaxisBifurcation.Semidiscrete.continuumLam L (n + 1))) atTop atTop := by
  have hlam := continuumLam_succ_tendsto_atTop L hL
  have hscaled : Tendsto
      (fun n : ℕ => K * ChemotaxisBifurcation.Semidiscrete.continuumLam L (n + 1))
      atTop atTop := hlam.const_mul_atTop hK
  refine tendsto_atTop_mono (fun n => ?_) hscaled
  exact mul_le_mul_of_nonneg_left
    (lam_le_modeFactor q mu _ hq hmu
      (continuumLam_pos L (n + 1) hL (Nat.succ_pos n))) hK.le

/-- Any real sequence tending to positive infinity attains a global minimum
when indexed by the natural numbers. -/
theorem exists_global_min_of_tendsto_atTop (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop) :
    ∃ n₀, ∀ n, f n₀ ≤ f n := by
  have hev : ∀ᶠ n in atTop, f 0 ≤ f n := hf.eventually_ge_atTop (f 0)
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hnonempty : (Finset.range (N + 1)).Nonempty := by
    exact ⟨0, by simp⟩
  obtain ⟨n₀, hn₀, hmin⟩ :=
    Finset.exists_min_image (Finset.range (N + 1)) f hnonempty
  refine ⟨n₀, fun n => ?_⟩
  by_cases hn : n < N + 1
  · exact hmin n (Finset.mem_range.mpr hn)
  · have hNn : N ≤ n := by omega
    exact (hmin 0 (by simp)).trans (hN n hNn)

/-- Therefore the modal threshold over the positive Neumann modes attains its
minimum, over the positive modes. -/
theorem exists_minimizing_positive_mode (L K q mu : ℝ)
    (hL : 0 < L) (hK : 0 < K) (hq : 0 ≤ q) (hmu : 0 ≤ mu) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, 0 < n →
      modeThreshold K q mu (ChemotaxisBifurcation.Semidiscrete.continuumLam L n₀)
        ≤ modeThreshold K q mu (ChemotaxisBifurcation.Semidiscrete.continuumLam L n) := by
  obtain ⟨j, hj⟩ := exists_global_min_of_tendsto_atTop
    (fun n : ℕ => modeThreshold K q mu
      (ChemotaxisBifurcation.Semidiscrete.continuumLam L (n + 1)))
    (modeThreshold_succ_tendsto_atTop L K q mu hL hK hq hmu)
  refine ⟨j + 1, Nat.succ_pos j, fun n hn => ?_⟩
  have hnrep : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simpa [hnrep] using hj (n - 1)

/-- The legacy modal-factor interface is exactly the current semidiscrete map. -/
theorem modeThreshold_eq_semidiscrete (K q mu lam : ℝ) :
    modeThreshold K q mu lam = Semidiscrete.modeThreshold K q mu lam := rfl

end ChemotaxisBifurcation.Thresholds
