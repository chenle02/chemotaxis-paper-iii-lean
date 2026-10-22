module
public import ChemotaxisBifurcation.ThresholdCutoff

@[expose] public section

/-!
# Convergence of the actual mesh-dependent minimum

The finite cutoff is constructed from the eigenvalue lower bounds. The
continuum threshold is the infimum over all positive integer modes, while the
discrete threshold is the minimum over the modes represented by the mesh.
-/

namespace ChemotaxisBifurcation.Semidiscrete

open Filter
open scoped Topology

noncomputable section

/-- Positive modes represented by a mesh with N intervals. -/
def positiveModes (N : ℕ) : Finset ℕ := Finset.Icc 1 N

theorem positiveModes_nonempty {N : ℕ} (hN : 0 < N) : (positiveModes N).Nonempty :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩

/-- Actual discrete minimum, with a harmless value at the unphysical mesh N=0. -/
def discreteCritical (K q mu L : ℝ) (N : ℕ) : ℝ :=
  if hN : 0 < N then
    (positiveModes N).inf' (positiveModes_nonempty hN)
      (fun n => modeThreshold K q mu (discLam L n N))
  else 0

/-- Continuum threshold over all positive modes. -/
def continuumCritical (K q mu L : ℝ) : ℝ :=
  sInf {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ y = modeThreshold K q mu (continuumLam L n)}

theorem exists_uniform_continuum_tail (K q mu L : ℝ)
    (hK : 0 < K) (hq : 0 ≤ q) (hmu : 0 ≤ mu) (hL : 0 < L) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ n : ℕ, k < n →
      modeThreshold K q mu (continuumLam L 1) <
        modeThreshold K q mu (continuumLam L n) := by
  obtain ⟨k, hk, htail⟩ := exists_quadratic_tail
    (K * Real.pi ^ 2 / L ^ 2)
    (modeThreshold K q mu (continuumLam L 1)) (by positivity)
  refine ⟨k, hk, ?_⟩
  intro n hkn
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hk.trans hkn.le)
  have hlam : 0 < continuumLam L n := by unfold continuumLam; positivity
  have hid : K * Real.pi ^ 2 / L ^ 2 * (n : ℝ) ^ 2 = K * continuumLam L n := by
    unfold continuumLam
    ring
  apply (htail n hkn).trans_le
  rw [hid]
  exact threshold_lower_bound K q mu _ hK.le hq hmu hlam

/-- A continuum tail estimate identifies the actual infinite-mode infimum
with the finite minimum on the retained modes. -/
theorem continuumCritical_eq_finite (K q mu L : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (htail : ∀ n : ℕ, k < n →
      modeThreshold K q mu (continuumLam L 1) ≤
        modeThreshold K q mu (continuumLam L n)) :
    continuumCritical K q mu L =
      (positiveModes k).inf' (positiveModes_nonempty hk)
        (fun n => modeThreshold K q mu (continuumLam L n)) := by
  let f : ℕ → ℝ := fun n => modeThreshold K q mu (continuumLam L n)
  have hne := positiveModes_nonempty hk
  have hleast : IsLeast {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ y = f n}
      ((positiveModes k).inf' hne f) := by
    constructor
    · obtain ⟨n, hn, heq⟩ := Finset.exists_mem_eq_inf' hne f
      exact ⟨n, (Finset.mem_Icc.mp hn).1, heq⟩
    · rintro y ⟨n, hn, rfl⟩
      by_cases hnk : n ≤ k
      · exact Finset.inf'_le f (Finset.mem_Icc.mpr ⟨hn, hnk⟩)
      · exact (Finset.inf'_le f (Finset.mem_Icc.mpr ⟨le_rfl, hk⟩)).trans
          (htail n (lt_of_not_ge hnk))
  exact hleast.csInf_eq

/-- Theorem 1.4's threshold convergence for a positive prefactor and
nonnegative reaction/mass parameters. The proof constructs both tail cutoffs. -/
theorem discreteCritical_tendsto_continuumCritical (K q mu L : ℝ)
    (hK : 0 < K) (hq : 0 ≤ q) (hmu : 0 ≤ mu) (hL : 0 < L) :
    Tendsto (discreteCritical K q mu L) atTop (𝓝 (continuumCritical K q mu L)) := by
  obtain ⟨kd, hkd, hd⟩ := exists_uniform_discrete_tail K q mu L hK hq hmu hL
  obtain ⟨kc, hkc, hc⟩ := exists_uniform_continuum_tail K q mu L hK hq hmu hL
  let k := max kd kc
  have hk : 1 ≤ k := hkd.trans (le_max_left _ _)
  have hne := positiveModes_nonempty hk
  have hpos : ∀ n ∈ positiveModes k, 0 < n := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).1
  have hlimit : continuumCritical K q mu L =
      (positiveModes k).inf' hne (fun n => modeThreshold K q mu (continuumLam L n)) :=
    continuumCritical_eq_finite K q mu L k hk (fun n hn =>
      (hc n (lt_of_le_of_lt (le_max_right _ _) hn)).le)
  apply critical_threshold_tendsto_of_finite_cutoff
    (positiveModes k) hne hpos K q mu L hL
    (discreteCritical K q mu L) (continuumCritical K q mu L) _ hlimit
  filter_upwards [hd, eventually_ge_atTop k] with N hNtail hkN
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (hk.trans hkN)
  unfold discreteCritical
  rw [dif_pos hN]
  apply finite_infimum_eq_of_tail hne (positiveModes_nonempty hN) (j := 1)
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hkN⟩
  · exact Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
  · intro n hn hnS
    have hnk : k < n := by
      by_contra h
      exact hnS (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, le_of_not_gt h⟩)
    exact (hNtail n (lt_of_le_of_lt (le_max_left _ _) hnk) (Finset.mem_Icc.mp hn).2).le

end

end ChemotaxisBifurcation.Semidiscrete
