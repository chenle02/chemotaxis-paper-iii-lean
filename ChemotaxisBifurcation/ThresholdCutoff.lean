module
public import ChemotaxisBifurcation.Semidiscrete

@[expose] public section

/-!
# A uniform discrete minimizing-mode cutoff

This is the extra tail argument needed beyond fixed-mode convergence in
Theorem 1.4. It constructs a cutoff from the first-mode limit and the quadratic
lower bound. It does not assume the existence of such a cutoff.
-/

namespace ChemotaxisBifurcation.Semidiscrete

open Filter
open scoped Topology

/-- A positive quadratic sequence eventually exceeds any prescribed bound. -/
theorem exists_quadratic_tail (c M : ℝ) (hc : 0 < c) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ n : ℕ, k < n → M < c * (n : ℝ) ^ 2 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (M / c))
  have hk1 : (1 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkn : 1 < k := by exact_mod_cast hk1
  refine ⟨k, hkn.le, ?_⟩
  intro n hn
  have hnr : (k : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) < n := hk1.trans hnr
  have hratio : M / c < n := (lt_of_le_of_lt (le_max_right _ _) hk).trans hnr
  have hM : M < (n : ℝ) * c := (div_lt_iff₀ hc).mp hratio
  have hs : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs hc.le
  nlinarith

/-- For all sufficiently fine meshes, every represented mode beyond one fixed
cutoff has threshold strictly greater than the first mode's threshold. -/
theorem exists_uniform_discrete_tail (K q mu L : ℝ)
    (hK : 0 < K) (hq : 0 ≤ q) (hmu : 0 ≤ mu) (hL : 0 < L) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ᶠ N in atTop,
      ∀ n : ℕ, k < n → n ≤ N →
        modeThreshold K q mu (discLam L 1 N) <
          modeThreshold K q mu (discLam L n N) := by
  let M := modeThreshold K q mu (continuumLam L 1) + 1
  have hfirst := modeThreshold_disc_tendsto L 1 K q mu hL Nat.one_pos
  have hbounded : ∀ᶠ N in atTop, modeThreshold K q mu (discLam L 1 N) < M :=
    hfirst.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨k, hk, htail⟩ := exists_quadratic_tail (4 * K / L ^ 2) M (by positivity)
  refine ⟨k, hk, ?_⟩
  filter_upwards [hbounded, eventually_gt_atTop (0 : ℕ)] with N hNbound hN
  intro n hkn hnN
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hk.trans hkn.le)
  have hlower := discLam_lower_bound L n N hL hN hnN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlam : 0 < discLam L n N := lt_of_lt_of_le (by positivity) hlower
  have hscaled : (4 * K / L ^ 2) * (n : ℝ) ^ 2 ≤ K * discLam L n N := by
    calc
      (4 * K / L ^ 2) * (n : ℝ) ^ 2 = K * (4 * (n : ℝ) ^ 2 / L ^ 2) := by ring
      _ ≤ K * discLam L n N := mul_le_mul_of_nonneg_left hlower hK.le
  exact hNbound.trans ((htail n hkn).trans_le
    (hscaled.trans (threshold_lower_bound K q mu _ hK.le hq hmu hlam)))

/-- A finite minimum is unchanged after excluding modes above a known member.
This order lemma is the bridge between a tail estimate and a truncated minimum. -/
theorem finite_infimum_eq_of_tail {S T : Finset ℕ}
    (hS : S.Nonempty) (hT : T.Nonempty) (hsub : S ⊆ T)
    (f : ℕ → ℝ) (j : ℕ) (hj : j ∈ S)
    (htail : ∀ n ∈ T, n ∉ S → f j ≤ f n) :
    T.inf' hT f = S.inf' hS f := by
  apply le_antisymm
  · apply Finset.le_inf' hS f
    intro n hn
    exact Finset.inf'_le f (hsub hn)
  · apply Finset.le_inf' hT f
    intro n hn
    by_cases hnS : n ∈ S
    · exact Finset.inf'_le f hnS
    · exact (Finset.inf'_le f hj).trans (htail n hn hnS)

end ChemotaxisBifurcation.Semidiscrete
