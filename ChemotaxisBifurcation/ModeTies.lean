module
public import ChemotaxisBifurcation.ModeLengths

@[expose] public section

/-!
# The two minimizers at an excluded tie length

At r=c*n*(n+1), precisely n and n+1 minimize the threshold factor.
This is a statement about the finite modal calculation; it does not classify
bifurcation at the two-dimensional critical eigenspace.
-/

namespace ChemotaxisBifurcation.ModeIntervals

open Thresholds

noncomputable section

theorem tied_adjacent_values (q mu c r : ℝ) (n : ℕ)
    (hc : 0 < c) (hn : 0 < n) (hrsq : r ^ 2 = q * mu)
    (htie : r = c * (n : ℝ) * ((n : ℝ) + 1)) :
    modeFactor q mu (modeAt c n) = modeFactor q mu (modeAt c (n + 1)) := by
  have hp : modeAt c n * modeAt c (n + 1) = q * mu := by
    rw [mode_product, Nat.cast_add, Nat.cast_one, ← htie, hrsq]
  have hd : modeFactor q mu (modeAt c (n + 1)) - modeFactor q mu (modeAt c n) = 0 := by
    rw [modeFactor_sub q mu _ _ (modeAt_pos hc hn).ne'
      (modeAt_pos hc (by omega : 0 < n + 1)).ne', hp]
    simp
  exact (sub_eq_zero.mp hd).symm

theorem tied_modes_strictly_below_others (q mu c r : ℝ) (n : ℕ)
    (hc : 0 < c) (hr : 0 < r) (hn : 0 < n)
    (hrsq : r ^ 2 = q * mu) (htie : r = c * (n : ℝ) * ((n : ℝ) + 1)) :
    ∀ m : ℕ, 0 < m → m ≠ n → m ≠ n + 1 →
      modeFactor q mu (modeAt c n) < modeFactor q mu (modeAt c m) := by
  intro m hm hmn hmsucc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hmnR : (m : ℝ) < n := by exact_mod_cast hlt
    have hroot : c * (m : ℝ) * (n : ℝ) < r := by
      rw [htie]
      have hlt' : (m : ℝ) < (n : ℝ) + 1 := by linarith
      have hh := mul_lt_mul_of_pos_left hlt' (mul_pos hc hnR)
      nlinarith
    apply (modeFactor_reverse_lt_iff_product q mu (modeAt c m) (modeAt c n)
      (modeAt_pos hc hm) (modeAt_strictMono hc hlt)).mpr
    rw [mode_product, ← hrsq]
    exact (sq_lt_sq₀ (by positivity) hr.le).mpr hroot
  · have hslt : n + 1 < m := by omega
    have hnmR : (n : ℝ) + 1 < m := by exact_mod_cast hslt
    have hroot : r < c * (n : ℝ) * (m : ℝ) := by
      rw [htie]
      exact mul_lt_mul_of_pos_left hnmR (mul_pos hc hnR)
    apply (modeFactor_lt_iff_product q mu (modeAt c n) (modeAt c m)
      (modeAt_pos hc hn) (modeAt_strictMono hc hgt)).mpr
    rw [mode_product, ← hrsq]
    exact (sq_lt_sq₀ hr.le (by positivity)).mpr hroot

/-- Exact minimum and equality set at a tie. -/
theorem tied_minimizers_exact (q mu c r : ℝ) (n : ℕ)
    (hc : 0 < c) (hr : 0 < r) (hn : 0 < n)
    (hrsq : r ^ 2 = q * mu) (htie : r = c * (n : ℝ) * ((n : ℝ) + 1)) :
    (∀ m : ℕ, 0 < m → modeFactor q mu (modeAt c n) ≤ modeFactor q mu (modeAt c m)) ∧
      (∀ m : ℕ, 0 < m →
        (modeFactor q mu (modeAt c m) = modeFactor q mu (modeAt c n) ↔
          m = n ∨ m = n + 1)) := by
  have heq := tied_adjacent_values q mu c r n hc hn hrsq htie
  have hstrict := tied_modes_strictly_below_others q mu c r n hc hr hn hrsq htie
  constructor
  · intro m hm
    by_cases hmn : m = n
    · subst m; exact le_rfl
    by_cases hms : m = n + 1
    · subst m; exact heq.le
    exact (hstrict m hm hmn hms).le
  · intro m hm
    constructor
    · intro h
      by_cases hmn : m = n
      · exact Or.inl hmn
      by_cases hms : m = n + 1
      · exact Or.inr hms
      have hlt := hstrict m hm hmn hms
      rw [h] at hlt
      exact (lt_irrefl _ hlt).elim
    · rintro (rfl | rfl)
      · rfl
      · exact heq.symm

theorem criticalLength_tie_identity (r : ℝ) (n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    r = (Real.pi / criticalLength r n) ^ 2 * (n : ℝ) * ((n : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnp : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [div_pow, criticalLength_sq r n hr]
  field_simp [hr.ne', hnR.ne', hnp, Real.pi_ne_zero] <;> ring

/-- Literal threshold-factor minimum at the manuscript's boundary L_n. -/
theorem tie_at_criticalLength (q mu r : ℝ) (n : ℕ)
    (hr : 0 < r) (hn : 0 < n) (hrsq : r ^ 2 = q * mu) :
    (∀ m : ℕ, 0 < m →
      modeFactor q mu (Semidiscrete.continuumLam (criticalLength r n) n) ≤
        modeFactor q mu (Semidiscrete.continuumLam (criticalLength r n) m)) ∧
      (∀ m : ℕ, 0 < m →
        (modeFactor q mu (Semidiscrete.continuumLam (criticalLength r n) m) =
          modeFactor q mu (Semidiscrete.continuumLam (criticalLength r n) n) ↔
          m = n ∨ m = n + 1)) := by
  have hL := criticalLength_pos r n hr hn
  have hc : 0 < (Real.pi / criticalLength r n) ^ 2 := by positivity
  simpa only [continuumLam_eq_modeAt] using
    tied_minimizers_exact q mu _ r n hc hr hn hrsq (criticalLength_tie_identity r n hr hn)

end

end ChemotaxisBifurcation.ModeIntervals
