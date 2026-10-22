module
public import ChemotaxisBifurcation.ModeLengths
public import ChemotaxisBifurcation.ModeRootCounts

@[expose] public section

/-!
# Realizing admissible eigenvalues by unique positive domain lengths

This supplies the converse needed to turn certified polynomial roots inside a
mode corridor into actual domain lengths. Strict corridors exclude mode ties.
-/
namespace ChemotaxisBifurcation.ModeIntervals

open PhysicalModeGuards
noncomputable section

def lengthForEigenvalue (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * Real.pi / Real.sqrt x

theorem lengthForEigenvalue_pos (n : ℕ) (x : ℝ) (hn : 0 < n) (hx : 0 < x) :
    0 < lengthForEigenvalue n x := by
  unfold lengthForEigenvalue
  positivity

theorem continuumLam_lengthForEigenvalue (n : ℕ) (x : ℝ)
    (hn : 0 < n) (hx : 0 < x) :
    Semidiscrete.continuumLam (lengthForEigenvalue n x) n = x := by
  have ha : (n : ℝ) * Real.pi ≠ 0 := ne_of_gt (by positivity)
  have he : (n : ℝ) * Real.pi / ((n : ℝ) * Real.pi / Real.sqrt x) =
      Real.sqrt x := by field_simp [ha]
  unfold Semidiscrete.continuumLam lengthForEigenvalue
  rw [he, Real.sq_sqrt hx.le]

theorem unique_lengthForEigenvalue (n : ℕ) (x L : ℝ)
    (hn : 0 < n) (hx : 0 < x) (hL : 0 < L) :
    Semidiscrete.continuumLam L n = x ↔ L = lengthForEigenvalue n x := by
  constructor
  · intro h
    apply ModeRootCounts.eigenvalue_injOn_positive n hn hL
      (lengthForEigenvalue_pos n x hn hx)
    change Semidiscrete.continuumLam L n =
      Semidiscrete.continuumLam (lengthForEigenvalue n x) n
    rw [h, continuumLam_lengthForEigenvalue n x hn hx]
  · rintro rfl
    exact continuumLam_lengthForEigenvalue n x hn hx

theorem modeCell_iff_corridor (c r : ℝ) (n : ℕ)
    (hr : 0 < r) (hn : 0 < n) :
    modeCell c r n ↔
      r * (n : ℝ) / ((n : ℝ) + 1) < modeAt c n ∧
        (n = 1 ∨ modeAt c n < r * (n : ℝ) / ((n : ℝ) - 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h
    refine ⟨cell_lower_corridor c r n hn h, ?_⟩
    by_cases h1 : n = 1
    · exact Or.inl h1
    · exact Or.inr (cell_upper_corridor c r n (by omega) h)
  · rintro ⟨hl, hu⟩
    have hl' := (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp hl
    simp only [modeAt] at hl'
    have hupper : r < c * (n : ℝ) * ((n : ℝ) + 1) := by
      apply (mul_lt_mul_iff_right₀ hnR).mp
      convert hl' using 1 <;> ring
    refine ⟨?_, hupper⟩
    rcases hu with h1 | hu
    · simpa [h1] using hr
    · by_cases h1 : n = 1
      · simpa [h1] using hr
      · have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
        have hu' := (lt_div_iff₀ (sub_pos.mpr hn1)).mp hu
        simp only [modeAt] at hu'
        apply (mul_lt_mul_iff_right₀ hnR).mp
        convert hu' using 1 <;> ring

theorem physical_critical_eigenvalue_corridor_iff
    (p : PhysicalParams) (d : ModeData) (beta r : ℝ)
    (hp : PositiveModeParameters p) (hL : 0 < d.L) (hn : 0 < d.n0)
    (hr : 0 < r) (hrsq : r ^ 2 = p.logisticSlope * p.mu) :
    StrictCriticalMode p d beta ↔
      r * (d.n0 : ℝ) / ((d.n0 : ℝ) + 1) < d.eigenvalue ∧
        (d.n0 = 1 ∨ d.eigenvalue < r * (d.n0 : ℝ) / ((d.n0 : ℝ) - 1)) := by
  have hc : 0 < (Real.pi / d.L) ^ 2 := by positivity
  rw [physical_strictMode_iff p d beta hp hL,
    strictMode_iff_cell p.logisticSlope p.mu _ r d.n0 hc hr hrsq hn,
    modeCell_iff_corridor _ r d.n0 hr hn, data_eigenvalue_eq_modeAt]

theorem physical_realization_iff (p : PhysicalParams) (beta r x : ℝ) (n : ℕ)
    (hp : PositiveModeParameters p) (hn : 0 < n) (hx : 0 < x)
    (hr : 0 < r) (hrsq : r ^ 2 = p.logisticSlope * p.mu) :
    StrictCriticalMode p ⟨lengthForEigenvalue n x, n⟩ beta ↔
      r * (n : ℝ) / ((n : ℝ) + 1) < x ∧
        (n = 1 ∨ x < r * (n : ℝ) / ((n : ℝ) - 1)) := by
  rw [physical_critical_eigenvalue_corridor_iff p _ beta r hp
    (lengthForEigenvalue_pos n x hn hx) hn hr hrsq]
  change (_ < Semidiscrete.continuumLam (lengthForEigenvalue n x) n ∧
    (_ ∨ Semidiscrete.continuumLam (lengthForEigenvalue n x) n < _)) ↔ _
  rw [continuumLam_lengthForEigenvalue n x hn hx]

end
end ChemotaxisBifurcation.ModeIntervals
