module

public import ChemotaxisBifurcation.NormalizedLimits
public import ChemotaxisBifurcation.RootTable
public import ChemotaxisBifurcation.ModeRealization

/-!
# Finite mode consequences for the normalized examples

The certified positive roots at `beta=3/2` and `beta=19/10` are placed in the
exact strict-mode corridors.  This records which Neumann indices each root can
realize; it does not classify mode ties.
-/

@[expose] public section

namespace ChemotaxisBifurcation.ModeExamples

open PhysicalModeGuards ModeIntervals SpecializedPolynomial
open ChemotaxisBifurcation.RootTable
open ChemotaxisBifurcation.NormalizedSpecialization

noncomputable section

def realizedMode (beta x : ℝ) (n : ℕ) : Prop :=
  StrictCriticalMode allOnesParams ⟨lengthForEigenvalue n x, n⟩ beta

theorem realizedMode_iff (beta x : ℝ) (n : ℕ) (hn : 0 < n) (hx : 0 < x) :
    realizedMode beta x n ↔
      (n : ℝ) / ((n : ℝ) + 1) < x ∧
        (n = 1 ∨ x < (n : ℝ) / ((n : ℝ) - 1)) := by
  unfold realizedMode
  have h := physical_realization_iff allOnesParams beta 1 x n
    (logistic_positive_parameters allOnesParams allOnes_admissible) hn hx
    (by norm_num) (by norm_num [allOnesParams, PhysicalParams.logisticSlope])
  simpa using h

private theorem x_pos_of_realizedMode {beta x : ℝ} {n : ℕ}
    (hmode : realizedMode beta x n) : 0 < x := by
  unfold realizedMode at hmode
  have hn : 0 < n := hmode.2.1
  have hnum : 0 < (n : ℝ) * Real.pi := by positivity
  have hL := hmode.1
  change 0 < (n : ℝ) * Real.pi / Real.sqrt x at hL
  rcases (div_pos_iff.mp hL) with h | h
  · exact Real.sqrt_pos.mp h.2
  · exact (not_lt_of_ge hnum.le h.1).elim

private theorem lower_corridor_ge_two_thirds (n : ℕ) (hn : 2 ≤ n) :
    (2 / 3 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem lower_corridor_ge_four_fifths (n : ℕ) (hn : 4 ≤ n) :
    (4 / 5 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem upper_corridor_le_three_halves (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) / ((n : ℝ) - 1) ≤ 3 / 2 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 1 := by linarith
  apply (div_le_iff₀ hden).2
  nlinarith

private theorem upper_corridor_le_two (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) / ((n : ℝ) - 1) ≤ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 1 := by linarith
  apply (div_le_iff₀ hden).2
  nlinarith

theorem beta_three_halves_lower_root_modes :
    ∃ x : ℝ,
      x ∈ Set.Ioo (7734105 / 10000000 : ℝ) (7734115 / 10000000 : ℝ) ∧
      numerator x (3 / 2) = 0 ∧
      realizedMode (3 / 2) x 1 ∧ realizedMode (3 / 2) x 2 ∧
      realizedMode (3 / 2) x 3 ∧
      ∀ n : ℕ, 4 ≤ n → ¬ realizedMode (3 / 2) x n := by
  rcases beta_three_halves_rounding_cells.2.2.1 with ⟨x, hx, -⟩
  have hxpos : 0 < x := by linarith [hx.1.1]
  refine ⟨x, hx.1, hx.2, ?_, ?_, ?_, ?_⟩
  · rw [realizedMode_iff _ _ 1 (by norm_num) hxpos]
    norm_num
    linarith [hx.1.1]
  · rw [realizedMode_iff _ _ 2 (by norm_num) hxpos]
    norm_num
    constructor <;> linarith [hx.1.1, hx.1.2]
  · rw [realizedMode_iff _ _ 3 (by norm_num) hxpos]
    norm_num
    constructor <;> linarith [hx.1.1, hx.1.2]
  · intro n hn hmode
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hc := (realizedMode_iff (3 / 2) x n hnpos hxpos).mp hmode
    have hlower := lower_corridor_ge_four_fifths n hn
    linarith [hx.1.2]

theorem beta_three_halves_upper_root_modes :
    ∃ x : ℝ,
      x ∈ Set.Ioo (15186645 / 10000000 : ℝ) (15186655 / 10000000 : ℝ) ∧
      numerator x (3 / 2) = 0 ∧
      realizedMode (3 / 2) x 1 ∧ realizedMode (3 / 2) x 2 ∧
      ∀ n : ℕ, 3 ≤ n → ¬ realizedMode (3 / 2) x n := by
  rcases beta_three_halves_rounding_cells.2.2.2 with ⟨x, hx, -⟩
  have hxpos : 0 < x := by linarith [hx.1.1]
  refine ⟨x, hx.1, hx.2, ?_, ?_, ?_⟩
  · rw [realizedMode_iff _ _ 1 (by norm_num) hxpos]
    norm_num
    linarith [hx.1.1]
  · rw [realizedMode_iff _ _ 2 (by norm_num) hxpos]
    norm_num
    constructor <;> linarith [hx.1.1, hx.1.2]
  · intro n hn hmode
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hc := (realizedMode_iff (3 / 2) x n hnpos hxpos).mp hmode
    rcases hc.2 with hnone | hupper
    · omega
    · have hu := upper_corridor_le_three_halves n hn
      linarith [hx.1.1]

theorem beta_nineteen_tenths_lower_root_modes :
    ∃ x : ℝ,
      x ∈ Set.Ioo (5301805 / 10000000 : ℝ) (5301815 / 10000000 : ℝ) ∧
      numerator x (19 / 10) = 0 ∧ realizedMode (19 / 10) x 1 ∧
      ∀ n : ℕ, 2 ≤ n → ¬ realizedMode (19 / 10) x n := by
  rcases beta_nineteen_tenths_rounding_cells.2.2.1 with ⟨x, hx, -⟩
  have hxpos : 0 < x := by linarith [hx.1.1]
  refine ⟨x, hx.1, hx.2, ?_, ?_⟩
  · rw [realizedMode_iff _ _ 1 (by norm_num) hxpos]
    norm_num
    linarith [hx.1.1]
  · intro n hn hmode
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hc := (realizedMode_iff (19 / 10) x n hnpos hxpos).mp hmode
    have hlower := lower_corridor_ge_two_thirds n hn
    linarith [hx.1.2]

theorem beta_nineteen_tenths_upper_root_modes :
    ∃ x : ℝ,
      x ∈ Set.Ioo (38265475 / 10000000 : ℝ) (38265485 / 10000000 : ℝ) ∧
      numerator x (19 / 10) = 0 ∧ realizedMode (19 / 10) x 1 ∧
      ∀ n : ℕ, 2 ≤ n → ¬ realizedMode (19 / 10) x n := by
  rcases beta_nineteen_tenths_rounding_cells.2.2.2 with ⟨x, hx, -⟩
  have hxpos : 0 < x := by linarith [hx.1.1]
  refine ⟨x, hx.1, hx.2, ?_, ?_⟩
  · rw [realizedMode_iff _ _ 1 (by norm_num) hxpos]
    norm_num
    linarith [hx.1.1]
  · intro n hn hmode
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hc := (realizedMode_iff (19 / 10) x n hnpos hxpos).mp hmode
    rcases hc.2 with hnone | hupper
    · omega
    · have hu := upper_corridor_le_two n hn
      linarith [hx.1.1]

theorem beta_three_halves_modes_one_two_signs :
    ∃ r3 r4 : ℝ,
      r3 ∈ Set.Icc (773 / 1000 : ℝ) (774 / 1000 : ℝ) ∧
      r4 ∈ Set.Icc (1518 / 1000 : ℝ) (1519 / 1000 : ℝ) ∧
      ∀ n : ℕ, (n = 1 ∨ n = 2) → ∀ x : ℝ, realizedMode (3 / 2) x n →
        (x < r3 → 0 < logisticBetaCoefficient allOnesParams x (3 / 2)) ∧
        (r3 < x → x < r4 → logisticBetaCoefficient allOnesParams x (3 / 2) < 0) ∧
        (r4 < x → 0 < logisticBetaCoefficient allOnesParams x (3 / 2)) := by
  rcases beta_three_halves_physical_signs with
    ⟨r3, r4, hr3, hr4, hleft, hmid, hright⟩
  refine ⟨r3, r4, hr3, hr4, ?_⟩
  intro n hn x hmode
  rcases hn with rfl | rfl
  · have hxpos : 0 < x := x_pos_of_realizedMode hmode
    have hc := (realizedMode_iff (3 / 2) x 1 (by norm_num) hxpos).mp hmode
    norm_num at hc
    exact ⟨fun hxr ↦ hleft x (by linarith [hc]) hxr,
      ⟨fun hrx hxr ↦ hmid x hrx hxr, fun hrx ↦ hright x hrx⟩⟩
  · have hxpos : 0 < x := x_pos_of_realizedMode hmode
    have hc := (realizedMode_iff (3 / 2) x 2 (by norm_num) hxpos).mp hmode
    norm_num at hc
    exact ⟨fun hxr ↦ hleft x (by linarith [hc.1]) hxr,
      ⟨fun hrx hxr ↦ hmid x hrx hxr, fun hrx ↦ hright x hrx⟩⟩

theorem beta_three_halves_mode_three_signs :
    ∃ r3 : ℝ,
      r3 ∈ Set.Icc (773 / 1000 : ℝ) (774 / 1000 : ℝ) ∧
      ∀ x : ℝ, realizedMode (3 / 2) x 3 →
        (x < r3 → 0 < logisticBetaCoefficient allOnesParams x (3 / 2)) ∧
        (r3 < x → logisticBetaCoefficient allOnesParams x (3 / 2) < 0) := by
  rcases beta_three_halves_physical_signs with
    ⟨r3, r4, hr3, hr4, hleft, hmid, -⟩
  refine ⟨r3, hr3, ?_⟩
  intro x hmode
  have hxpos : 0 < x := x_pos_of_realizedMode hmode
  have hc := (realizedMode_iff (3 / 2) x 3 (by norm_num) hxpos).mp hmode
  norm_num at hc
  refine ⟨fun hxr ↦ hleft x (by linarith [hc.1]) hxr, ?_⟩
  intro hrx
  apply hmid x hrx
  linarith [hc.2, hr4.1]

theorem beta_three_halves_higher_modes_negative :
    ∀ n : ℕ, 4 ≤ n → ∀ x : ℝ, realizedMode (3 / 2) x n →
      logisticBetaCoefficient allOnesParams x (3 / 2) < 0 := by
  rcases beta_three_halves_physical_signs with
    ⟨r3, r4, hr3, hr4, -, hmid, -⟩
  intro n hn x hmode
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hxpos : 0 < x := x_pos_of_realizedMode hmode
  have hc := (realizedMode_iff (3 / 2) x n hnpos hxpos).mp hmode
  apply hmid x
  · have hlower := lower_corridor_ge_four_fifths n hn
    linarith [hc.1, hr3.2]
  · rcases hc.2 with hnone | hupper
    · omega
    · have hu := upper_corridor_le_three_halves n (le_trans (by norm_num) hn)
      linarith [hr4.1]

theorem beta_nineteen_tenths_mode_one_signs :
    ∃ r3 r4 : ℝ,
      r3 ∈ Set.Icc (530 / 1000 : ℝ) (531 / 1000 : ℝ) ∧
      r4 ∈ Set.Icc (3826 / 1000 : ℝ) (3827 / 1000 : ℝ) ∧
      ∀ x : ℝ, realizedMode (19 / 10) x 1 →
        (x < r3 → 0 < logisticBetaCoefficient allOnesParams x (19 / 10)) ∧
        (r3 < x → x < r4 → logisticBetaCoefficient allOnesParams x (19 / 10) < 0) ∧
        (r4 < x → 0 < logisticBetaCoefficient allOnesParams x (19 / 10)) := by
  rcases beta_nineteen_tenths_physical_signs with
    ⟨r3, r4, hr3, hr4, hleft, hmid, hright⟩
  refine ⟨r3, r4, hr3, hr4, ?_⟩
  intro x hmode
  have hxpos : 0 < x := x_pos_of_realizedMode hmode
  have hc := (realizedMode_iff (19 / 10) x 1 (by norm_num) hxpos).mp hmode
  norm_num at hc
  exact ⟨fun hxr ↦ hleft x (by linarith [hc]) hxr,
    ⟨fun hrx hxr ↦ hmid x hrx hxr, fun hrx ↦ hright x hrx⟩⟩

theorem beta_nineteen_tenths_higher_modes_negative :
    ∀ n : ℕ, 2 ≤ n → ∀ x : ℝ, realizedMode (19 / 10) x n →
      logisticBetaCoefficient allOnesParams x (19 / 10) < 0 := by
  rcases beta_nineteen_tenths_physical_signs with
    ⟨r3, r4, hr3, hr4, -, hmid, -⟩
  intro n hn x hmode
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hxpos : 0 < x := x_pos_of_realizedMode hmode
  have hc := (realizedMode_iff (19 / 10) x n hnpos hxpos).mp hmode
  apply hmid x
  · have hlower := lower_corridor_ge_two_thirds n hn
    linarith [hc.1, hr3.2]
  · rcases hc.2 with hnone | hupper
    · omega
    · have hu := upper_corridor_le_two n hn
      linarith [hr4.1]

end

end ChemotaxisBifurcation.ModeExamples

end
