module

public import ChemotaxisBifurcation.SpecializedPolynomial
public import ChemotaxisBifurcation.QuarticRoot

/-!
# Certified intervals for the normalized quartic

This module checks the eight root intervals of width `1/1000` used in the
current manuscript's beta `3/2` and beta `19/10` examples (two positive and two
negative roots for each beta).  Each proof applies the Mathlib-only certificate
`QuarticRoot.existsUnique_root`: a sign change at the endpoints and a rational
derivative bound, both decided by `norm_num` (route C, 2026-10-17; before, the
intervals were checked by an external interval-arithmetic tactic).

Source baseline: `09-26-2026-CRS-3-Le.tex`, SHA-256
`6132a4f21e03eca32dfcc1d242be718bf401ca0c63b7777c7149da263708d6ee`,
lines 1977--2125.  The table is Table 2.2 (page 23).

Each theorem gives a unique root in one closed rational interval.  These eight
local certificates do not prove that the quartic has no other admissible roots
and do not by themselves prove the sign on every complementary interval.
-/

@[expose] public section

namespace ChemotaxisBifurcation.CertifiedRoots

open ChemotaxisBifurcation.SpecializedPolynomial
open ChemotaxisBifurcation.QuarticRoot

/-- The normalized numerator is the quartic `QuarticRoot.q` in `lambda` whose
coefficients are its displayed polynomials in `beta`. -/
theorem numerator_eq_quartic (lambda beta : ℝ) :
    numerator lambda beta =
      q (224 - 96 * beta) (192 - 152 * beta) (8 - 104 * beta - 16 * beta ^ 2)
        (96 - 28 * beta - 8 * beta ^ 2) (56 + 11 * beta - beta ^ 2) lambda := by
  unfold numerator q
  ring

theorem beta_three_halves_first_root :
    ∃! x : ℝ, x ∈ Set.Icc (773 / 1000 : ℝ) (774 / 1000 : ℝ) ∧
      numerator x (3 / 2 : ℝ) = 0 := by
  simp only [numerator_eq_quartic]
  apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]

theorem beta_three_halves_second_root :
    ∃! x : ℝ, x ∈ Set.Icc (1518 / 1000 : ℝ) (1519 / 1000 : ℝ) ∧
      numerator x (3 / 2 : ℝ) = 0 := by
  simp only [numerator_eq_quartic]
  apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]

theorem beta_nineteen_tenths_first_root :
    ∃! x : ℝ, x ∈ Set.Icc (530 / 1000 : ℝ) (531 / 1000 : ℝ) ∧
      numerator x (19 / 10 : ℝ) = 0 := by
  simp only [numerator_eq_quartic]
  apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]

theorem beta_nineteen_tenths_second_root :
    ∃! x : ℝ, x ∈ Set.Icc (3826 / 1000 : ℝ) (3827 / 1000 : ℝ) ∧
      numerator x (19 / 10 : ℝ) = 0 := by
  simp only [numerator_eq_quartic]
  apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]

theorem beta_three_halves_negative_first_root :
    ∃! x : ℝ, x ∈ Set.Icc (-1239 / 1000 : ℝ) (-1238 / 1000 : ℝ) ∧
      numerator x (3 / 2 : ℝ) = 0 := by
  simp only [numerator_eq_quartic]
  apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]

theorem beta_three_halves_negative_second_root :
    ∃! x : ℝ, x ∈ Set.Icc (-604 / 1000 : ℝ) (-603 / 1000 : ℝ) ∧
      numerator x (3 / 2 : ℝ) = 0 := by
  simp only [numerator_eq_quartic]
  apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]

theorem beta_nineteen_tenths_negative_first_root :
    ∃! x : ℝ, x ∈ Set.Icc (-1417 / 1000 : ℝ) (-1416 / 1000 : ℝ) ∧
      numerator x (19 / 10 : ℝ) = 0 := by
  simp only [numerator_eq_quartic]
  apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]

theorem beta_nineteen_tenths_negative_second_root :
    ∃! x : ℝ, x ∈ Set.Icc (-613 / 1000 : ℝ) (-612 / 1000 : ℝ) ∧
      numerator x (19 / 10 : ℝ) = 0 := by
  simp only [numerator_eq_quartic]
  apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]

end ChemotaxisBifurcation.CertifiedRoots

end
