module

public import ChemotaxisBifurcation.RootTableRemaining
public import ChemotaxisBifurcation.TwoRootExhaustion

/-!
# Admissible roots in the normalized table

The normalized physical range is `x > 1 / 2`.  These finite consequences of
the exhaustive root classifications identify exactly which displayed roots
lie in that range.  They make no claim about mode selection.
-/

@[expose] public section

namespace ChemotaxisBifurcation.RootTableAdmissible

open SpecializedPolynomial
open RootTableRemaining
open TwoRootExhaustion

noncomputable section

theorem beta_one_no_admissible_root (x : ℝ)
    (hx : numerator x 1 = 0) : ¬(1 / 2 : ℝ) < x := by
  rcases f1_zero_eq_certified_roots with ⟨r1, r2, hr1, hr2, hall⟩
  have hfx : f1 x = 0 := by simpa [f1] using hx
  rcases (hall x).mp hfx with rfl | rfl <;> linarith [hr1.2, hr2.2]

theorem beta_two_unique_admissible_root :
    ∃ r : ℝ,
      r ∈ Set.Ioo (50927905 / 10000000 : ℝ) (50927915 / 10000000 : ℝ) ∧
      numerator r 2 = 0 ∧
      ∀ x : ℝ, numerator x 2 = 0 → ((1 / 2 : ℝ) < x ↔ x = r) := by
  rcases beta_two_roots_exhaust with ⟨r1, r2, r4, hr1, hr2, hr4, hall⟩
  have hr4zero : numerator r4 2 = 0 :=
    (hall r4).mpr (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨r4, hr4, hr4zero, ?_⟩
  intro x hx
  rcases (hall x).mp hx with rfl | rfl | rfl | rfl
  · constructor <;> intro h <;> linarith [hr1.2, hr4.1]
  · constructor <;> intro h <;> linarith [hr2.2, hr4.1]
  · constructor <;> intro h <;> linarith [hr4.1]
  · constructor
    · exact fun _ ↦ rfl
    · intro _
      linarith [hr4.1]

theorem beta_twenty_one_tenths_unique_admissible_root :
    ∃ r : ℝ,
      r ∈ Set.Ioo (73704435 / 10000000 : ℝ) (73704445 / 10000000 : ℝ) ∧
      numerator r (21 / 10) = 0 ∧
      ∀ x : ℝ, numerator x (21 / 10) = 0 → ((1 / 2 : ℝ) < x ↔ x = r) := by
  rcases beta_twenty_one_tenths_roots_exhaust with
    ⟨r1, r2, r3, r4, hr1, hr2, hr3, hr4, hall⟩
  have hr4zero : numerator r4 (21 / 10) = 0 :=
    (hall r4).mpr (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨r4, hr4, hr4zero, ?_⟩
  intro x hx
  rcases (hall x).mp hx with rfl | rfl | rfl | rfl
  · constructor <;> intro h <;> linarith [hr1.2, hr4.1]
  · constructor <;> intro h <;> linarith [hr2.2, hr4.1]
  · constructor <;> intro h <;> linarith [hr3.2, hr4.1]
  · constructor
    · exact fun _ ↦ rfl
    · intro _
      linarith [hr4.1]

theorem beta_seven_thirds_no_admissible_root (x : ℝ)
    (hx : numerator x (7 / 3) = 0) : ¬(1 / 2 : ℝ) < x := by
  rcases beta_seven_thirds_roots_exhaust with
    ⟨r1, r2, r3, hr1, hr2, hr3, hall⟩
  rcases (hall x).mp hx with rfl | rfl | rfl <;>
    linarith [hr1.2, hr2.2, hr3.2]

theorem beta_twelve_fifths_no_admissible_root (x : ℝ)
    (hx : numerator x (12 / 5) = 0) : ¬(1 / 2 : ℝ) < x := by
  rcases beta_twelve_fifths_roots_exhaust with
    ⟨r1, r2, r3, r4, hr1, hr2, hr3, hr4, hall⟩
  rcases (hall x).mp hx with rfl | rfl | rfl | rfl <;>
    linarith [hr1.2, hr2.2, hr3.2, hr4.2]

theorem beta_three_no_admissible_root (x : ℝ)
    (hx : numerator x 3 = 0) : ¬(1 / 2 : ℝ) < x := by
  rcases f3_zero_eq_certified_roots with ⟨r1, r2, hr1, hr2, hall⟩
  have hfx : f3 x = 0 := by simpa [f3] using hx
  rcases (hall x).mp hfx with rfl | rfl <;> linarith [hr1.2, hr2.2]

end

end ChemotaxisBifurcation.RootTableAdmissible

end
