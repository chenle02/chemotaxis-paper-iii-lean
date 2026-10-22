module

public import ChemotaxisBifurcation.RootSigns
public import ChemotaxisBifurcation.NormalizedSpecialization
public import ChemotaxisBifurcation.QuarticRoot

/-!
# Six-decimal root table and physical coefficient signs

The narrow certified intervals below justify the six-decimal values printed in
Table 2.2 for `beta=3/2` and `beta=19/10`.  Each interval is certified by the
Mathlib-only lemma `QuarticRoot.existsUnique_root` (sign change plus a rational
derivative bound, decided by `norm_num`).  The complementary sign theorems
then pass through the positive normalized denominator and the all-ones
physical specialization.
-/

@[expose] public section

namespace ChemotaxisBifurcation.RootTable

open ChemotaxisBifurcation.CertifiedRoots
open ChemotaxisBifurcation.QuarticRoot
open ChemotaxisBifurcation.SpecializedPolynomial
open ChemotaxisBifurcation.NormalizedSpecialization

theorem beta_three_halves_six_decimal_roots :
    (∃! x : ℝ, x ∈ Set.Icc (-12383485 / 10000000 : ℝ)
      (-12383475 / 10000000 : ℝ) ∧ numerator x (3 / 2 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Icc (-6037285 / 10000000 : ℝ)
      (-6037275 / 10000000 : ℝ) ∧ numerator x (3 / 2 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Icc (7734105 / 10000000 : ℝ)
      (7734115 / 10000000 : ℝ) ∧ numerator x (3 / 2 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Icc (15186645 / 10000000 : ℝ)
      (15186655 / 10000000 : ℝ) ∧ numerator x (3 / 2 : ℝ) = 0) := by
  simp only [numerator_eq_quartic]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]

theorem beta_nineteen_tenths_six_decimal_roots :
    (∃! x : ℝ, x ∈ Set.Icc (-14169345 / 10000000 : ℝ)
      (-14169335 / 10000000 : ℝ) ∧ numerator x (19 / 10 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Icc (-6128735 / 10000000 : ℝ)
      (-6128725 / 10000000 : ℝ) ∧ numerator x (19 / 10 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Icc (5301805 / 10000000 : ℝ)
      (5301815 / 10000000 : ℝ) ∧ numerator x (19 / 10 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Icc (38265475 / 10000000 : ℝ)
      (38265485 / 10000000 : ℝ) ∧ numerator x (19 / 10 : ℝ) = 0) := by
  simp only [numerator_eq_quartic]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]

private theorem unique_Ioo_of_unique_Icc {f : ℝ → ℝ} {lo hi : ℝ}
    (h : ∃! x : ℝ, x ∈ Set.Icc lo hi ∧ f x = 0)
    (hlo : f lo ≠ 0) (hhi : f hi ≠ 0) :
    ∃! x : ℝ, x ∈ Set.Ioo lo hi ∧ f x = 0 := by
  rcases h with ⟨x, ⟨hx, hzero⟩, huniq⟩
  have hxlo_ne : x ≠ lo := by
    intro heq
    apply hlo
    simpa [heq] using hzero
  have hxhi_ne : x ≠ hi := by
    intro heq
    apply hhi
    simpa [heq] using hzero
  refine ⟨x, ⟨⟨lt_of_le_of_ne hx.1 hxlo_ne.symm,
    lt_of_le_of_ne hx.2 hxhi_ne⟩, hzero⟩, ?_⟩
  intro y hy
  apply huniq y
  exact ⟨⟨hy.1.1.le, hy.1.2.le⟩, hy.2⟩

/-- Open rounding cells exclude both half-unit endpoint ties, so the four
roots round unambiguously to the six decimals printed for `beta=3/2`. -/
theorem beta_three_halves_rounding_cells :
    (∃! x : ℝ, x ∈ Set.Ioo (-12383485 / 10000000 : ℝ)
      (-12383475 / 10000000 : ℝ) ∧ numerator x (3 / 2 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Ioo (-6037285 / 10000000 : ℝ)
      (-6037275 / 10000000 : ℝ) ∧ numerator x (3 / 2 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Ioo (7734105 / 10000000 : ℝ)
      (7734115 / 10000000 : ℝ) ∧ numerator x (3 / 2 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Ioo (15186645 / 10000000 : ℝ)
      (15186655 / 10000000 : ℝ) ∧ numerator x (3 / 2 : ℝ) = 0) := by
  rcases beta_three_halves_six_decimal_roots with ⟨h1, h2, h3, h4⟩
  exact ⟨unique_Ioo_of_unique_Icc h1 (by norm_num [numerator])
      (by norm_num [numerator]),
    unique_Ioo_of_unique_Icc h2 (by norm_num [numerator])
      (by norm_num [numerator]),
    unique_Ioo_of_unique_Icc h3 (by norm_num [numerator])
      (by norm_num [numerator]),
    unique_Ioo_of_unique_Icc h4 (by norm_num [numerator])
      (by norm_num [numerator])⟩

/-- Open rounding cells exclude both half-unit endpoint ties, so the four
roots round unambiguously to the six decimals printed for `beta=19/10`. -/
theorem beta_nineteen_tenths_rounding_cells :
    (∃! x : ℝ, x ∈ Set.Ioo (-14169345 / 10000000 : ℝ)
      (-14169335 / 10000000 : ℝ) ∧ numerator x (19 / 10 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Ioo (-6128735 / 10000000 : ℝ)
      (-6128725 / 10000000 : ℝ) ∧ numerator x (19 / 10 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Ioo (5301805 / 10000000 : ℝ)
      (5301815 / 10000000 : ℝ) ∧ numerator x (19 / 10 : ℝ) = 0) ∧
    (∃! x : ℝ, x ∈ Set.Ioo (38265475 / 10000000 : ℝ)
      (38265485 / 10000000 : ℝ) ∧ numerator x (19 / 10 : ℝ) = 0) := by
  rcases beta_nineteen_tenths_six_decimal_roots with ⟨h1, h2, h3, h4⟩
  exact ⟨unique_Ioo_of_unique_Icc h1 (by norm_num [numerator])
      (by norm_num [numerator]),
    unique_Ioo_of_unique_Icc h2 (by norm_num [numerator])
      (by norm_num [numerator]),
    unique_Ioo_of_unique_Icc h3 (by norm_num [numerator])
      (by norm_num [numerator]),
    unique_Ioo_of_unique_Icc h4 (by norm_num [numerator])
      (by norm_num [numerator])⟩

/-- The actual all-ones logistic coefficient has the certified sign pattern
for `beta=3/2`. -/
theorem beta_three_halves_physical_signs :
    ∃ r3 r4 : ℝ,
      r3 ∈ Set.Icc (773 / 1000 : ℝ) (774 / 1000 : ℝ) ∧
      r4 ∈ Set.Icc (1518 / 1000 : ℝ) (1519 / 1000 : ℝ) ∧
      (∀ x, 1 / 2 < x → x < r3 →
        0 < logisticBetaCoefficient allOnesParams x (3 / 2 : ℝ)) ∧
      (∀ x, r3 < x → x < r4 →
        logisticBetaCoefficient allOnesParams x (3 / 2 : ℝ) < 0) ∧
      (∀ x, r4 < x →
        0 < logisticBetaCoefficient allOnesParams x (3 / 2 : ℝ)) := by
  rcases RootSigns.beta_three_halves_positive_root_signs with
    ⟨r3, r4, hr3, hr4, hleft, hmid, hright⟩
  refine ⟨r3, r4, hr3, hr4, ?_, ?_, ?_⟩
  · intro x hx hxr
    rw [logisticBetaCoefficient_allOnes hx]
    exact div_pos (hleft x hx hxr) (denominator_pos hx)
  · intro x hrx hxr
    have hx : 1 / 2 < x := by linarith [hr3.1]
    rw [logisticBetaCoefficient_allOnes hx]
    exact div_neg_of_neg_of_pos (hmid x hrx hxr) (denominator_pos hx)
  · intro x hrx
    have hx : 1 / 2 < x := by linarith [hr4.1]
    rw [logisticBetaCoefficient_allOnes hx]
    exact div_pos (hright x hrx) (denominator_pos hx)

/-- The actual all-ones logistic coefficient has the certified sign pattern
for `beta=19/10`. -/
theorem beta_nineteen_tenths_physical_signs :
    ∃ r3 r4 : ℝ,
      r3 ∈ Set.Icc (530 / 1000 : ℝ) (531 / 1000 : ℝ) ∧
      r4 ∈ Set.Icc (3826 / 1000 : ℝ) (3827 / 1000 : ℝ) ∧
      (∀ x, 1 / 2 < x → x < r3 →
        0 < logisticBetaCoefficient allOnesParams x (19 / 10 : ℝ)) ∧
      (∀ x, r3 < x → x < r4 →
        logisticBetaCoefficient allOnesParams x (19 / 10 : ℝ) < 0) ∧
      (∀ x, r4 < x →
        0 < logisticBetaCoefficient allOnesParams x (19 / 10 : ℝ)) := by
  rcases RootSigns.beta_nineteen_tenths_positive_root_signs with
    ⟨r3, r4, hr3, hr4, hleft, hmid, hright⟩
  refine ⟨r3, r4, hr3, hr4, ?_, ?_, ?_⟩
  · intro x hx hxr
    rw [logisticBetaCoefficient_allOnes hx]
    exact div_pos (hleft x hx hxr) (denominator_pos hx)
  · intro x hrx hxr
    have hx : 1 / 2 < x := by linarith [hr3.1]
    rw [logisticBetaCoefficient_allOnes hx]
    exact div_neg_of_neg_of_pos (hmid x hrx hxr) (denominator_pos hx)
  · intro x hrx
    have hx : 1 / 2 < x := by linarith [hr4.1]
    rw [logisticBetaCoefficient_allOnes hx]
    exact div_pos (hright x hrx) (denominator_pos hx)

end ChemotaxisBifurcation.RootTable

end
