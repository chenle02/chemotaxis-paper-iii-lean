module

public import ChemotaxisBifurcation.RootExhaustion
public import ChemotaxisBifurcation.RootTable
public import ChemotaxisBifurcation.RootTableAdmissible

/-!
# Table 3.2 as two aggregate statements

arXiv:2610.20976v1, Table 3.2 (`Tb:polynomial-roots`, p. 27) lists, for eight values of `β`,
the real roots of `P(λ, β)` rounded to six decimals and the roots with `λ > 1/2`. Here
`P = SpecializedPolynomial.numerator`, the numerator displayed in Example 3.1
(`CoefficientDictionary.example_3_1_display` identifies it with the all-ones coefficient).

* `table_3_2_real_roots`: for each of the eight rows, the real roots of `P(·, β)` are exactly
  the listed number of roots, each in the open cell of width `10⁻⁶` around its printed
  six-decimal value (the exact root `1/2` for `β = 2`).
* `table_3_2_admissible_roots`: the third column; for `β = 1, 7/3, 2.4, 3` no root exceeds
  `1/2`, for `β = 2, 2.1` exactly one does, and for `β = 1.5, 1.9` exactly the two listed ones.

Both only collect the per-row theorems of `RootExhaustion`, `RootTable`, `RootTableRemaining`,
`TwoRootExhaustion` and `RootTableAdmissible`; the rows `β = 1.5, 1.9` combine the three-decimal
exhaustion with the six-decimal rounding cells.
-/

@[expose] public section

namespace ChemotaxisBifurcation.RootTableAggregate

open Set
open ChemotaxisBifurcation.SpecializedPolynomial

noncomputable section

/-- Row `β = 3/2` with six-decimal cells: exactly four real roots. -/
theorem beta_three_halves_roots_six_decimal :
    ∃ r1 r2 r3 r4 : ℝ,
      r1 ∈ Ioo (-12383485 / 10000000 : ℝ) (-12383475 / 10000000) ∧
      r2 ∈ Ioo (-6037285 / 10000000 : ℝ) (-6037275 / 10000000) ∧
      r3 ∈ Ioo (7734105 / 10000000 : ℝ) (7734115 / 10000000) ∧
      r4 ∈ Ioo (15186645 / 10000000 : ℝ) (15186655 / 10000000) ∧
      ∀ x : ℝ, numerator x (3 / 2) = 0 ↔ x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4 := by
  obtain ⟨⟨s1, ⟨hs1, hz1⟩, -⟩, ⟨s2, ⟨hs2, hz2⟩, -⟩, ⟨s3, ⟨hs3, hz3⟩, -⟩,
    ⟨s4, ⟨hs4, hz4⟩, -⟩⟩ := RootTable.beta_three_halves_rounding_cells
  obtain ⟨r1, r2, r3, r4, h1, h2, h3, h4, hall⟩ :=
    RootExhaustion.beta_three_halves_roots_exhaust
  have e1 : s1 = r1 := by
    rcases (hall s1).mp hz1 with h | h | h | h <;> subst h <;>
      first | rfl | (exfalso; linarith [hs1.1, hs1.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
        h4.1, h4.2])
  have e2 : s2 = r2 := by
    rcases (hall s2).mp hz2 with h | h | h | h <;> subst h <;>
      first | rfl | (exfalso; linarith [hs2.1, hs2.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
        h4.1, h4.2])
  have e3 : s3 = r3 := by
    rcases (hall s3).mp hz3 with h | h | h | h <;> subst h <;>
      first | rfl | (exfalso; linarith [hs3.1, hs3.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
        h4.1, h4.2])
  have e4 : s4 = r4 := by
    rcases (hall s4).mp hz4 with h | h | h | h <;> subst h <;>
      first | rfl | (exfalso; linarith [hs4.1, hs4.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
        h4.1, h4.2])
  subst e1 e2 e3 e4
  exact ⟨s1, s2, s3, s4, hs1, hs2, hs3, hs4, hall⟩

/-- Row `β = 19/10` with six-decimal cells: exactly four real roots. -/
theorem beta_nineteen_tenths_roots_six_decimal :
    ∃ r1 r2 r3 r4 : ℝ,
      r1 ∈ Ioo (-14169345 / 10000000 : ℝ) (-14169335 / 10000000) ∧
      r2 ∈ Ioo (-6128735 / 10000000 : ℝ) (-6128725 / 10000000) ∧
      r3 ∈ Ioo (5301805 / 10000000 : ℝ) (5301815 / 10000000) ∧
      r4 ∈ Ioo (38265475 / 10000000 : ℝ) (38265485 / 10000000) ∧
      ∀ x : ℝ, numerator x (19 / 10) = 0 ↔ x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4 := by
  obtain ⟨⟨s1, ⟨hs1, hz1⟩, -⟩, ⟨s2, ⟨hs2, hz2⟩, -⟩, ⟨s3, ⟨hs3, hz3⟩, -⟩,
    ⟨s4, ⟨hs4, hz4⟩, -⟩⟩ := RootTable.beta_nineteen_tenths_rounding_cells
  obtain ⟨r1, r2, r3, r4, h1, h2, h3, h4, hall⟩ :=
    RootExhaustion.beta_nineteen_tenths_roots_exhaust
  have e1 : s1 = r1 := by
    rcases (hall s1).mp hz1 with h | h | h | h <;> subst h <;>
      first | rfl | (exfalso; linarith [hs1.1, hs1.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
        h4.1, h4.2])
  have e2 : s2 = r2 := by
    rcases (hall s2).mp hz2 with h | h | h | h <;> subst h <;>
      first | rfl | (exfalso; linarith [hs2.1, hs2.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
        h4.1, h4.2])
  have e3 : s3 = r3 := by
    rcases (hall s3).mp hz3 with h | h | h | h <;> subst h <;>
      first | rfl | (exfalso; linarith [hs3.1, hs3.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
        h4.1, h4.2])
  have e4 : s4 = r4 := by
    rcases (hall s4).mp hz4 with h | h | h | h <;> subst h <;>
      first | rfl | (exfalso; linarith [hs4.1, hs4.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
        h4.1, h4.2])
  subst e1 e2 e3 e4
  exact ⟨s1, s2, s3, s4, hs1, hs2, hs3, hs4, hall⟩

/-- **Table 3.2, second column (all eight rows).** For each `β` in the table, the real roots
of `P(·, β)` are exactly the listed ones, each in the open cell of width `10⁻⁶` centred at its
printed six-decimal value (`β = 2` has the exact root `1/2`). -/
theorem table_3_2_real_roots :
    -- β = 1: -1.105795, -0.581565
    (∃ r1 r2 : ℝ,
      r1 ∈ Ioo (-11057955 / 10000000 : ℝ) (-11057945 / 10000000) ∧
      r2 ∈ Ioo (-5815655 / 10000000 : ℝ) (-5815645 / 10000000) ∧
      ∀ x : ℝ, numerator x 1 = 0 ↔ x = r1 ∨ x = r2) ∧
    -- β = 1.5: -1.238348, -0.603728, 0.773411, 1.518665
    (∃ r1 r2 r3 r4 : ℝ,
      r1 ∈ Ioo (-12383485 / 10000000 : ℝ) (-12383475 / 10000000) ∧
      r2 ∈ Ioo (-6037285 / 10000000 : ℝ) (-6037275 / 10000000) ∧
      r3 ∈ Ioo (7734105 / 10000000 : ℝ) (7734115 / 10000000) ∧
      r4 ∈ Ioo (15186645 / 10000000 : ℝ) (15186655 / 10000000) ∧
      ∀ x : ℝ, numerator x (3 / 2) = 0 ↔ x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4) ∧
    -- β = 1.9: -1.416934, -0.612873, 0.530181, 3.826548
    (∃ r1 r2 r3 r4 : ℝ,
      r1 ∈ Ioo (-14169345 / 10000000 : ℝ) (-14169335 / 10000000) ∧
      r2 ∈ Ioo (-6128735 / 10000000 : ℝ) (-6128725 / 10000000) ∧
      r3 ∈ Ioo (5301805 / 10000000 : ℝ) (5301815 / 10000000) ∧
      r4 ∈ Ioo (38265475 / 10000000 : ℝ) (38265485 / 10000000) ∧
      ∀ x : ℝ, numerator x (19 / 10) = 0 ↔ x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4) ∧
    -- β = 2: -1.478596, -0.614195, 1/2, 5.092791
    (∃ r1 r2 r4 : ℝ,
      r1 ∈ Ioo (-14785965 / 10000000 : ℝ) (-14785955 / 10000000) ∧
      r2 ∈ Ioo (-6141955 / 10000000 : ℝ) (-6141945 / 10000000) ∧
      r4 ∈ Ioo (50927905 / 10000000 : ℝ) (50927915 / 10000000) ∧
      ∀ x : ℝ, numerator x 2 = 0 ↔ x = r1 ∨ x = r2 ∨ x = 1 / 2 ∨ x = r4) ∧
    -- β = 2.1: -1.550853, -0.615194, 0.474175, 7.370444
    (∃ r1 r2 r3 r4 : ℝ,
      r1 ∈ Ioo (-15508535 / 10000000 : ℝ) (-15508525 / 10000000) ∧
      r2 ∈ Ioo (-6151945 / 10000000 : ℝ) (-6151935 / 10000000) ∧
      r3 ∈ Ioo (4741745 / 10000000 : ℝ) (4741755 / 10000000) ∧
      r4 ∈ Ioo (73704435 / 10000000 : ℝ) (73704445 / 10000000) ∧
      ∀ x : ℝ, numerator x (21 / 10) = 0 ↔ x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4) ∧
    -- β = 7/3: -1.787083, -0.616422, 0.425363
    (∃ r1 r2 r3 : ℝ,
      r1 ∈ Ioo (-17870835 / 10000000 : ℝ) (-17870825 / 10000000) ∧
      r2 ∈ Ioo (-6164225 / 10000000 : ℝ) (-6164215 / 10000000) ∧
      r3 ∈ Ioo (4253625 / 10000000 : ℝ) (4253635 / 10000000) ∧
      ∀ x : ℝ, numerator x (7 / 3) = 0 ↔ x = r1 ∨ x = r2 ∨ x = r3) ∧
    -- β = 2.4: -24.911734, -1.885301, -0.616526, 0.413561
    (∃ r1 r2 r3 r4 : ℝ,
      r1 ∈ Ioo (-249117345 / 10000000 : ℝ) (-249117335 / 10000000) ∧
      r2 ∈ Ioo (-18853015 / 10000000 : ℝ) (-18853005 / 10000000) ∧
      r3 ∈ Ioo (-6165265 / 10000000 : ℝ) (-6165255 / 10000000) ∧
      r4 ∈ Ioo (4135605 / 10000000 : ℝ) (4135615 / 10000000) ∧
      ∀ x : ℝ, numerator x (12 / 5) = 0 ↔ x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4) ∧
    -- β = 3: -0.613838, 0.332575
    (∃ r1 r2 : ℝ,
      r1 ∈ Ioo (-6138385 / 10000000 : ℝ) (-6138375 / 10000000) ∧
      r2 ∈ Ioo (3325745 / 10000000 : ℝ) (3325755 / 10000000) ∧
      ∀ x : ℝ, numerator x 3 = 0 ↔ x = r1 ∨ x = r2) := by
  refine ⟨?_, beta_three_halves_roots_six_decimal, beta_nineteen_tenths_roots_six_decimal,
    RootTableRemaining.beta_two_roots_exhaust,
    RootTableRemaining.beta_twenty_one_tenths_roots_exhaust,
    RootTableRemaining.beta_seven_thirds_roots_exhaust,
    RootTableRemaining.beta_twelve_fifths_roots_exhaust, ?_⟩
  · simpa [TwoRootExhaustion.f1] using TwoRootExhaustion.f1_zero_eq_certified_roots
  · simpa [TwoRootExhaustion.f3] using TwoRootExhaustion.f3_zero_eq_certified_roots

/-- **Table 3.2, third column (all eight rows).** Roots with `λ > 1/2`: none for
`β = 1, 7/3, 2.4, 3`; exactly one for `β = 2` (≈ 5.092791) and `β = 2.1` (≈ 7.370444);
exactly the two listed ones for `β = 1.5` and `β = 1.9`. -/
theorem table_3_2_admissible_roots :
    (∀ x : ℝ, numerator x 1 = 0 → ¬(1 / 2 : ℝ) < x) ∧
    (∃ r3 r4 : ℝ,
      r3 ∈ Ioo (7734105 / 10000000 : ℝ) (7734115 / 10000000) ∧
      r4 ∈ Ioo (15186645 / 10000000 : ℝ) (15186655 / 10000000) ∧
      ∀ x : ℝ, numerator x (3 / 2) = 0 → ((1 / 2 : ℝ) < x ↔ x = r3 ∨ x = r4)) ∧
    (∃ r3 r4 : ℝ,
      r3 ∈ Ioo (5301805 / 10000000 : ℝ) (5301815 / 10000000) ∧
      r4 ∈ Ioo (38265475 / 10000000 : ℝ) (38265485 / 10000000) ∧
      ∀ x : ℝ, numerator x (19 / 10) = 0 → ((1 / 2 : ℝ) < x ↔ x = r3 ∨ x = r4)) ∧
    (∃ r : ℝ, r ∈ Ioo (50927905 / 10000000 : ℝ) (50927915 / 10000000) ∧
      numerator r 2 = 0 ∧ ∀ x : ℝ, numerator x 2 = 0 → ((1 / 2 : ℝ) < x ↔ x = r)) ∧
    (∃ r : ℝ, r ∈ Ioo (73704435 / 10000000 : ℝ) (73704445 / 10000000) ∧
      numerator r (21 / 10) = 0 ∧
      ∀ x : ℝ, numerator x (21 / 10) = 0 → ((1 / 2 : ℝ) < x ↔ x = r)) ∧
    (∀ x : ℝ, numerator x (7 / 3) = 0 → ¬(1 / 2 : ℝ) < x) ∧
    (∀ x : ℝ, numerator x (12 / 5) = 0 → ¬(1 / 2 : ℝ) < x) ∧
    (∀ x : ℝ, numerator x 3 = 0 → ¬(1 / 2 : ℝ) < x) := by
  refine ⟨RootTableAdmissible.beta_one_no_admissible_root, ?_, ?_,
    RootTableAdmissible.beta_two_unique_admissible_root,
    RootTableAdmissible.beta_twenty_one_tenths_unique_admissible_root,
    RootTableAdmissible.beta_seven_thirds_no_admissible_root,
    RootTableAdmissible.beta_twelve_fifths_no_admissible_root,
    RootTableAdmissible.beta_three_no_admissible_root⟩
  · obtain ⟨r1, r2, r3, r4, h1, h2, h3, h4, hall⟩ := beta_three_halves_roots_six_decimal
    refine ⟨r3, r4, h3, h4, fun x hx => ?_⟩
    rcases (hall x).mp hx with rfl | rfl | rfl | rfl
    · constructor
      · intro h; exfalso; linarith [h1.2]
      · rintro (h | h) <;> linarith [h1.2, h3.1, h4.1]
    · constructor
      · intro h; exfalso; linarith [h2.2]
      · rintro (h | h) <;> linarith [h2.2, h3.1, h4.1]
    · exact ⟨fun _ => Or.inl rfl, fun _ => by linarith [h3.1]⟩
    · exact ⟨fun _ => Or.inr rfl, fun _ => by linarith [h4.1]⟩
  · obtain ⟨r1, r2, r3, r4, h1, h2, h3, h4, hall⟩ := beta_nineteen_tenths_roots_six_decimal
    refine ⟨r3, r4, h3, h4, fun x hx => ?_⟩
    rcases (hall x).mp hx with rfl | rfl | rfl | rfl
    · constructor
      · intro h; exfalso; linarith [h1.2]
      · rintro (h | h) <;> linarith [h1.2, h3.1, h4.1]
    · constructor
      · intro h; exfalso; linarith [h2.2]
      · rintro (h | h) <;> linarith [h2.2, h3.1, h4.1]
    · exact ⟨fun _ => Or.inl rfl, fun _ => by linarith [h3.1]⟩
    · exact ⟨fun _ => Or.inr rfl, fun _ => by linarith [h4.1]⟩

end

end ChemotaxisBifurcation.RootTableAggregate

end
