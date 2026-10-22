module

public import ChemotaxisBifurcation.RootTable
public import ChemotaxisBifurcation.QuarticRoot

/-! # Remaining six-decimal rows of Table 2.2

Each row is a unique root in an open rounding cell of width `10^-6`.  The
closed-interval certificate is the Mathlib-only lemma
`QuarticRoot.existsUnique_root` (sign change plus a rational derivative bound,
decided by `norm_num`); the endpoints are then excluded by `norm_num`. -/

@[expose] public section

namespace ChemotaxisBifurcation.RootTableRemaining
open ChemotaxisBifurcation.SpecializedPolynomial
open Polynomial
open ChemotaxisBifurcation.CertifiedRoots
open ChemotaxisBifurcation.QuarticRoot

noncomputable section

private theorem unique_Ioo_of_unique_Icc {f : ℝ → ℝ} {lo hi : ℝ}
    (h : ∃! x : ℝ, x ∈ Set.Icc lo hi ∧ f x = 0)
    (hlo : f lo ≠ 0) (hhi : f hi ≠ 0) :
    ∃! x : ℝ, x ∈ Set.Ioo lo hi ∧ f x = 0 := by
  rcases h with ⟨x, ⟨hx, hzero⟩, huniq⟩
  have hxlo_ne : x ≠ lo := by intro heq; apply hlo; simpa [heq] using hzero
  have hxhi_ne : x ≠ hi := by intro heq; apply hhi; simpa [heq] using hzero
  refine ⟨x, ⟨⟨lt_of_le_of_ne hx.1 hxlo_ne.symm, lt_of_le_of_ne hx.2 hxhi_ne⟩, hzero⟩, ?_⟩
  intro y hy
  apply huniq y
  exact ⟨⟨hy.1.1.le, hy.1.2.le⟩, hy.2⟩

theorem b1r1_root : ∃! x : ℝ, x ∈ Set.Ioo (-11057955 / 10000000 : ℝ) (-11057945 / 10000000 : ℝ) ∧ numerator x (((1) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((1) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b1r2_root : ∃! x : ℝ, x ∈ Set.Ioo (-5815655 / 10000000 : ℝ) (-5815645 / 10000000 : ℝ) ∧ numerator x (((1) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((1) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b2r1_root : ∃! x : ℝ, x ∈ Set.Ioo (-14785965 / 10000000 : ℝ) (-14785955 / 10000000 : ℝ) ∧ numerator x (((2) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((2) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b2r2_root : ∃! x : ℝ, x ∈ Set.Ioo (-6141955 / 10000000 : ℝ) (-6141945 / 10000000 : ℝ) ∧ numerator x (((2) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((2) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b2r3_root : ∃! x : ℝ, x ∈ Set.Ioo (50927905 / 10000000 : ℝ) (50927915 / 10000000 : ℝ) ∧ numerator x (((2) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((2) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b21r1_root : ∃! x : ℝ, x ∈ Set.Ioo (-15508535 / 10000000 : ℝ) (-15508525 / 10000000 : ℝ) ∧ numerator x (((21/10) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((21/10) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b21r2_root : ∃! x : ℝ, x ∈ Set.Ioo (-6151945 / 10000000 : ℝ) (-6151935 / 10000000 : ℝ) ∧ numerator x (((21/10) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((21/10) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b21r3_root : ∃! x : ℝ, x ∈ Set.Ioo (4741745 / 10000000 : ℝ) (4741755 / 10000000 : ℝ) ∧ numerator x (((21/10) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((21/10) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b21r4_root : ∃! x : ℝ, x ∈ Set.Ioo (73704435 / 10000000 : ℝ) (73704445 / 10000000 : ℝ) ∧ numerator x (((21/10) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((21/10) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b73r1_root : ∃! x : ℝ, x ∈ Set.Ioo (-17870835 / 10000000 : ℝ) (-17870825 / 10000000 : ℝ) ∧ numerator x (((7/3) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((7/3) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b73r2_root : ∃! x : ℝ, x ∈ Set.Ioo (-6164225 / 10000000 : ℝ) (-6164215 / 10000000 : ℝ) ∧ numerator x (((7/3) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((7/3) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b73r3_root : ∃! x : ℝ, x ∈ Set.Ioo (4253625 / 10000000 : ℝ) (4253635 / 10000000 : ℝ) ∧ numerator x (((7/3) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((7/3) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b24r1_root : ∃! x : ℝ, x ∈ Set.Ioo (-249117345 / 10000000 : ℝ) (-249117335 / 10000000 : ℝ) ∧ numerator x (((12/5) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((12/5) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b24r2_root : ∃! x : ℝ, x ∈ Set.Ioo (-18853015 / 10000000 : ℝ) (-18853005 / 10000000 : ℝ) ∧ numerator x (((12/5) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((12/5) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b24r3_root : ∃! x : ℝ, x ∈ Set.Ioo (-6165265 / 10000000 : ℝ) (-6165255 / 10000000 : ℝ) ∧ numerator x (((12/5) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((12/5) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b24r4_root : ∃! x : ℝ, x ∈ Set.Ioo (4135605 / 10000000 : ℝ) (4135615 / 10000000 : ℝ) ∧ numerator x (((12/5) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((12/5) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b3r1_root : ∃! x : ℝ, x ∈ Set.Ioo (-6138385 / 10000000 : ℝ) (-6138375 / 10000000 : ℝ) ∧ numerator x (((3) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((3) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem b3r2_root : ∃! x : ℝ, x ∈ Set.Ioo (3325745 / 10000000 : ℝ) (3325755 / 10000000 : ℝ) ∧ numerator x (((3) : ℚ) : ℝ) = 0 := by
  apply unique_Ioo_of_unique_Icc (f := fun x ↦ numerator x (((3) : ℚ) : ℝ))
  · simp only [numerator_eq_quartic]
    apply existsUnique_root <;> norm_num [q, q', abs_of_pos, abs_of_neg]
  · norm_num [numerator]
  · norm_num [numerator]

theorem beta_two_exact_half_root : numerator (1 / 2 : ℝ) 2 = 0 := by
  norm_num [numerator]

/-- Polynomial form used to turn the certified distinct roots into an exact
exhaustive real-root list. -/
def tablePoly (beta : ℝ) : ℝ[X] :=
  C (224 - 96 * beta) * X ^ 4 +
    C (192 - 152 * beta) * X ^ 3 +
    C (8 - 104 * beta - 16 * beta ^ 2) * X ^ 2 +
    C (96 - 28 * beta - 8 * beta ^ 2) * X +
    C (56 + 11 * beta - beta ^ 2)

theorem tablePoly_eval (x beta : ℝ) :
    (tablePoly beta).eval x = numerator x beta := by
  simp [tablePoly, numerator]
  ring

private theorem roots_exhausted_of_three
    (p : ℝ[X]) (hp : p ≠ 0) (hdeg : p.natDegree ≤ 3)
    {r1 r2 r3 : ℝ} (h12 : r1 < r2) (h23 : r2 < r3)
    (hr1 : p.IsRoot r1) (hr2 : p.IsRoot r2) (hr3 : p.IsRoot r3) :
    ∀ x : ℝ, p.IsRoot x ↔ x = r1 ∨ x = r2 ∨ x = r3 := by
  classical
  let s : Finset ℝ := {r1, r2, r3}
  have h13 : r1 < r3 := h12.trans h23
  have hs_card : s.card = 3 := by
    dsimp [s]
    simp [h12.ne, h13.ne, h23.ne]
  have hs_sub : s ⊆ p.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots hp]
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hr1
    · exact hr2
    · exact hr3
  have hcard : p.roots.toFinset.card ≤ s.card := by
    calc
      p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le p.roots
      _ ≤ p.natDegree := card_roots' p
      _ ≤ 3 := hdeg
      _ = s.card := hs_card.symm
  have hs_eq : s = p.roots.toFinset := Finset.eq_of_subset_of_card_le hs_sub hcard
  intro x
  rw [← mem_roots hp, ← Multiset.mem_toFinset, ← hs_eq]
  simp [s, eq_comm]

private theorem tablePoly_ne_zero_of_degree {beta : ℝ} {n : ℕ}
    (hdeg : (tablePoly beta).natDegree = n) (hn : n ≠ 0) :
    tablePoly beta ≠ 0 := by
  intro h
  rw [h] at hdeg
  simp at hdeg
  exact hn hdeg.symm

theorem tablePoly_degree_beta_two : (tablePoly 2).natDegree = 4 := by
  unfold tablePoly
  compute_degree <;> norm_num

theorem tablePoly_degree_beta_twenty_one_tenths :
    (tablePoly (21 / 10)).natDegree = 4 := by
  unfold tablePoly
  compute_degree <;> norm_num

theorem tablePoly_degree_beta_twelve_fifths :
    (tablePoly (12 / 5)).natDegree = 4 := by
  unfold tablePoly
  compute_degree <;> norm_num

theorem tablePoly_degree_beta_seven_thirds :
    (tablePoly (7 / 3)).natDegree = 3 := by
  rw [show tablePoly (7 / 3) =
      C (-488 / 3) * X ^ 3 + C (-2896 / 9) * X ^ 2 +
        C (-116 / 9) * X + C (686 / 9) by
    unfold tablePoly
    norm_num]
  compute_degree <;> norm_num

/-- The four displayed roots for `beta=2` exhaust all real roots. -/
theorem beta_two_roots_exhaust :
    ∃ r1 r2 r4 : ℝ,
      r1 ∈ Set.Ioo (-14785965 / 10000000 : ℝ) (-14785955 / 10000000 : ℝ) ∧
      r2 ∈ Set.Ioo (-6141955 / 10000000 : ℝ) (-6141945 / 10000000 : ℝ) ∧
      r4 ∈ Set.Ioo (50927905 / 10000000 : ℝ) (50927915 / 10000000 : ℝ) ∧
      ∀ x : ℝ, numerator x 2 = 0 ↔
        x = r1 ∨ x = r2 ∨ x = 1 / 2 ∨ x = r4 := by
  rcases b2r1_root with ⟨r1, hr1, -⟩
  rcases b2r2_root with ⟨r2, hr2, -⟩
  rcases b2r3_root with ⟨r4, hr4, -⟩
  have h12 : r1 < r2 := by linarith [hr1.1.2, hr2.1.1]
  have h23 : r2 < (1 / 2 : ℝ) := by linarith [hr2.1.2]
  have h34 : (1 / 2 : ℝ) < r4 := by linarith [hr4.1.1]
  have hp : tablePoly 2 ≠ 0 :=
    tablePoly_ne_zero_of_degree tablePoly_degree_beta_two (by norm_num)
  have hexhaust := RootExhaustion.roots_exhausted_of_four (tablePoly 2) hp
    (by rw [tablePoly_degree_beta_two]) h12 h23 h34
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr1.2)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr2.2)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using beta_two_exact_half_root)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr4.2)
  refine ⟨r1, r2, r4, hr1.1, hr2.1, hr4.1, ?_⟩
  intro x
  simpa [Polynomial.IsRoot, tablePoly_eval] using hexhaust x

/-- The four displayed roots for `beta=2.1` exhaust all real roots. -/
theorem beta_twenty_one_tenths_roots_exhaust :
    ∃ r1 r2 r3 r4 : ℝ,
      r1 ∈ Set.Ioo (-15508535 / 10000000 : ℝ) (-15508525 / 10000000 : ℝ) ∧
      r2 ∈ Set.Ioo (-6151945 / 10000000 : ℝ) (-6151935 / 10000000 : ℝ) ∧
      r3 ∈ Set.Ioo (4741745 / 10000000 : ℝ) (4741755 / 10000000 : ℝ) ∧
      r4 ∈ Set.Ioo (73704435 / 10000000 : ℝ) (73704445 / 10000000 : ℝ) ∧
      ∀ x : ℝ, numerator x (21 / 10) = 0 ↔
        x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4 := by
  rcases b21r1_root with ⟨r1, hr1, -⟩
  rcases b21r2_root with ⟨r2, hr2, -⟩
  rcases b21r3_root with ⟨r3, hr3, -⟩
  rcases b21r4_root with ⟨r4, hr4, -⟩
  have h12 : r1 < r2 := by linarith [hr1.1.2, hr2.1.1]
  have h23 : r2 < r3 := by linarith [hr2.1.2, hr3.1.1]
  have h34 : r3 < r4 := by linarith [hr3.1.2, hr4.1.1]
  have hp : tablePoly (21 / 10) ≠ 0 :=
    tablePoly_ne_zero_of_degree tablePoly_degree_beta_twenty_one_tenths (by norm_num)
  have hexhaust := RootExhaustion.roots_exhausted_of_four (tablePoly (21 / 10)) hp
    (by rw [tablePoly_degree_beta_twenty_one_tenths]) h12 h23 h34
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr1.2)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr2.2)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr3.2)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr4.2)
  refine ⟨r1, r2, r3, r4, hr1.1, hr2.1, hr3.1, hr4.1, ?_⟩
  intro x
  simpa [Polynomial.IsRoot, tablePoly_eval] using hexhaust x

/-- The four displayed roots for `beta=2.4` exhaust all real roots. -/
theorem beta_twelve_fifths_roots_exhaust :
    ∃ r1 r2 r3 r4 : ℝ,
      r1 ∈ Set.Ioo (-249117345 / 10000000 : ℝ) (-249117335 / 10000000 : ℝ) ∧
      r2 ∈ Set.Ioo (-18853015 / 10000000 : ℝ) (-18853005 / 10000000 : ℝ) ∧
      r3 ∈ Set.Ioo (-6165265 / 10000000 : ℝ) (-6165255 / 10000000 : ℝ) ∧
      r4 ∈ Set.Ioo (4135605 / 10000000 : ℝ) (4135615 / 10000000 : ℝ) ∧
      ∀ x : ℝ, numerator x (12 / 5) = 0 ↔
        x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4 := by
  rcases b24r1_root with ⟨r1, hr1, -⟩
  rcases b24r2_root with ⟨r2, hr2, -⟩
  rcases b24r3_root with ⟨r3, hr3, -⟩
  rcases b24r4_root with ⟨r4, hr4, -⟩
  have h12 : r1 < r2 := by linarith [hr1.1.2, hr2.1.1]
  have h23 : r2 < r3 := by linarith [hr2.1.2, hr3.1.1]
  have h34 : r3 < r4 := by linarith [hr3.1.2, hr4.1.1]
  have hp : tablePoly (12 / 5) ≠ 0 :=
    tablePoly_ne_zero_of_degree tablePoly_degree_beta_twelve_fifths (by norm_num)
  have hexhaust := RootExhaustion.roots_exhausted_of_four (tablePoly (12 / 5)) hp
    (by rw [tablePoly_degree_beta_twelve_fifths]) h12 h23 h34
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr1.2)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr2.2)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr3.2)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr4.2)
  refine ⟨r1, r2, r3, r4, hr1.1, hr2.1, hr3.1, hr4.1, ?_⟩
  intro x
  simpa [Polynomial.IsRoot, tablePoly_eval] using hexhaust x

/-- At `beta=7/3` the quartic coefficient vanishes; the three displayed roots
exhaust the resulting cubic's real roots. -/
theorem beta_seven_thirds_roots_exhaust :
    ∃ r1 r2 r3 : ℝ,
      r1 ∈ Set.Ioo (-17870835 / 10000000 : ℝ) (-17870825 / 10000000 : ℝ) ∧
      r2 ∈ Set.Ioo (-6164225 / 10000000 : ℝ) (-6164215 / 10000000 : ℝ) ∧
      r3 ∈ Set.Ioo (4253625 / 10000000 : ℝ) (4253635 / 10000000 : ℝ) ∧
      ∀ x : ℝ, numerator x (7 / 3) = 0 ↔
        x = r1 ∨ x = r2 ∨ x = r3 := by
  rcases b73r1_root with ⟨r1, hr1, -⟩
  rcases b73r2_root with ⟨r2, hr2, -⟩
  rcases b73r3_root with ⟨r3, hr3, -⟩
  have h12 : r1 < r2 := by linarith [hr1.1.2, hr2.1.1]
  have h23 : r2 < r3 := by linarith [hr2.1.2, hr3.1.1]
  have hp : tablePoly (7 / 3) ≠ 0 :=
    tablePoly_ne_zero_of_degree tablePoly_degree_beta_seven_thirds (by norm_num)
  have hexhaust := roots_exhausted_of_three (tablePoly (7 / 3)) hp
    (by rw [tablePoly_degree_beta_seven_thirds]) h12 h23
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr1.2)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr2.2)
    (by simpa [Polynomial.IsRoot, tablePoly_eval] using hr3.2)
  refine ⟨r1, r2, r3, hr1.1, hr2.1, hr3.1, ?_⟩
  intro x
  simpa [Polynomial.IsRoot, tablePoly_eval] using hexhaust x

end

end ChemotaxisBifurcation.RootTableRemaining

end
