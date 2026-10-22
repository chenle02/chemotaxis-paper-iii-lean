module
public import ChemotaxisBifurcation.BetaQuadratic

@[expose] public section

/-!
# Four nonnegative-axis regimes of a concave quadratic

These theorems formalize the sign classifications in current Theorem 1.1(2).
Roots remain explicit in the root-bearing cases, matching the manuscript's
notation.  Separate root-construction lemmas can instantiate these interfaces.
-/

namespace ChemotaxisBifurcation

def betaQuadratic (A B C beta : ℝ) : ℝ :=
  A * beta ^ 2 + B * beta + C

def betaDiscriminant (A B C : ℝ) : ℝ := B ^ 2 - 4 * A * C

noncomputable def betaMinus (A B C : ℝ) : ℝ :=
  (-B + Real.sqrt (betaDiscriminant A B C)) / (2 * A)

noncomputable def betaPlus (A B C : ℝ) : ℝ :=
  (-B - Real.sqrt (betaDiscriminant A B C)) / (2 * A)

theorem betaMinus_is_root
    (A B C : ℝ) (hA : A ≠ 0) (hD : 0 ≤ betaDiscriminant A B C) :
    betaQuadratic A B C (betaMinus A B C) = 0 := by
  have hs := Real.sq_sqrt hD
  simp only [betaQuadratic, betaMinus, betaDiscriminant]
  field_simp [hA]
  ring_nf
  unfold betaDiscriminant at hs
  have hs' :
      Real.sqrt (B ^ 2 - A * C * 4) ^ 2 = B ^ 2 - A * C * 4 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hs
  nlinarith [hs']

theorem betaPlus_is_root
    (A B C : ℝ) (hA : A ≠ 0) (hD : 0 ≤ betaDiscriminant A B C) :
    betaQuadratic A B C (betaPlus A B C) = 0 := by
  have hs := Real.sq_sqrt hD
  simp only [betaQuadratic, betaPlus, betaDiscriminant]
  field_simp [hA]
  ring_nf
  unfold betaDiscriminant at hs
  have hs' :
      Real.sqrt (B ^ 2 - A * C * 4) ^ 2 = B ^ 2 - A * C * 4 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hs
  nlinarith [hs']

theorem betaMinus_lt_betaPlus
    (A B C : ℝ) (hA : A < 0) (hD : 0 < betaDiscriminant A B C) :
    betaMinus A B C < betaPlus A B C := by
  unfold betaMinus betaPlus
  have hden : 2 * A < 0 := by linarith
  have hs : 0 < Real.sqrt (betaDiscriminant A B C) := Real.sqrt_pos.2 hD
  have hleft := div_mul_cancel₀
    (-B + Real.sqrt (betaDiscriminant A B C)) (ne_of_lt hden)
  have hright := div_mul_cancel₀
    (-B - Real.sqrt (betaDiscriminant A B C)) (ne_of_lt hden)
  by_contra h
  have hge :
      (-B + Real.sqrt (betaDiscriminant A B C)) / (2 * A) ≥
        (-B - Real.sqrt (betaDiscriminant A B C)) / (2 * A) :=
    le_of_not_gt h
  have hmul := mul_le_mul_of_nonpos_right hge (le_of_lt hden)
  rw [hleft, hright] at hmul
  linarith

theorem betaRoots_nonnegative_of_C_nonpos_B_pos
    (A B C : ℝ) (hA : A < 0) (hB : 0 < B) (hC : C ≤ 0)
    (hD : 0 < betaDiscriminant A B C) :
    0 ≤ betaMinus A B C ∧ 0 < betaPlus A B C := by
  have hAC : 0 ≤ A * C :=
    mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA) hC
  have hD0 : 0 ≤ betaDiscriminant A B C := le_of_lt hD
  have hs0 := Real.sqrt_nonneg (betaDiscriminant A B C)
  have hs2 := Real.sq_sqrt hD0
  have hsB : Real.sqrt (betaDiscriminant A B C) ≤ B := by
    unfold betaDiscriminant at hs2 ⊢
    nlinarith
  have hden : 2 * A < 0 := by linarith
  constructor
  · unfold betaMinus
    by_contra h
    have hr : (-B + Real.sqrt (betaDiscriminant A B C)) / (2 * A) < 0 :=
      lt_of_not_ge h
    have hp := mul_pos_of_neg_of_neg hr hden
    rw [div_mul_cancel₀ _ (ne_of_lt hden)] at hp
    linarith
  · unfold betaPlus
    exact div_pos_of_neg_of_neg (by linarith) hden

theorem betaRoots_sign_of_C_pos
    (A B C : ℝ) (hA : A < 0) (hC : 0 < C) :
    betaMinus A B C < 0 ∧ 0 < betaPlus A B C := by
  have hAC : A * C < 0 := mul_neg_of_neg_of_pos hA hC
  have hD : 0 < betaDiscriminant A B C := by
    unfold betaDiscriminant
    nlinarith [sq_nonneg B]
  have hs0 := Real.sqrt_nonneg (betaDiscriminant A B C)
  have hs2 := Real.sq_sqrt (le_of_lt hD)
  have hBsq : B ^ 2 < betaDiscriminant A B C := by
    unfold betaDiscriminant
    nlinarith
  have habs : |B| < Real.sqrt (betaDiscriminant A B C) := by
    have hsqrt := Real.sqrt_lt_sqrt (sq_nonneg B) hBsq
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  have hsB : B < Real.sqrt (betaDiscriminant A B C) :=
    lt_of_le_of_lt (le_abs_self B) habs
  have hsnegB : -B < Real.sqrt (betaDiscriminant A B C) :=
    lt_of_le_of_lt (neg_le_abs B) habs
  have hden : 2 * A < 0 := by linarith
  constructor
  · unfold betaMinus
    exact div_neg_of_pos_of_neg (by linarith) hden
  · unfold betaPlus
    exact div_pos_of_neg_of_neg (by linarith) hden

noncomputable def betaDouble (A B : ℝ) : ℝ := -B / (2 * A)

theorem betaDouble_data
    (A B C : ℝ) (hA : A < 0) (hB : 0 < B)
    (hD : betaDiscriminant A B C = 0) :
    0 < betaDouble A B ∧
      betaQuadratic A B C (betaDouble A B) = 0 ∧
      2 * A * betaDouble A B + B = 0 := by
  have hA0 : A ≠ 0 := ne_of_lt hA
  unfold betaDouble
  constructor
  · exact div_pos_of_neg_of_neg (neg_lt_zero.mpr hB) (by linarith)
  constructor
  · unfold betaDiscriminant at hD
    unfold betaQuadratic
    field_simp [hA0]
    nlinarith
  · field_simp [hA0]
    ring

theorem betaQuadratic_factor_of_root
    (A B C beta0 beta : ℝ)
    (hroot : betaQuadratic A B C beta0 = 0) :
    betaQuadratic A B C beta =
      (beta - beta0) * (A * (beta + beta0) + B) := by
  unfold betaQuadratic at hroot ⊢
  have hC : C = -(A * beta0 ^ 2 + B * beta0) := by linarith
  rw [hC]
  ring

theorem cofactor_neg_of_pos_constant
    (A B C betaPlus beta : ℝ)
    (hA : A < 0) (hC : 0 < C) (hPlus : 0 < betaPlus)
    (hroot : betaQuadratic A B C betaPlus = 0) (hbeta : 0 ≤ beta) :
    A * (beta + betaPlus) + B < 0 := by
  unfold betaQuadratic at hroot
  have hprod : betaPlus * (A * betaPlus + B) = -C := by
    linear_combination hroot
  have hg0 : A * betaPlus + B < 0 := by nlinarith
  nlinarith

/-- Case (i): positive constant term and one supplied positive root. -/
theorem regime_one_positive_root
    (A B C betaPlus : ℝ)
    (hA : A < 0) (hC : 0 < C) (hPlus : 0 < betaPlus)
    (hroot : betaQuadratic A B C betaPlus = 0) :
    (∀ beta, 0 ≤ beta → beta < betaPlus →
      0 < betaQuadratic A B C beta) ∧
    (∀ beta, betaPlus < beta → betaQuadratic A B C beta < 0) ∧
    (∀ beta, 0 ≤ beta → betaQuadratic A B C beta = 0 →
      beta = betaPlus) := by
  refine ⟨?_, ?_, ?_⟩
  · intro beta hbeta hlt
    rw [betaQuadratic_factor_of_root A B C betaPlus beta hroot]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hlt)
      (cofactor_neg_of_pos_constant A B C betaPlus beta
        hA hC hPlus hroot hbeta)
  · intro beta hgt
    have hbeta : 0 ≤ beta := by linarith
    rw [betaQuadratic_factor_of_root A B C betaPlus beta hroot]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hgt)
      (cofactor_neg_of_pos_constant A B C betaPlus beta
        hA hC hPlus hroot hbeta)
  · intro beta hbeta hzero
    rw [betaQuadratic_factor_of_root A B C betaPlus beta hroot] at hzero
    have hco := cofactor_neg_of_pos_constant A B C betaPlus beta
      hA hC hPlus hroot hbeta
    rcases mul_eq_zero.mp hzero with h | h
    · linarith
    · exact absurd h (ne_of_lt hco)

/-- A concave quadratic with two distinct roots factors through them. -/
theorem betaQuadratic_factor_two_roots
    (A B C betaMinus betaPlus beta : ℝ)
    (hA : A ≠ 0) (hlt : betaMinus < betaPlus)
    (hminus : betaQuadratic A B C betaMinus = 0)
    (hplus : betaQuadratic A B C betaPlus = 0) :
    betaQuadratic A B C beta =
      A * (beta - betaMinus) * (beta - betaPlus) := by
  have hdiff : betaMinus - betaPlus ≠ 0 := sub_ne_zero.mpr (ne_of_lt hlt)
  unfold betaQuadratic at hminus hplus ⊢
  have hsum : A * (betaMinus + betaPlus) + B = 0 := by
    have hsub :
        (betaMinus - betaPlus) *
          (A * (betaMinus + betaPlus) + B) = 0 := by
      nlinarith [hminus, hplus]
    exact (mul_eq_zero.mp hsub).resolve_left hdiff
  have hprod : C = A * betaMinus * betaPlus := by
    nlinarith [hminus, hsum]
  have hB : B = -A * (betaMinus + betaPlus) := by linarith
  rw [hprod, hB]
  ring

/-- Case (ii): two nonnegative roots and positivity precisely between them. -/
theorem regime_two_nonnegative_roots
    (A B C betaMinus betaPlus : ℝ)
    (hA : A < 0) (hminus0 : 0 ≤ betaMinus)
    (hlt : betaMinus < betaPlus)
    (hminus : betaQuadratic A B C betaMinus = 0)
    (hplus : betaQuadratic A B C betaPlus = 0) :
    (∀ beta, 0 ≤ beta → beta < betaMinus →
      betaQuadratic A B C beta < 0) ∧
    (∀ beta, betaMinus < beta → beta < betaPlus →
      0 < betaQuadratic A B C beta) ∧
    (∀ beta, betaPlus < beta → betaQuadratic A B C beta < 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro beta _hbeta hbm
    have hfac := betaQuadratic_factor_two_roots
      (A := A) (B := B) (C := C) (betaMinus := betaMinus)
      (betaPlus := betaPlus) (beta := beta)
      (ne_of_lt hA) hlt hminus hplus
    rw [hfac]
    have h1 : beta - betaMinus < 0 := sub_neg.mpr hbm
    have h2 : beta - betaPlus < 0 := by linarith
    have hA1 : 0 < A * (beta - betaMinus) :=
      mul_pos_of_neg_of_neg hA h1
    exact mul_neg_of_pos_of_neg hA1 h2
  · intro beta hbm hbp
    have hfac := betaQuadratic_factor_two_roots
      (A := A) (B := B) (C := C) (betaMinus := betaMinus)
      (betaPlus := betaPlus) (beta := beta)
      (ne_of_lt hA) hlt hminus hplus
    rw [hfac]
    have hA1 : A * (beta - betaMinus) < 0 :=
      mul_neg_of_neg_of_pos hA (sub_pos.mpr hbm)
    exact mul_pos_of_neg_of_neg hA1 (sub_neg.mpr hbp)
  · intro beta hbp
    have hfac := betaQuadratic_factor_two_roots
      (A := A) (B := B) (C := C) (betaMinus := betaMinus)
      (betaPlus := betaPlus) (beta := beta)
      (ne_of_lt hA) hlt hminus hplus
    rw [hfac]
    have hA1 : A * (beta - betaMinus) < 0 :=
      mul_neg_of_neg_of_pos hA (by linarith)
    exact mul_neg_of_neg_of_pos hA1 (sub_pos.mpr hbp)

/-- A root with vanishing derivative gives the double-root factorization. -/
theorem betaQuadratic_double_root_factor
    (A B C beta0 beta : ℝ)
    (hroot : betaQuadratic A B C beta0 = 0)
    (htangent : 2 * A * beta0 + B = 0) :
    betaQuadratic A B C beta = A * (beta - beta0) ^ 2 := by
  unfold betaQuadratic at hroot ⊢
  have hB : B = -2 * A * beta0 := by linarith
  have hC : C = A * beta0 ^ 2 := by
    rw [hB] at hroot
    nlinarith
  rw [hB, hC]
  ring

/-- Case (iii-a): a concave double root is the sole nonnegative zero. -/
theorem regime_double_nonnegative_root
    (A B C beta0 : ℝ)
    (hA : A < 0) (hbeta0 : 0 ≤ beta0)
    (hroot : betaQuadratic A B C beta0 = 0)
    (htangent : 2 * A * beta0 + B = 0) :
    (∀ beta, 0 ≤ beta → beta ≠ beta0 →
      betaQuadratic A B C beta < 0) ∧
    betaQuadratic A B C beta0 = 0 := by
  refine ⟨?_, hroot⟩
  intro beta _hbeta hne
  rw [betaQuadratic_double_root_factor A B C beta0 beta hroot htangent]
  have hs : 0 < (beta - beta0) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  exact mul_neg_of_neg_of_pos hA hs

/-- Case (iii-b): when `C=0` and `B≤0`, zero is the sole nonnegative root. -/
theorem regime_zero_root
    (A B C : ℝ) (hA : A < 0) (hB : B ≤ 0) (hC : C = 0) :
    (∀ beta, 0 < beta → betaQuadratic A B C beta < 0) ∧
    betaQuadratic A B C 0 = 0 ∧
    (∀ beta, 0 ≤ beta → betaQuadratic A B C beta = 0 → beta = 0) := by
  subst C
  refine ⟨?_, by simp [betaQuadratic], ?_⟩
  · intro beta hbeta
    unfold betaQuadratic
    have hlin : A * beta + B < 0 := by nlinarith
    nlinarith
  · intro beta hbeta hzero
    by_contra hne
    have hpos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hne)
    have hneg := (show betaQuadratic A B 0 beta < 0 from by
      unfold betaQuadratic
      have hlin : A * beta + B < 0 := by nlinarith
      nlinarith)
    linarith

/-- Case (iv-a): nonpositive linear coefficient makes a negative constant
quadratic negative on the whole nonnegative axis. -/
theorem regime_everywhere_neg_of_B_nonpos
    (A B C : ℝ) (hA : A < 0) (hB : B ≤ 0) (hC : C < 0) :
    ∀ beta, 0 ≤ beta → betaQuadratic A B C beta < 0 := by
  intro beta hbeta
  unfold betaQuadratic
  have hs := sq_nonneg beta
  nlinarith

/-- Case (iv-b): a negative discriminant makes a concave quadratic negative
everywhere. -/
theorem regime_everywhere_neg_of_discriminant_neg
    (A B C : ℝ) (hA : A < 0)
    (hD : B ^ 2 - 4 * A * C < 0) :
    ∀ beta, betaQuadratic A B C beta < 0 := by
  intro beta
  unfold betaQuadratic
  have hs : 0 ≤ (2 * A * beta + B) ^ 2 := sq_nonneg _
  nlinarith

/-- Manuscript case (i) with the positive root constructed from the
discriminant. -/
theorem regime_case_i
    (A B C : ℝ) (hA : A < 0) (hC : 0 < C) :
    (∀ beta, 0 ≤ beta → beta < betaPlus A B C →
      0 < betaQuadratic A B C beta) ∧
    (∀ beta, betaPlus A B C < beta → betaQuadratic A B C beta < 0) ∧
    (∀ beta, 0 ≤ beta → betaQuadratic A B C beta = 0 →
      beta = betaPlus A B C) := by
  have hsign := betaRoots_sign_of_C_pos A B C hA hC
  have hD : 0 ≤ betaDiscriminant A B C := by
    unfold betaDiscriminant
    have hAC := mul_neg_of_neg_of_pos hA hC
    nlinarith [sq_nonneg B]
  exact regime_one_positive_root A B C (betaPlus A B C)
    hA hC hsign.2 (betaPlus_is_root A B C (ne_of_lt hA) hD)

/-- Manuscript case (ii) with both nonnegative roots constructed from the
discriminant. -/
theorem regime_case_ii
    (A B C : ℝ) (hA : A < 0) (hB : 0 < B) (hC : C ≤ 0)
    (hD : 0 < betaDiscriminant A B C) :
    (∀ beta, 0 ≤ beta → beta < betaMinus A B C →
      betaQuadratic A B C beta < 0) ∧
    (∀ beta, betaMinus A B C < beta → beta < betaPlus A B C →
      0 < betaQuadratic A B C beta) ∧
    (∀ beta, betaPlus A B C < beta → betaQuadratic A B C beta < 0) := by
  have hroots := betaRoots_nonnegative_of_C_nonpos_B_pos
    A B C hA hB hC hD
  have horder := betaMinus_lt_betaPlus A B C hA hD
  have hD0 := le_of_lt hD
  exact regime_two_nonnegative_roots A B C
    (betaMinus A B C) (betaPlus A B C) hA hroots.1 horder
    (betaMinus_is_root A B C (ne_of_lt hA) hD0)
    (betaPlus_is_root A B C (ne_of_lt hA) hD0)

/-- Manuscript double-root part of case (iii), with the nonnegative root
constructed from `A`, `B`, and the zero discriminant. -/
theorem regime_case_iii_double
    (A B C : ℝ) (hA : A < 0) (hB : 0 < B)
    (hD : betaDiscriminant A B C = 0) :
    (∀ beta, 0 ≤ beta → beta ≠ betaDouble A B →
      betaQuadratic A B C beta < 0) ∧
    betaQuadratic A B C (betaDouble A B) = 0 := by
  have hd := betaDouble_data A B C hA hB hD
  exact regime_double_nonnegative_root A B C (betaDouble A B)
    hA (le_of_lt hd.1) hd.2.1 hd.2.2

def regimeConditionI (_A _B C : ℝ) : Prop := 0 < C

def regimeConditionII (A B C : ℝ) : Prop :=
  C ≤ 0 ∧ 0 < B ∧ 0 < betaDiscriminant A B C

def regimeConditionIII (A B C : ℝ) : Prop :=
  (C < 0 ∧ 0 < B ∧ betaDiscriminant A B C = 0) ∨
    (C = 0 ∧ B ≤ 0)

def regimeConditionIV (A B C : ℝ) : Prop :=
  C < 0 ∧ (B ≤ 0 ∨ betaDiscriminant A B C < 0)

/-- The four manuscript conditions exhaust all real `B,C` possibilities. -/
theorem betaRegime_conditions_exhaustive (A B C : ℝ) :
    regimeConditionI A B C ∨ regimeConditionII A B C ∨
      regimeConditionIII A B C ∨ regimeConditionIV A B C := by
  by_cases hCp : 0 < C
  · exact Or.inl hCp
  right
  have hCle : C ≤ 0 := le_of_not_gt hCp
  by_cases hC0 : C = 0
  · by_cases hBp : 0 < B
    · left
      refine ⟨hCle, hBp, ?_⟩
      unfold betaDiscriminant
      rw [hC0]
      have hs : 0 < B ^ 2 := sq_pos_of_pos hBp
      nlinarith
    · right
      left
      exact Or.inr ⟨hC0, le_of_not_gt hBp⟩
  · have hCn : C < 0 := lt_of_le_of_ne hCle (fun h0C => hC0 h0C)
    by_cases hBp : 0 < B
    · rcases lt_trichotomy (betaDiscriminant A B C) 0 with hD | hD | hD
      · exact Or.inr (Or.inr ⟨hCn, Or.inr hD⟩)
      · exact Or.inr (Or.inl (Or.inl ⟨hCn, hBp, hD⟩))
      · exact Or.inl ⟨hCle, hBp, hD⟩
    · exact Or.inr (Or.inr ⟨hCn, Or.inl (le_of_not_gt hBp)⟩)

/-- No two of the four manuscript conditions can hold simultaneously. -/
theorem betaRegime_conditions_pairwise_disjoint (A B C : ℝ) :
    (regimeConditionI A B C →
      ¬regimeConditionII A B C ∧ ¬regimeConditionIII A B C ∧
        ¬regimeConditionIV A B C) ∧
    (regimeConditionII A B C →
      ¬regimeConditionIII A B C ∧ ¬regimeConditionIV A B C) ∧
    (regimeConditionIII A B C → ¬regimeConditionIV A B C) := by
  unfold regimeConditionI regimeConditionII regimeConditionIII regimeConditionIV
  refine ⟨?_, ?_, ?_⟩
  · intro h1
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨hC, _⟩
      linarith
    · rintro (⟨hC, _⟩ | ⟨hC, _⟩)
      · linarith
      · linarith
    · rintro ⟨hC, _⟩
      linarith
  · rintro ⟨hC, hB, hD⟩
    constructor
    · rintro (⟨_hCn, _hBp, hDz⟩ | ⟨_hCz, hBn⟩)
      · linarith
      · linarith
    · rintro ⟨_hCn, hrest⟩
      rcases hrest with hBn | hDn
      · linarith
      · linarith
  · intro h3
    rintro ⟨hCn, hrest⟩
    rcases h3 with ⟨_hCn, hBp, hDz⟩ | ⟨hCz, _hBn⟩
    · rcases hrest with hBn | hDn
      · linarith
      · linarith
    · linarith

end ChemotaxisBifurcation
