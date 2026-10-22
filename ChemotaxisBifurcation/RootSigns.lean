module

public import ChemotaxisBifurcation.RootExhaustion

/-!
# Complementary signs around the certified positive roots

The root certificates and the degree argument locate and exhaust all real
roots.  This module uses continuity and the intermediate value theorem to
transport one exact rational sign evaluation across each root-free interval.
-/

@[expose] public section

namespace ChemotaxisBifurcation.RootSigns

open Set
open ChemotaxisBifurcation.SpecializedPolynomial
open ChemotaxisBifurcation.RootExhaustion

private theorem positive_of_anchor
    {f : ℝ → ℝ} (hf : Continuous f) {a x : ℝ}
    (ha : 0 < f a) (hzero : ∀ y ∈ uIcc a x, f y ≠ 0) :
    0 < f x := by
  by_contra h
  have hxle : f x ≤ 0 := le_of_not_gt h
  have hxne : f x ≠ 0 := hzero x right_mem_uIcc
  have hxlt : f x < 0 := lt_of_le_of_ne hxle hxne
  have hz : (0 : ℝ) ∈ uIcc (f a) (f x) := by
    rw [mem_uIcc]
    exact Or.inr ⟨hxlt.le, ha.le⟩
  obtain ⟨y, hy, hfy⟩ :=
    (Set.mem_image _ _ _).mp (intermediate_value_uIcc hf.continuousOn hz)
  exact hzero y hy hfy

private theorem negative_of_anchor
    {f : ℝ → ℝ} (hf : Continuous f) {a x : ℝ}
    (ha : f a < 0) (hzero : ∀ y ∈ uIcc a x, f y ≠ 0) :
    f x < 0 := by
  have hneg : 0 < (-f) a := by simpa using neg_pos.mpr ha
  have hz : ∀ y ∈ uIcc a x, (-f) y ≠ 0 := by
    intro y hy h
    apply hzero y hy
    simpa using h
  have := positive_of_anchor hf.neg hneg hz
  simpa using this

private theorem positive_between
    {f : ℝ → ℝ} (hf : Continuous f)
    {lo hi anchor : ℝ} (hlo : lo < anchor) (hhi : anchor < hi)
    (ha : 0 < f anchor)
    (hroots : ∀ y, f y = 0 → y ≤ lo ∨ hi ≤ y) :
    ∀ x, lo < x → x < hi → 0 < f x := by
  intro x hxlo hxhi
  apply positive_of_anchor hf ha
  intro y hy hfy
  rw [mem_uIcc] at hy
  have hylo : lo < y := by rcases hy with h | h <;> linarith
  have hyhi : y < hi := by rcases hy with h | h <;> linarith
  rcases hroots y hfy with h | h <;> linarith

private theorem negative_between
    {f : ℝ → ℝ} (hf : Continuous f)
    {lo hi anchor : ℝ} (hlo : lo < anchor) (hhi : anchor < hi)
    (ha : f anchor < 0)
    (hroots : ∀ y, f y = 0 → y ≤ lo ∨ hi ≤ y) :
    ∀ x, lo < x → x < hi → f x < 0 := by
  intro x hxlo hxhi
  apply negative_of_anchor hf ha
  intro y hy hfy
  rw [mem_uIcc] at hy
  have hylo : lo < y := by rcases hy with h | h <;> linarith
  have hyhi : y < hi := by rcases hy with h | h <;> linarith
  rcases hroots y hfy with h | h <;> linarith

private theorem positive_right
    {f : ℝ → ℝ} (hf : Continuous f)
    {lo anchor : ℝ} (hlo : lo < anchor) (ha : 0 < f anchor)
    (hroots : ∀ y, f y = 0 → y ≤ lo) :
    ∀ x, lo < x → 0 < f x := by
  intro x hx
  apply positive_of_anchor hf ha
  intro y hy hfy
  rw [mem_uIcc] at hy
  have hylo : lo < y := by rcases hy with h | h <;> linarith
  exact (not_lt_of_ge (hroots y hfy)) hylo

/-- For `beta=3/2`, the normalized numerator is positive, negative, positive
on the three admissible complementary intervals cut out by its two positive
roots. -/
theorem beta_three_halves_positive_root_signs :
    ∃ r3 r4 : ℝ,
      r3 ∈ Icc (773 / 1000 : ℝ) (774 / 1000 : ℝ) ∧
      r4 ∈ Icc (1518 / 1000 : ℝ) (1519 / 1000 : ℝ) ∧
      (∀ x, 1 / 2 < x → x < r3 → 0 < numerator x (3 / 2 : ℝ)) ∧
      (∀ x, r3 < x → x < r4 → numerator x (3 / 2 : ℝ) < 0) ∧
      (∀ x, r4 < x → 0 < numerator x (3 / 2 : ℝ)) := by
  rcases beta_three_halves_roots_exhaust with
    ⟨r1, r2, r3, r4, hr1, hr2, hr3, hr4, hexhaust⟩
  have hcont : Continuous (fun x : ℝ ↦ numerator x (3 / 2 : ℝ)) := by
    unfold numerator
    fun_prop
  have hhalf : 0 < numerator (51 / 100) (3 / 2 : ℝ) := by
    norm_num [numerator]
  have hone : numerator 1 (3 / 2 : ℝ) < 0 := by
    norm_num [numerator]
  have htwo : 0 < numerator 2 (3 / 2 : ℝ) := by
    norm_num [numerator]
  have hpre : ∀ y, numerator y (3 / 2 : ℝ) = 0 →
      y ≤ (1 / 2 : ℝ) ∨ r3 ≤ y := by
    intro y hy
    rcases (hexhaust y).mp hy with rfl | rfl | rfl | rfl
    · left; linarith [hr1.2]
    · left; linarith [hr2.2]
    · exact Or.inr le_rfl
    · right; linarith [hr3.2, hr4.1]
  have hmid : ∀ y, numerator y (3 / 2 : ℝ) = 0 →
      y ≤ r3 ∨ r4 ≤ y := by
    intro y hy
    rcases (hexhaust y).mp hy with rfl | rfl | rfl | rfl
    · left; linarith [hr1.2, hr3.1]
    · left; linarith [hr2.2, hr3.1]
    · exact Or.inl le_rfl
    · exact Or.inr le_rfl
  have hright : ∀ y, numerator y (3 / 2 : ℝ) = 0 → y ≤ r4 := by
    intro y hy
    rcases (hexhaust y).mp hy with rfl | rfl | rfl | rfl
    · linarith [hr1.2, hr4.1]
    · linarith [hr2.2, hr4.1]
    · linarith [hr3.2, hr4.1]
    · exact le_rfl
  refine ⟨r3, r4, hr3, hr4, ?_, ?_, ?_⟩
  · exact positive_between hcont (by norm_num) (by linarith [hr3.1]) hhalf hpre
  · exact negative_between hcont (by linarith [hr3.2])
      (by linarith [hr4.1]) hone hmid
  · exact positive_right hcont (by linarith [hr4.2]) htwo hright

/-- For `beta=19/10`, the normalized numerator has the same complementary
positive/negative/positive pattern around its two positive roots. -/
theorem beta_nineteen_tenths_positive_root_signs :
    ∃ r3 r4 : ℝ,
      r3 ∈ Icc (530 / 1000 : ℝ) (531 / 1000 : ℝ) ∧
      r4 ∈ Icc (3826 / 1000 : ℝ) (3827 / 1000 : ℝ) ∧
      (∀ x, 1 / 2 < x → x < r3 → 0 < numerator x (19 / 10 : ℝ)) ∧
      (∀ x, r3 < x → x < r4 → numerator x (19 / 10 : ℝ) < 0) ∧
      (∀ x, r4 < x → 0 < numerator x (19 / 10 : ℝ)) := by
  rcases beta_nineteen_tenths_roots_exhaust with
    ⟨r1, r2, r3, r4, hr1, hr2, hr3, hr4, hexhaust⟩
  have hcont : Continuous (fun x : ℝ ↦ numerator x (19 / 10 : ℝ)) := by
    unfold numerator
    fun_prop
  have hhalf : 0 < numerator (51 / 100) (19 / 10 : ℝ) := by
    norm_num [numerator]
  have hone : numerator 1 (19 / 10 : ℝ) < 0 := by
    norm_num [numerator]
  have hfour : 0 < numerator 4 (19 / 10 : ℝ) := by
    norm_num [numerator]
  have hpre : ∀ y, numerator y (19 / 10 : ℝ) = 0 →
      y ≤ (1 / 2 : ℝ) ∨ r3 ≤ y := by
    intro y hy
    rcases (hexhaust y).mp hy with rfl | rfl | rfl | rfl
    · left; linarith [hr1.2]
    · left; linarith [hr2.2]
    · exact Or.inr le_rfl
    · right; linarith [hr3.2, hr4.1]
  have hmid : ∀ y, numerator y (19 / 10 : ℝ) = 0 →
      y ≤ r3 ∨ r4 ≤ y := by
    intro y hy
    rcases (hexhaust y).mp hy with rfl | rfl | rfl | rfl
    · left; linarith [hr1.2, hr3.1]
    · left; linarith [hr2.2, hr3.1]
    · exact Or.inl le_rfl
    · exact Or.inr le_rfl
  have hright : ∀ y, numerator y (19 / 10 : ℝ) = 0 → y ≤ r4 := by
    intro y hy
    rcases (hexhaust y).mp hy with rfl | rfl | rfl | rfl
    · linarith [hr1.2, hr4.1]
    · linarith [hr2.2, hr4.1]
    · linarith [hr3.2, hr4.1]
    · exact le_rfl
  refine ⟨r3, r4, hr3, hr4, ?_, ?_, ?_⟩
  · exact positive_between hcont (by norm_num) (by linarith [hr3.1]) hhalf hpre
  · exact negative_between hcont (by linarith [hr3.2])
      (by linarith [hr4.1]) hone hmid
  · exact positive_right hcont (by linarith [hr4.2]) hfour hright

end ChemotaxisBifurcation.RootSigns

end
