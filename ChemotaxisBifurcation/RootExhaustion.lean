module

public import ChemotaxisBifurcation.CertifiedRoots
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

namespace ChemotaxisBifurcation.RootExhaustion

open Polynomial
open ChemotaxisBifurcation.CertifiedRoots
open ChemotaxisBifurcation.SpecializedPolynomial

noncomputable section

def betaThreeHalvesPoly : ℝ[X] :=
  C 80 * X ^ 4 - C 36 * X ^ 3 - C 184 * X ^ 2 + C 36 * X + C (281 / 4)

def betaNineteenTenthsPoly : ℝ[X] :=
  C (208 / 5) * X ^ 4 - C (484 / 5) * X ^ 3 - C (6184 / 25) * X ^ 2 +
    C (348 / 25) * X + C (7329 / 100)

theorem betaThreeHalvesPoly_eval (x : ℝ) :
    betaThreeHalvesPoly.eval x = numerator x (3 / 2 : ℝ) := by
  simp [betaThreeHalvesPoly, numerator]
  ring

theorem betaNineteenTenthsPoly_eval (x : ℝ) :
    betaNineteenTenthsPoly.eval x = numerator x (19 / 10 : ℝ) := by
  simp [betaNineteenTenthsPoly, numerator]
  ring

theorem betaThreeHalvesPoly_natDegree : betaThreeHalvesPoly.natDegree = 4 := by
  unfold betaThreeHalvesPoly
  compute_degree <;> norm_num

theorem betaNineteenTenthsPoly_natDegree : betaNineteenTenthsPoly.natDegree = 4 := by
  unfold betaNineteenTenthsPoly
  compute_degree <;> norm_num

theorem roots_exhausted_of_four
    (p : ℝ[X]) (hp : p ≠ 0) (hdeg : p.natDegree ≤ 4)
    {r1 r2 r3 r4 : ℝ}
    (h12 : r1 < r2) (h23 : r2 < r3) (h34 : r3 < r4)
    (hr1 : p.IsRoot r1) (hr2 : p.IsRoot r2)
    (hr3 : p.IsRoot r3) (hr4 : p.IsRoot r4) :
    ∀ x : ℝ, p.IsRoot x ↔ x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4 := by
  classical
  let s : Finset ℝ := {r1, r2, r3, r4}
  have h13 : r1 < r3 := lt_trans h12 h23
  have h14 : r1 < r4 := lt_trans h13 h34
  have h24 : r2 < r4 := lt_trans h23 h34
  have hs_card : s.card = 4 := by
    dsimp [s]
    simp [h12.ne, h13.ne, h14.ne, h23.ne, h24.ne, h34.ne]
  have hs_sub : s ⊆ p.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots hp]
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hr1
    · exact hr2
    · exact hr3
    · exact hr4
  have hcard : p.roots.toFinset.card ≤ s.card := by
    calc
      p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le p.roots
      _ ≤ p.natDegree := card_roots' p
      _ ≤ 4 := hdeg
      _ = s.card := hs_card.symm
  have hs_eq : s = p.roots.toFinset := Finset.eq_of_subset_of_card_le hs_sub hcard
  intro x
  rw [← mem_roots hp, ← Multiset.mem_toFinset, ← hs_eq]
  simp [s, eq_comm]

theorem beta_three_halves_roots_exhaust :
    ∃ r1 r2 r3 r4 : ℝ,
      r1 ∈ Set.Icc (-1239 / 1000 : ℝ) (-1238 / 1000 : ℝ) ∧
      r2 ∈ Set.Icc (-604 / 1000 : ℝ) (-603 / 1000 : ℝ) ∧
      r3 ∈ Set.Icc (773 / 1000 : ℝ) (774 / 1000 : ℝ) ∧
      r4 ∈ Set.Icc (1518 / 1000 : ℝ) (1519 / 1000 : ℝ) ∧
      ∀ x : ℝ, numerator x (3 / 2 : ℝ) = 0 ↔
        x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4 := by
  rcases beta_three_halves_negative_first_root with ⟨r1, hr1, -⟩
  rcases beta_three_halves_negative_second_root with ⟨r2, hr2, -⟩
  rcases beta_three_halves_first_root with ⟨r3, hr3, -⟩
  rcases beta_three_halves_second_root with ⟨r4, hr4, -⟩
  have h12 : r1 < r2 := by linarith [hr1.1.2, hr2.1.1]
  have h23 : r2 < r3 := by linarith [hr2.1.2, hr3.1.1]
  have h34 : r3 < r4 := by linarith [hr3.1.2, hr4.1.1]
  have hp : betaThreeHalvesPoly ≠ 0 := by
    intro h
    have hc := congrArg (fun q : ℝ[X] => q.coeff 4) h
    norm_num [betaThreeHalvesPoly] at hc
  have hexhaust := roots_exhausted_of_four betaThreeHalvesPoly hp
    (by rw [betaThreeHalvesPoly_natDegree]) h12 h23 h34
    (by simpa [IsRoot, betaThreeHalvesPoly_eval] using hr1.2)
    (by simpa [IsRoot, betaThreeHalvesPoly_eval] using hr2.2)
    (by simpa [IsRoot, betaThreeHalvesPoly_eval] using hr3.2)
    (by simpa [IsRoot, betaThreeHalvesPoly_eval] using hr4.2)
  refine ⟨r1, r2, r3, r4, hr1.1, hr2.1, hr3.1, hr4.1, ?_⟩
  intro x
  simpa [IsRoot, betaThreeHalvesPoly_eval] using hexhaust x

theorem beta_nineteen_tenths_roots_exhaust :
    ∃ r1 r2 r3 r4 : ℝ,
      r1 ∈ Set.Icc (-1417 / 1000 : ℝ) (-1416 / 1000 : ℝ) ∧
      r2 ∈ Set.Icc (-613 / 1000 : ℝ) (-612 / 1000 : ℝ) ∧
      r3 ∈ Set.Icc (530 / 1000 : ℝ) (531 / 1000 : ℝ) ∧
      r4 ∈ Set.Icc (3826 / 1000 : ℝ) (3827 / 1000 : ℝ) ∧
      ∀ x : ℝ, numerator x (19 / 10 : ℝ) = 0 ↔
        x = r1 ∨ x = r2 ∨ x = r3 ∨ x = r4 := by
  rcases beta_nineteen_tenths_negative_first_root with ⟨r1, hr1, -⟩
  rcases beta_nineteen_tenths_negative_second_root with ⟨r2, hr2, -⟩
  rcases beta_nineteen_tenths_first_root with ⟨r3, hr3, -⟩
  rcases beta_nineteen_tenths_second_root with ⟨r4, hr4, -⟩
  have h12 : r1 < r2 := by linarith [hr1.1.2, hr2.1.1]
  have h23 : r2 < r3 := by linarith [hr2.1.2, hr3.1.1]
  have h34 : r3 < r4 := by linarith [hr3.1.2, hr4.1.1]
  have hp : betaNineteenTenthsPoly ≠ 0 := by
    intro h
    have hc := congrArg (fun q : ℝ[X] => q.coeff 4) h
    norm_num [betaNineteenTenthsPoly] at hc
  have hexhaust := roots_exhausted_of_four betaNineteenTenthsPoly hp
    (by rw [betaNineteenTenthsPoly_natDegree]) h12 h23 h34
    (by simpa [IsRoot, betaNineteenTenthsPoly_eval] using hr1.2)
    (by simpa [IsRoot, betaNineteenTenthsPoly_eval] using hr2.2)
    (by simpa [IsRoot, betaNineteenTenthsPoly_eval] using hr3.2)
    (by simpa [IsRoot, betaNineteenTenthsPoly_eval] using hr4.2)
  refine ⟨r1, r2, r3, r4, hr1.1, hr2.1, hr3.1, hr4.1, ?_⟩
  intro x
  simpa [IsRoot, betaNineteenTenthsPoly_eval] using hexhaust x

end

end ChemotaxisBifurcation.RootExhaustion

end
