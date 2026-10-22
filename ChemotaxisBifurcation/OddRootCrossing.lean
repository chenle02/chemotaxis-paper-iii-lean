module
public import ChemotaxisBifurcation.ModeRootCounts

@[expose] public section

/-!
# Local sign changes at odd-multiplicity roots

Mathlib supplies exact root-multiplicity factorization and nonvanishing of the
remaining factor, but no theorem directly packages the resulting local sign
change.  This file records that finite polynomial bridge and transports it to
the physical coefficient wherever the positive denominator comparison applies.
-/

namespace ChemotaxisBifurcation.OddRootCrossing

open Filter Polynomial
open ModeRootCounts PhysicalPolynomial

noncomputable section

/-- A nonzero real polynomial changes sign locally across every root of odd
multiplicity.  The neighborhood is explicit as a member of `𝒩 a`. -/
theorem polynomial_local_sign_change_of_odd_rootMultiplicity
    (P : ℝ[X]) (a : ℝ) (hP : P ≠ 0)
    (hodd : Odd (P.rootMultiplicity a)) :
    ∃ U : Set ℝ, U ∈ nhds a ∧
      ∀ x ∈ U, ∀ y ∈ U, x < a → a < y → P.eval x * P.eval y < 0 := by
  let m := P.rootMultiplicity a
  let Q := P /ₘ (X - C a) ^ m
  have hQa : Q.eval a ≠ 0 := by
    simpa [Q, m] using P.eval_divByMonic_pow_rootMultiplicity_ne_zero a hP
  have hfactor (z : ℝ) : P.eval z = (z - a) ^ m * Q.eval z := by
    have h := congrArg (eval z) (P.pow_mul_divByMonic_rootMultiplicity_eq a)
    simpa [Q, m, eval_mul, eval_pow, eval_sub, eval_X, eval_C] using h.symm
  rcases lt_or_gt_of_ne hQa with hQa_neg | hQa_pos
  · have hQneg : ∀ᶠ z in nhds a, Q.eval z < 0 :=
      Q.continuous.continuousAt.eventually (eventually_lt_nhds hQa_neg)
    refine ⟨{z | Q.eval z < 0}, hQneg, ?_⟩
    intro x hx y hy hxa hay
    have hxpow : (x - a) ^ m < 0 := hodd.pow_neg_iff.mpr (sub_neg.mpr hxa)
    have hypow : 0 < (y - a) ^ m := hodd.pow_pos_iff.mpr (sub_pos.mpr hay)
    have hPx : 0 < P.eval x := by
      rw [hfactor]
      exact mul_pos_of_neg_of_neg hxpow hx
    have hPy : P.eval y < 0 := by
      rw [hfactor]
      exact mul_neg_of_pos_of_neg hypow hy
    exact mul_neg_of_pos_of_neg hPx hPy
  · have hQpos : ∀ᶠ z in nhds a, 0 < Q.eval z :=
      Q.continuous.continuousAt.eventually (eventually_gt_nhds hQa_pos)
    refine ⟨{z | 0 < Q.eval z}, hQpos, ?_⟩
    intro x hx y hy hxa hay
    have hxpow : (x - a) ^ m < 0 := hodd.pow_neg_iff.mpr (sub_neg.mpr hxa)
    have hypow : 0 < (y - a) ^ m := hodd.pow_pos_iff.mpr (sub_pos.mpr hay)
    have hPx : P.eval x < 0 := by
      rw [hfactor]
      exact mul_neg_of_neg_of_pos hxpow hx
    have hPy : 0 < P.eval y := by
      rw [hfactor]
      exact mul_pos hypow hy
    exact mul_neg_of_neg_of_pos hPx hPy

/-- On an admissible eigenvalue neighborhood, an odd-multiplicity numerator
root produces a local sign switch of the actual assembled coefficient. -/
theorem physical_coefficient_local_sign_change_of_odd_rootMultiplicity
    (p : PhysicalParams) (beta a : ℝ) (hp : p.LogisticAdmissible)
    (hP : paperNumeratorPoly p beta ≠ 0)
    (hodd : Odd ((paperNumeratorPoly p beta).rootMultiplicity a)) :
    ∃ U : Set ℝ, U ∈ nhds a ∧
      ∀ x ∈ U, ∀ y ∈ U,
        Real.sqrt (p.logisticSlope * p.mu) / 2 < x →
        Real.sqrt (p.logisticSlope * p.mu) / 2 < y →
        x < a → a < y →
        logisticBetaCoefficient p x beta * logisticBetaCoefficient p y beta < 0 := by
  rcases polynomial_local_sign_change_of_odd_rootMultiplicity
      (paperNumeratorPoly p beta) a hP hodd with ⟨U, hU, hcross⟩
  refine ⟨U, hU, ?_⟩
  intro x hx y hy hadm_x hadm_y hxa hay
  have hnum := hcross x hx y hy hxa hay
  rcases (mul_neg_iff.mp hnum) with ⟨hnum_x, hnum_y⟩ | ⟨hnum_x, hnum_y⟩
  · have hcoef_x := (physical_coefficient_pos_iff p x beta hp hadm_x).mpr hnum_x
    have hcoef_y := (physical_coefficient_neg_iff p y beta hp hadm_y).mpr hnum_y
    exact mul_neg_of_pos_of_neg hcoef_x hcoef_y
  · have hcoef_x := (physical_coefficient_neg_iff p x beta hp hadm_x).mpr hnum_x
    have hcoef_y := (physical_coefficient_pos_iff p y beta hp hadm_y).mpr hnum_y
    exact mul_neg_of_neg_of_pos hcoef_x hcoef_y

/-- At an even-multiplicity point, a nonzero real polynomial has the same
strict sign at every two nearby points distinct from the center. -/
theorem polynomial_local_same_sign_of_even_rootMultiplicity
    (P : ℝ[X]) (a : ℝ) (hP : P ≠ 0)
    (heven : Even (P.rootMultiplicity a)) :
    ∃ U : Set ℝ, U ∈ nhds a ∧
      ∀ x ∈ U, ∀ y ∈ U, x ≠ a → y ≠ a → 0 < P.eval x * P.eval y := by
  let m := P.rootMultiplicity a
  let Q := P /ₘ (X - C a) ^ m
  have hQa : Q.eval a ≠ 0 := by
    simpa [Q, m] using P.eval_divByMonic_pow_rootMultiplicity_ne_zero a hP
  have hfactor (z : ℝ) : P.eval z = (z - a) ^ m * Q.eval z := by
    have h := congrArg (eval z) (P.pow_mul_divByMonic_rootMultiplicity_eq a)
    simpa [Q, m, eval_mul, eval_pow, eval_sub, eval_X, eval_C] using h.symm
  rcases lt_or_gt_of_ne hQa with hQa_neg | hQa_pos
  · have hQneg : ∀ᶠ z in nhds a, Q.eval z < 0 :=
      Q.continuous.continuousAt.eventually (eventually_lt_nhds hQa_neg)
    refine ⟨{z | Q.eval z < 0}, hQneg, ?_⟩
    intro x hx y hy hxa hya
    have hxpow : 0 < (x - a) ^ m := heven.pow_pos (sub_ne_zero.mpr hxa)
    have hypow : 0 < (y - a) ^ m := heven.pow_pos (sub_ne_zero.mpr hya)
    have hPx : P.eval x < 0 := by
      rw [hfactor]
      exact mul_neg_of_pos_of_neg hxpow hx
    have hPy : P.eval y < 0 := by
      rw [hfactor]
      exact mul_neg_of_pos_of_neg hypow hy
    exact mul_pos_of_neg_of_neg hPx hPy
  · have hQpos : ∀ᶠ z in nhds a, 0 < Q.eval z :=
      Q.continuous.continuousAt.eventually (eventually_gt_nhds hQa_pos)
    refine ⟨{z | 0 < Q.eval z}, hQpos, ?_⟩
    intro x hx y hy hxa hya
    have hxpow : 0 < (x - a) ^ m := heven.pow_pos (sub_ne_zero.mpr hxa)
    have hypow : 0 < (y - a) ^ m := heven.pow_pos (sub_ne_zero.mpr hya)
    have hPx : 0 < P.eval x := by
      rw [hfactor]
      exact mul_pos hxpow hx
    have hPy : 0 < P.eval y := by
      rw [hfactor]
      exact mul_pos hypow hy
    exact mul_pos hPx hPy

/-- The physical coefficient has the same local sign at admissible points on
both sides of an even-multiplicity numerator root. -/
theorem physical_coefficient_local_same_sign_of_even_rootMultiplicity
    (p : PhysicalParams) (beta a : ℝ) (hp : p.LogisticAdmissible)
    (hP : paperNumeratorPoly p beta ≠ 0)
    (heven : Even ((paperNumeratorPoly p beta).rootMultiplicity a)) :
    ∃ U : Set ℝ, U ∈ nhds a ∧
      ∀ x ∈ U, ∀ y ∈ U,
        Real.sqrt (p.logisticSlope * p.mu) / 2 < x →
        Real.sqrt (p.logisticSlope * p.mu) / 2 < y →
        x ≠ a → y ≠ a →
        0 < logisticBetaCoefficient p x beta * logisticBetaCoefficient p y beta := by
  rcases polynomial_local_same_sign_of_even_rootMultiplicity
      (paperNumeratorPoly p beta) a hP heven with ⟨U, hU, hsame⟩
  refine ⟨U, hU, ?_⟩
  intro x hx y hy hadm_x hadm_y hxa hya
  have hnum := hsame x hx y hy hxa hya
  rcases (mul_pos_iff.mp hnum) with ⟨hnum_x, hnum_y⟩ | ⟨hnum_x, hnum_y⟩
  · have hcoef_x := (physical_coefficient_pos_iff p x beta hp hadm_x).mpr hnum_x
    have hcoef_y := (physical_coefficient_pos_iff p y beta hp hadm_y).mpr hnum_y
    exact mul_pos hcoef_x hcoef_y
  · have hcoef_x := (physical_coefficient_neg_iff p x beta hp hadm_x).mpr hnum_x
    have hcoef_y := (physical_coefficient_neg_iff p y beta hp hadm_y).mpr hnum_y
    exact mul_pos_of_neg_of_neg hcoef_x hcoef_y

end

end ChemotaxisBifurcation.OddRootCrossing
