module
/-
Adapted from the MIT-licensed Paper III Lean package published at
chenle02/Chemataxis_Numerics, commit 5c7ef67e3c39e13daeef9321069e459b7444d04d.
-/

public import Mathlib

@[expose] public section

/-!
# Finite trigonometric identities for current Lemma 2.1
-/

namespace ChemotaxisBifurcation

theorem cos_sq (theta : ℝ) :
    Real.cos theta ^ 2 = (1 + Real.cos (2 * theta)) / 2 := by
  rw [Real.cos_two_mul]
  ring

theorem cos_mul_cos_two (theta : ℝ) :
    Real.cos theta * Real.cos (2 * theta) =
      (Real.cos theta + Real.cos (3 * theta)) / 2 := by
  calc
    Real.cos theta * Real.cos (2 * theta) =
        (Real.cos (theta + 2 * theta) +
          Real.cos (theta - 2 * theta)) / 2 := by
      rw [Real.cos_add, Real.cos_sub]
      ring_nf
    _ = (Real.cos theta + Real.cos (3 * theta)) / 2 := by
      rw [show theta - 2 * theta = -theta by ring_nf, Real.cos_neg]
      ring_nf

theorem cos_cube (theta : ℝ) :
    Real.cos theta ^ 3 =
      (3 * Real.cos theta + Real.cos (3 * theta)) / 4 := by
  rw [Real.cos_three_mul]
  ring_nf

theorem cos_mul_sin_two (theta : ℝ) :
    Real.cos theta * Real.sin (2 * theta) =
      (Real.sin theta + Real.sin (3 * theta)) / 2 := by
  calc
    Real.cos theta * Real.sin (2 * theta) =
        (Real.sin (2 * theta + theta) +
          Real.sin (2 * theta - theta)) / 2 := by
      rw [Real.sin_add, Real.sin_sub]
      ring_nf
    _ = (Real.sin theta + Real.sin (3 * theta)) / 2 := by ring_nf

theorem cos_two_mul_sin (theta : ℝ) :
    Real.cos (2 * theta) * Real.sin theta =
      (Real.sin (3 * theta) - Real.sin theta) / 2 := by
  calc
    Real.cos (2 * theta) * Real.sin theta =
        (Real.sin (theta + 2 * theta) +
          Real.sin (theta - 2 * theta)) / 2 := by
      rw [Real.sin_add, Real.sin_sub]
      ring_nf
    _ = (Real.sin (3 * theta) - Real.sin theta) / 2 := by
      rw [show theta - 2 * theta = -theta by ring_nf, Real.sin_neg]
      ring_nf

theorem cos_sq_mul_sin (theta : ℝ) :
    Real.cos theta ^ 2 * Real.sin theta =
      (Real.sin theta + Real.sin (3 * theta)) / 4 := by
  rw [cos_sq]
  calc
    (1 + Real.cos (2 * theta)) / 2 * Real.sin theta =
        (Real.sin theta + Real.cos (2 * theta) * Real.sin theta) / 2 := by ring
    _ = (Real.sin theta + Real.sin (3 * theta)) / 4 := by
      rw [cos_two_mul_sin]
      ring

end ChemotaxisBifurcation
