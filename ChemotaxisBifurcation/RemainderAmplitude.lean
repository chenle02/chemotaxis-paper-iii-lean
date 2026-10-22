module
public import ChemotaxisBifurcation.NormalForm

@[expose] public section

/-!
# Quantitative square-root approximation with a remainder

These finite inequalities apply to an existing nonzero equilibrium of the
reduced scalar equation. Branch existence and the analytic remainder estimates
are separate inputs, not consequences of the exact cubic polynomial alone.
-/

namespace ChemotaxisBifurcation.NormalForm

/-- Factoring a difference of squares bounds the magnitude error. -/
theorem magnitude_sqrt_error (s t : ℝ) (hs : s ≠ 0) (ht : 0 ≤ t) :
    abs (|s| - Real.sqrt t) ≤ |s ^ 2 - t| / |s| := by
  have hspos : 0 < |s| := abs_pos.mpr hs
  have hf : s ^ 2 - t = (|s| - Real.sqrt t) * (|s| + Real.sqrt t) := by
    nlinarith [sq_abs s, Real.sq_sqrt ht]
  apply (le_div_iff₀ hspos).mpr
  rw [hf, abs_mul, abs_of_nonneg (add_nonneg (abs_nonneg s) (Real.sqrt_nonneg t))]
  exact mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (Real.sqrt_nonneg t)) (abs_nonneg _)

/-- A cubic bound on the divided remainder gives a quadratic amplitude error.
This is a quantitative version of the square-root leading-amplitude step. -/
theorem remainder_magnitude_error (alpha beta eta s e C : ℝ)
    (hbeta : beta ≠ 0) (hs : s ≠ 0)
    (hroot : alpha * eta - beta * s ^ 2 + e = 0)
    (ht : 0 ≤ alpha * eta / beta) (herr : |e| ≤ C * |s| ^ 3) :
    abs (|s| - Real.sqrt (alpha * eta / beta)) ≤ C * s ^ 2 / |beta| := by
  have hb : |beta| ≠ 0 := abs_ne_zero.mpr hbeta
  have hsn : |s| ≠ 0 := abs_ne_zero.mpr hs
  calc
    abs (|s| - Real.sqrt (alpha * eta / beta))
        ≤ |s ^ 2 - alpha * eta / beta| / |s| := magnitude_sqrt_error s _ hs ht
    _ = (|e| / |beta|) / |s| := by
      rw [remainder_squared_amplitude_error alpha beta eta s e hbeta hroot]
    _ ≤ (C * |s| ^ 3 / |beta|) / |s| :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right herr (abs_nonneg beta)) (abs_nonneg s)
    _ = C * s ^ 2 / |beta| := by
      rw [show |s| ^ 3 = |s| ^ 2 * |s| by ring, sq_abs]
      field_simp

end ChemotaxisBifurcation.NormalForm
