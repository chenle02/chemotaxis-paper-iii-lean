module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
Reused exact-cubic core from the Paper III verification subtree.

# Paper III -- scalar normal-form endgame

This file verifies the exact cubic algebra underlying Step 5 in both local
bifurcation proofs.  It does not replace Hadamard's lemma, the implicit
function theorem, remainder control, or the center-manifold reduction.
-/

public import Mathlib

@[expose] public section

namespace ChemotaxisBifurcation.NormalForm

/-- The cubic leading part of the reduced scalar equation. -/
noncomputable def normalForm (alpha beta chi A : ℝ) : ℝ :=
  alpha * chi * A - beta * A ^ 3

/-- Every nonzero exact equilibrium satisfies the squared-amplitude formula. -/
theorem nonzero_equilibrium_sq (alpha beta chi A : ℝ)
    (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : normalForm alpha beta chi A = 0) :
    A ^ 2 = alpha * chi / beta := by
  unfold normalForm at hroot
  field_simp
  apply (mul_left_cancel₀ hA)
  nlinarith

/-- With positive transversality, a nonzero branch can occur only on the side
where `chi * beta > 0`. -/
theorem nonzero_equilibrium_branch_side (alpha beta chi A : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : normalForm alpha beta chi A = 0) :
    0 < chi * beta := by
  have hratio : 0 < alpha * chi / beta := by
    rw [← nonzero_equilibrium_sq alpha beta chi A hbeta hA hroot]
    exact sq_pos_of_ne_zero hA
  rcases (div_pos_iff.mp hratio) with h | h
  · have hchi : 0 < chi :=
      pos_of_mul_pos_left (by simpa [mul_comm] using h.1) halpha.le
    exact mul_pos hchi h.2
  · have hchi : chi < 0 :=
      neg_of_mul_neg_left (by simpa [mul_comm] using h.1) halpha.le
    exact mul_pos_of_neg_of_neg hchi h.2

/-- The leading squared amplitude is positive precisely on the branch side. -/
theorem amplitude_sq_pos (alpha beta chi : ℝ)
    (halpha : 0 < alpha) (hside : 0 < chi * beta) :
    0 < alpha * chi / beta := by
  have hchi_beta : 0 < chi / beta := by
    rcases (mul_pos_iff.mp hside) with h | h
    · exact div_pos h.1 h.2
    · exact div_pos_of_neg_of_neg h.1 h.2
  rw [show alpha * chi / beta = alpha * (chi / beta) by ring]
  exact mul_pos halpha hchi_beta

/-- The two displayed leading amplitudes are exact roots of the cubic leading
normal form. -/
theorem branch_amplitudes (alpha beta chi : ℝ)
    (halpha : 0 < alpha) (hside : 0 < chi * beta) :
    normalForm alpha beta chi (Real.sqrt (alpha * chi / beta)) = 0 ∧
      normalForm alpha beta chi (-Real.sqrt (alpha * chi / beta)) = 0 := by
  have hsquare : (Real.sqrt (alpha * chi / beta)) ^ 2 = alpha * chi / beta :=
    Real.sq_sqrt (amplitude_sq_pos alpha beta chi halpha hside).le
  have hbeta : beta ≠ 0 := by
    intro h
    simp [h] at hside
  have hcoef : alpha * chi - beta * Real.sqrt (alpha * chi / beta) ^ 2 = 0 := by
    rw [hsquare]
    field_simp
    ring
  constructor
  · unfold normalForm
    calc
      alpha * chi * Real.sqrt (alpha * chi / beta) -
          beta * Real.sqrt (alpha * chi / beta) ^ 3 =
          Real.sqrt (alpha * chi / beta) *
            (alpha * chi - beta * Real.sqrt (alpha * chi / beta) ^ 2) := by ring
      _ = 0 := by rw [hcoef, mul_zero]
  · unfold normalForm
    calc
      alpha * chi * (-Real.sqrt (alpha * chi / beta)) -
          beta * (-Real.sqrt (alpha * chi / beta)) ^ 3 =
          -Real.sqrt (alpha * chi / beta) *
            (alpha * chi - beta * Real.sqrt (alpha * chi / beta) ^ 2) := by ring
      _ = 0 := by rw [hcoef, mul_zero]

/-- These are the only two nonzero roots of the exact cubic leading normal
form. -/
theorem nonzero_equilibrium_eq_branch (alpha beta chi A : ℝ)
    (_halpha : 0 < alpha) (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : normalForm alpha beta chi A = 0) :
    A = Real.sqrt (alpha * chi / beta) ∨
      A = -Real.sqrt (alpha * chi / beta) := by
  have hsq := nonzero_equilibrium_sq alpha beta chi A hbeta hA hroot
  have hratio : 0 ≤ alpha * chi / beta := by
    rw [← hsq]
    positivity
  have hsqrt : (Real.sqrt (alpha * chi / beta)) ^ 2 = alpha * chi / beta :=
    Real.sq_sqrt hratio
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans hsqrt.symm)

/-- Derivative of the exact cubic vector field. -/
theorem deriv_normalForm (alpha beta chi A : ℝ) :
    deriv (normalForm alpha beta chi) A =
      alpha * chi - 3 * beta * A ^ 2 := by
  have hlin : HasDerivAt (fun x : ℝ => alpha * chi * x) (alpha * chi) A := by
    simpa using (hasDerivAt_id A).const_mul (alpha * chi)
  have hcub : HasDerivAt (fun x : ℝ => beta * x ^ 3) (3 * beta * A ^ 2) A := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id A).pow 3).const_mul beta
  change deriv (fun x : ℝ => alpha * chi * x - beta * x ^ 3) A =
    alpha * chi - 3 * beta * A ^ 2
  exact (hlin.sub hcub).deriv

/-- At a nonzero equilibrium, the linearization reduces exactly to
`-2 * alpha * chi`. -/
theorem deriv_at_nonzero_equilibrium (alpha beta chi A : ℝ)
    (hbeta : beta ≠ 0) (hA : A ≠ 0)
    (hroot : normalForm alpha beta chi A = 0) :
    deriv (normalForm alpha beta chi) A = -2 * alpha * chi := by
  rw [deriv_normalForm]
  rw [nonzero_equilibrium_sq alpha beta chi A hbeta hA hroot]
  field_simp [hbeta]
  ring

/-- Supercritical exact branches have negative scalar linearization. -/
theorem supercritical_deriv_neg (alpha beta chi A : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hA : A ≠ 0)
    (hroot : normalForm alpha beta chi A = 0) :
    deriv (normalForm alpha beta chi) A < 0 := by
  rw [deriv_at_nonzero_equilibrium alpha beta chi A hbeta.ne' hA hroot]
  have hside := nonzero_equilibrium_branch_side alpha beta chi A
    halpha hbeta.ne' hA hroot
  have hchi : 0 < chi := by
    rcases (mul_pos_iff.mp hside) with h | h
    · exact h.1
    · exact (hbeta.asymm h.2).elim
  nlinarith [mul_pos halpha hchi]

/-- Subcritical exact branches have positive scalar linearization. -/
theorem subcritical_deriv_pos (alpha beta chi A : ℝ)
    (halpha : 0 < alpha) (hbeta : beta < 0) (hA : A ≠ 0)
    (hroot : normalForm alpha beta chi A = 0) :
    0 < deriv (normalForm alpha beta chi) A := by
  rw [deriv_at_nonzero_equilibrium alpha beta chi A hbeta.ne hA hroot]
  have hside := nonzero_equilibrium_branch_side alpha beta chi A
    halpha hbeta.ne hA hroot
  have hchi : chi < 0 := by
    rcases (mul_pos_iff.mp hside) with h | h
    · exact (hbeta.asymm h.2).elim
    · exact h.1
  nlinarith [mul_pos halpha (neg_pos.mpr hchi)]

/-- A nonzero equilibrium of the divided reduced equation is on the predicted
side whenever its divided remainder is smaller than the cubic coefficient.
The premise is a quantitative remainder bound, not an existence assertion. -/
theorem remainder_equilibrium_side (alpha beta eta s e : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hroot : alpha * eta - beta * s ^ 2 + e = 0)
    (hsmall : |e| < |beta| * s ^ 2) : 0 < eta * beta := by
  have he := abs_le.mp (le_refl |e|)
  rcases lt_or_gt_of_ne hbeta with hb | hb
  · rw [abs_of_neg hb] at hsmall
    have hae : alpha * eta < 0 := by nlinarith
    have heta : eta < 0 := by
      by_contra h
      have hp := mul_nonneg halpha.le (le_of_not_gt h)
      linarith
    exact mul_pos_of_neg_of_neg heta hb
  · rw [abs_of_pos hb] at hsmall
    have hae : 0 < alpha * eta := by nlinarith
    have heta : 0 < eta := (mul_pos_iff_of_pos_left halpha).mp hae
    exact mul_pos heta hb

/-- Separate error bounds for the reduced function and its derivative give the
scalar derivative sign. No derivative estimate is inferred from a size bound. -/
theorem remainder_equilibrium_derivative_sign (alpha beta eta s e es ds : ℝ)
    (hbeta : beta ≠ 0)
    (hroot : alpha * eta - beta * s ^ 2 + e = 0)
    (hderiv : ds = alpha * eta - 3 * beta * s ^ 2 + es)
    (hsmall : |e| + |es| < 2 * |beta| * s ^ 2) : ds * beta < 0 := by
  have he := abs_le.mp (le_refl |e|)
  have hes := abs_le.mp (le_refl |es|)
  rcases lt_or_gt_of_ne hbeta with hb | hb
  · rw [abs_of_neg hb] at hsmall
    have hds : 0 < ds := by nlinarith
    exact mul_neg_of_pos_of_neg hds hb
  · rw [abs_of_pos hb] at hsmall
    have hds : ds < 0 := by nlinarith
    exact mul_neg_of_neg_of_pos hds hb

/-- Exact squared-amplitude error at an equilibrium of the divided equation. -/
theorem remainder_squared_amplitude_error (alpha beta eta s e : ℝ)
    (hbeta : beta ≠ 0)
    (hroot : alpha * eta - beta * s ^ 2 + e = 0) :
    |s ^ 2 - alpha * eta / beta| = |e| / |beta| := by
  have hid : s ^ 2 - alpha * eta / beta = e / beta := by
    apply (eq_div_iff hbeta).mpr
    field_simp
    nlinarith
  rw [hid, abs_div]

end ChemotaxisBifurcation.NormalForm
