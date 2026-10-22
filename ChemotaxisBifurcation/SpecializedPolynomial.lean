module
public import Mathlib

@[expose] public section

/-!
# Specialized coefficient polynomial

This module checks the finite algebra in the current Paper III specialized
example with

`a = b = mu = nu = m = alpha = gamma = 1`.

Source baseline: `09-26-2026-CRS-3-Le.tex`, SHA-256
`6132a4f21e03eca32dfcc1d242be718bf401ca0c63b7777c7149da263708d6ee`,
lines 1977--2125.  The root table is Table 2.2 (page 23), but this module does
not yet certify the table rows.

The definitions transcribe the displayed normalized numerator and denominator
from the manuscript.  The proofs independently check the shifted polynomial,
denominator positivity, and the two parameter ranges whose signs follow from
the shifted coefficients.

This module does not derive the rational coefficient from the PDE or the
center-manifold reduction.
-/

namespace ChemotaxisBifurcation.SpecializedPolynomial

noncomputable section

/-- Numerator of the specialized normalized cubic coefficient. -/
def numerator (lambda beta : ℝ) : ℝ :=
  (224 - 96 * beta) * lambda ^ 4
    + (192 - 152 * beta) * lambda ^ 3
    + (8 - 104 * beta - 16 * beta ^ 2) * lambda ^ 2
    + (96 - 28 * beta - 8 * beta ^ 2) * lambda
    + 56 + 11 * beta - beta ^ 2

/-- Positive denominator of the specialized normalized cubic coefficient. -/
def denominator (lambda : ℝ) : ℝ :=
  96 * (1 + lambda) * (4 * lambda ^ 2 - 1)

/-- The specialized normalized cubic coefficient as a rational function. -/
def coefficient (lambda beta : ℝ) : ℝ :=
  numerator lambda beta / denominator lambda

/-- The denominator is strictly positive on the manuscript's admissible range. -/
theorem denominator_pos {lambda : ℝ} (hlambda : 1 / 2 < lambda) :
    0 < denominator lambda := by
  have hleft : 0 < 2 * lambda - 1 := by linarith
  have hright : 0 < 2 * lambda + 1 := by linarith
  have hfactor : 0 < (2 * lambda - 1) * (2 * lambda + 1) :=
    mul_pos hleft hright
  have hone : 0 < 1 + lambda := by linarith
  rw [denominator]
  have hquad : 0 < 4 * lambda ^ 2 - 1 := by nlinarith
  positivity

/-- Exact expansion after shifting the admissible half-line by `lambda = t + 1/2`. -/
theorem numerator_shift (t beta : ℝ) :
    numerator (t + 1 / 2) beta =
      32 * (7 - 3 * beta) * t ^ 4
        + 8 * (80 - 43 * beta) * t ^ 3
        + 4 * (158 - 119 * beta - 4 * beta ^ 2) * t ^ 2
        + 6 * (60 - 49 * beta - 4 * beta ^ 2) * t
        + 9 * (2 - beta) * (beta + 8) := by
  unfold numerator
  ring

/-- Every shifted coefficient is positive for `0 <= beta <= 1`. -/
theorem numerator_pos_of_beta_mem_Icc {lambda beta : ℝ}
    (hlambda : 1 / 2 < lambda) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    0 < numerator lambda beta := by
  let t := lambda - 1 / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hbeta_sq : beta ^ 2 ≤ beta := by
    nlinarith [mul_nonneg hbeta0 (sub_nonneg.mpr hbeta1)]
  have hc4 : 0 < 32 * (7 - 3 * beta) := by nlinarith
  have hc3 : 0 < 8 * (80 - 43 * beta) := by nlinarith
  have h4 : 0 < 32 * (7 - 3 * beta) * t ^ 4 := mul_pos hc4 (pow_pos ht 4)
  have h3 : 0 < 8 * (80 - 43 * beta) * t ^ 3 := mul_pos hc3 (pow_pos ht 3)
  have h2 : 0 < 4 * (158 - 119 * beta - 4 * beta ^ 2) * t ^ 2 := by
    have : 0 < 158 - 119 * beta - 4 * beta ^ 2 := by nlinarith
    positivity
  have h1 : 0 < 6 * (60 - 49 * beta - 4 * beta ^ 2) * t := by
    have : 0 < 60 - 49 * beta - 4 * beta ^ 2 := by nlinarith
    positivity
  have hleft : 0 < 9 * (2 - beta) := by nlinarith
  have hright : 0 < beta + 8 := by linarith
  have h0 : 0 < 9 * (2 - beta) * (beta + 8) := mul_pos hleft hright
  rw [show lambda = t + 1 / 2 by dsimp [t]; ring, numerator_shift]
  positivity

/-- Every nonconstant shifted term is nonpositive, and the constant term is
strictly negative, for `beta >= 7/3`. -/
theorem numerator_neg_of_beta_ge_seven_thirds {lambda beta : ℝ}
    (hlambda : 1 / 2 < lambda) (hbeta : 7 / 3 ≤ beta) :
    numerator lambda beta < 0 := by
  let t := lambda - 1 / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hc4 : 32 * (7 - 3 * beta) ≤ 0 := by nlinarith
  have hc3 : 8 * (80 - 43 * beta) ≤ 0 := by nlinarith
  have hc2 : 4 * (158 - 119 * beta - 4 * beta ^ 2) ≤ 0 := by nlinarith
  have hc1 : 6 * (60 - 49 * beta - 4 * beta ^ 2) ≤ 0 := by nlinarith
  have hc0 : 9 * (2 - beta) * (beta + 8) < 0 := by
    have hleft : 2 - beta < 0 := by linarith
    have hright : 0 < beta + 8 := by linarith
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hleft) hright
  have h4 : 32 * (7 - 3 * beta) * t ^ 4 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc4 (by positivity)
  have h3 : 8 * (80 - 43 * beta) * t ^ 3 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc3 (le_of_lt (pow_pos ht 3))
  have h2 : 4 * (158 - 119 * beta - 4 * beta ^ 2) * t ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc2 (sq_nonneg t)
  have h1 : 6 * (60 - 49 * beta - 4 * beta ^ 2) * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc1 (le_of_lt ht)
  rw [show lambda = t + 1 / 2 by dsimp [t]; ring, numerator_shift]
  linarith

/-- The normalized coefficient is positive throughout the low-beta range. -/
theorem coefficient_pos_of_beta_mem_Icc {lambda beta : ℝ}
    (hlambda : 1 / 2 < lambda) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    0 < coefficient lambda beta := by
  exact div_pos (numerator_pos_of_beta_mem_Icc hlambda hbeta0 hbeta1)
    (denominator_pos hlambda)

/-- The normalized coefficient is negative throughout the high-beta range. -/
theorem coefficient_neg_of_beta_ge_seven_thirds {lambda beta : ℝ}
    (hlambda : 1 / 2 < lambda) (hbeta : 7 / 3 ≤ beta) :
    coefficient lambda beta < 0 := by
  exact div_neg_of_neg_of_pos (numerator_neg_of_beta_ge_seven_thirds hlambda hbeta)
    (denominator_pos hlambda)

/-- The small-domain critical exponent in the specialized example. -/
def betaSmallDomain : ℝ := 7 / 3

/-- The large-domain limiting coefficient in the specialized example. -/
def betaInfinity (beta : ℝ) : ℝ :=
  1 - (41 / 64) * beta - (25 / 576) * beta ^ 2

/-- The unique nonnegative zero of `betaInfinity`. -/
def betaLargeDomain : ℝ :=
  (3 * Real.sqrt 21529 - 369) / 50

/-- The second zero of `betaInfinity`, which lies below zero. -/
def betaLargeDomainNeg : ℝ :=
  (-3 * Real.sqrt 21529 - 369) / 50

theorem sqrt_21529_sq : (Real.sqrt 21529) ^ 2 = 21529 := by
  norm_num

theorem betaLargeDomain_mem_Ioo : betaLargeDomain ∈ Set.Ioo (1 : ℝ) 2 := by
  have hsqrt_lower : (140 : ℝ) < Real.sqrt 21529 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21529), Real.sqrt_nonneg 21529]
  have hsqrt_upper : Real.sqrt 21529 < (147 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21529), Real.sqrt_nonneg 21529]
  constructor <;> unfold betaLargeDomain <;> linarith

theorem betaLargeDomainNeg_neg : betaLargeDomainNeg < 0 := by
  have hsqrt : 0 ≤ Real.sqrt 21529 := Real.sqrt_nonneg 21529
  unfold betaLargeDomainNeg
  linarith

theorem betaInfinity_factor (beta : ℝ) :
    betaInfinity beta =
      -(25 / 576) * (beta - betaLargeDomain) * (beta - betaLargeDomainNeg) := by
  rw [betaInfinity, betaLargeDomain, betaLargeDomainNeg]
  have hsqrt := sqrt_21529_sq
  field_simp
  nlinarith

theorem betaInfinity_eq_zero : betaInfinity betaLargeDomain = 0 := by
  rw [betaInfinity_factor]
  ring

theorem betaInfinity_pos_of_nonneg_of_lt {beta : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta : beta < betaLargeDomain) :
    0 < betaInfinity beta := by
  rw [betaInfinity_factor]
  have hneg : betaLargeDomainNeg < beta := lt_of_lt_of_le betaLargeDomainNeg_neg hbeta0
  have hfactor1 : beta - betaLargeDomain < 0 := sub_neg.mpr hbeta
  have hfactor2 : 0 < beta - betaLargeDomainNeg := sub_pos.mpr hneg
  have hc : -(25 / 576 : ℝ) < 0 := by norm_num
  exact mul_pos (mul_pos_of_neg_of_neg hc hfactor1) hfactor2

theorem betaInfinity_neg_of_gt {beta : ℝ} (hbeta : betaLargeDomain < beta) :
    betaInfinity beta < 0 := by
  rw [betaInfinity_factor]
  have hroot_order : betaLargeDomainNeg < betaLargeDomain :=
    lt_trans betaLargeDomainNeg_neg (lt_trans (by norm_num) betaLargeDomain_mem_Ioo.1)
  have hfactor1 : 0 < beta - betaLargeDomain := sub_pos.mpr hbeta
  have hfactor2 : 0 < beta - betaLargeDomainNeg :=
    sub_pos.mpr (lt_trans hroot_order hbeta)
  have hc : -(25 / 576 : ℝ) < 0 := by norm_num
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc hfactor1) hfactor2

end

end ChemotaxisBifurcation.SpecializedPolynomial
