module
public import ChemotaxisBifurcation.RationalCoefficient
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

/-!
# Polynomial degree bounds for the generic coefficient

The polynomial family is symbolic in every physical coefficient.  Concrete
examples specialize these theorems; they do not drive normalization.
-/

namespace ChemotaxisBifurcation.PolynomialDegree

open Polynomial
open ChemotaxisBifurcation.RationalCoefficient

noncomputable section

namespace RationalData

def pPoly (r : RationalData) : ℝ[X] := C r.mu + X
def qPoly (r : RationalData) : ℝ[X] := C r.mu + C 4 * X
def sPoly (r : RationalData) : ℝ[X] := X + C r.d
def deltaPoly (r : RationalData) : ℝ[X] := C (r.d * r.mu) - C 4 * X ^ 2

def n3Poly (r : RationalData) : ℝ[X] :=
  C (r.bA2 / 2 * r.K) * pPoly r * qPoly r -
    sPoly r *
      (C (2 * r.C2) * pPoly r ^ 2 +
        (C (r.bu * r.K) * pPoly r + C (r.bv * r.K ^ 2)) * qPoly r)

def n2Poly (r : RationalData) : ℝ[X] :=
  C (r.bA2 / 2 * r.K ^ 2) * pPoly r -
    C r.K * sPoly r *
      (C (r.bu * r.K) * pPoly r + C (r.bv * r.K ^ 2)) -
    C (r.K * r.C2 / 2) * pPoly r * (C 4 * X + C r.d)

def qNumeratorPoly (r : RationalData) : ℝ[X] :=
  C r.buu * pPoly r ^ 2 + C (r.buv * r.K) * pPoly r +
    C (r.bvv * r.K ^ 2)

def n4Poly (r : RationalData) : ℝ[X] :=
  C (24 * r.K * r.C2 * r.a0) * (pPoly r ^ 2 * deltaPoly r) +
    C (4 * r.C2) * (pPoly r * n3Poly r) +
    C (9 * r.K * r.C3) * (pPoly r ^ 2 * deltaPoly r) +
    C 4 * (pPoly r * (C r.bu * pPoly r + C (r.bv * r.K)) * n2Poly r) +
    C (12 * r.K ^ 2 * (r.bu * r.a0 + r.bv * r.E)) *
      (pPoly r ^ 2 * deltaPoly r) -
    C (2 * r.K * r.bu) * (pPoly r * n3Poly r) -
    C (2 * r.K * r.bv) * (pPoly r * n2Poly r) +
    C (3 * r.K ^ 2) * (qNumeratorPoly r * deltaPoly r)

def numeratorPoly (r : RationalData) : ℝ[X] :=
  C (-12 * r.K ^ 2 * r.betaConstant) * pPoly r ^ 2 * deltaPoly r -
    C (4 * r.K * r.bA2) * pPoly r * n3Poly r +
    sPoly r * n4Poly r

def denominatorPoly (r : RationalData) : ℝ[X] :=
  C (12 * r.K ^ 2) * pPoly r ^ 2 *
    (C 4 * X ^ 2 - C (r.d * r.mu))

theorem eval_pPoly (r : RationalData) (x : ℝ) :
    (pPoly r).eval x = r.p1 x := by
  simp [pPoly, RationalData.p1]

theorem eval_qPoly (r : RationalData) (x : ℝ) :
    (qPoly r).eval x = r.q x := by
  simp [qPoly, RationalData.q]

theorem eval_sPoly (r : RationalData) (x : ℝ) :
    (sPoly r).eval x = r.s x := by
  simp [sPoly, RationalData.s]

theorem eval_deltaPoly (r : RationalData) (x : ℝ) :
    (deltaPoly r).eval x = r.delta x := by
  simp [deltaPoly, RationalData.delta]

theorem eval_n3Poly (r : RationalData) (x : ℝ) :
    (n3Poly r).eval x = r.n3 x := by
  simp [n3Poly, RationalData.n3, pPoly, qPoly, sPoly,
    RationalData.p1, RationalData.q, RationalData.s]

theorem eval_n2Poly (r : RationalData) (x : ℝ) :
    (n2Poly r).eval x = r.n2 x := by
  simp [n2Poly, RationalData.n2, pPoly, sPoly,
    RationalData.p1, RationalData.s]
  ring

theorem eval_qNumeratorPoly (r : RationalData) (x : ℝ) :
    (qNumeratorPoly r).eval x = r.qNumerator x := by
  simp [qNumeratorPoly, RationalData.qNumerator, pPoly, RationalData.p1]

theorem eval_n4Poly (r : RationalData) (x : ℝ) :
    (n4Poly r).eval x = r.n4 x := by
  simp [n4Poly, RationalData.n4, pPoly, deltaPoly,
    eval_n3Poly, eval_n2Poly, eval_qNumeratorPoly,
    RationalData.p1, RationalData.delta] <;> ring

theorem eval_numeratorPoly (r : RationalData) (x : ℝ) :
    (numeratorPoly r).eval x = r.numerator x := by
  simp [numeratorPoly, RationalData.numerator, pPoly, sPoly, deltaPoly,
    eval_n3Poly, eval_n4Poly, RationalData.p1, RationalData.s,
    RationalData.delta]

theorem eval_denominatorPoly (r : RationalData) (x : ℝ) :
    (denominatorPoly r).eval x = r.denominator x := by
  simp [denominatorPoly, RationalData.denominator, pPoly, RationalData.p1]

/-- Coefficient of `X^5` in the constructed numerator. -/
def numeratorCoeff5 (r : RationalData) : ℝ :=
  -4 * (2 * r.C2 ^ 2 + 24 * r.C2 * r.K * r.a0 +
    5 * r.C2 * r.K * r.bu + 9 * r.C3 * r.K +
    12 * r.E * r.K ^ 2 * r.bv + 12 * r.K ^ 2 * r.a0 * r.bu -
    r.K ^ 2 * r.bu ^ 2 + 3 * r.K ^ 2 * r.buu)

/-- Coefficient of `X^4` in the constructed numerator. -/
def numeratorCoeff4 (r : RationalData) : ℝ :=
  -2 * (8 * r.C2 ^ 2 * r.d + 12 * r.C2 ^ 2 * r.mu +
    10 * r.C2 * r.K ^ 2 * r.bv + 48 * r.C2 * r.K * r.a0 * r.d +
    96 * r.C2 * r.K * r.a0 * r.mu - 8 * r.C2 * r.K * r.bA2 +
    17 * r.C2 * r.K * r.bu * r.d + 24 * r.C2 * r.K * r.bu * r.mu +
    18 * r.C3 * r.K * r.d + 36 * r.C3 * r.K * r.mu +
    24 * r.E * r.K ^ 2 * r.bv * r.d +
    48 * r.E * r.K ^ 2 * r.bv * r.mu - r.K ^ 3 * r.bu * r.bv +
    6 * r.K ^ 3 * r.buv - 48 * r.K ^ 2 * r.a0 * r.bA2 +
    24 * r.K ^ 2 * r.a0 * r.bu * r.d +
    48 * r.K ^ 2 * r.a0 * r.bu * r.mu -
    7 * r.K ^ 2 * r.bA2 * r.bu - 18 * r.K ^ 2 * r.bA3 -
    4 * r.K ^ 2 * r.bu ^ 2 * r.d - 3 * r.K ^ 2 * r.bu ^ 2 * r.mu +
    6 * r.K ^ 2 * r.buu * r.d + 12 * r.K ^ 2 * r.buu * r.mu)

def n3Coeff3 (r : RationalData) : ℝ :=
  -2 * (r.C2 + 2 * r.K * r.bu)

def n3Coeff2 (r : RationalData) : ℝ :=
  -2 * r.C2 * r.d - 4 * r.C2 * r.mu - 4 * r.K ^ 2 * r.bv +
    2 * r.K * r.bA2 - 4 * r.K * r.bu * r.d - 5 * r.K * r.bu * r.mu

def n2Coeff2 (r : RationalData) : ℝ :=
  -r.K * (2 * r.C2 + r.K * r.bu)

def n2Coeff1 (r : RationalData) : ℝ :=
  -r.K * (r.C2 * r.d + 4 * r.C2 * r.mu + 2 * r.K ^ 2 * r.bv -
    r.K * r.bA2 + 2 * r.K * r.bu * r.d + 2 * r.K * r.bu * r.mu) / 2

def qNumeratorCoeff1 (r : RationalData) : ℝ :=
  r.K * r.buv + 2 * r.buu * r.mu

def n4Coeff4 (r : RationalData) : ℝ := numeratorCoeff5 r

def n4Coeff3 (r : RationalData) : ℝ :=
  -2 * (4 * r.C2 ^ 2 * r.d + 12 * r.C2 ^ 2 * r.mu +
    10 * r.C2 * r.K ^ 2 * r.bv + 96 * r.C2 * r.K * r.a0 * r.mu -
    4 * r.C2 * r.K * r.bA2 + 7 * r.C2 * r.K * r.bu * r.d +
    24 * r.C2 * r.K * r.bu * r.mu + 36 * r.C3 * r.K * r.mu +
    48 * r.E * r.K ^ 2 * r.bv * r.mu - r.K ^ 3 * r.bu * r.bv +
    6 * r.K ^ 3 * r.buv + 48 * r.K ^ 2 * r.a0 * r.bu * r.mu +
    r.K ^ 2 * r.bA2 * r.bu - 2 * r.K ^ 2 * r.bu ^ 2 * r.d -
    3 * r.K ^ 2 * r.bu ^ 2 * r.mu + 12 * r.K ^ 2 * r.buu * r.mu)

theorem coeff_n3Poly_three (r : RationalData) :
    (n3Poly r).coeff 3 = n3Coeff3 r := by
  unfold n3Poly pPoly qPoly sPoly n3Coeff3
  compute_degree! <;> ring

theorem coeff_n3Poly_two (r : RationalData) :
    (n3Poly r).coeff 2 = n3Coeff2 r := by
  simp (config := { maxSteps := 200000 })
    [n3Poly, pPoly, qPoly, sPoly, n3Coeff2, Polynomial.coeff_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_add,
    Polynomial.coeff_sub, pow_two,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] <;> ring

theorem coeff_n2Poly_two (r : RationalData) :
    (n2Poly r).coeff 2 = n2Coeff2 r := by
  unfold n2Poly pPoly sPoly n2Coeff2
  compute_degree! <;> ring

theorem coeff_n2Poly_one (r : RationalData) :
    (n2Poly r).coeff 1 = n2Coeff1 r := by
  simp (config := { maxSteps := 200000 })
    [n2Poly, pPoly, sPoly, n2Coeff1, Polynomial.coeff_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_add,
    Polynomial.coeff_sub, pow_two,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] <;> ring

theorem coeff_qNumeratorPoly_one (r : RationalData) :
    (qNumeratorPoly r).coeff 1 = qNumeratorCoeff1 r := by
  simp [qNumeratorPoly, pPoly, qNumeratorCoeff1, Polynomial.coeff_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_add,
    pow_two, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] <;> ring

theorem coeff_pSquare_delta_three (r : RationalData) :
    (pPoly r ^ 2 * deltaPoly r).coeff 3 = -8 * r.mu := by
  simp [pPoly, deltaPoly, Polynomial.coeff_mul, Polynomial.coeff_C,
    Polynomial.coeff_X, Polynomial.coeff_add, Polynomial.coeff_sub, pow_two,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] <;> ring

theorem coeff_p_mul_n3_three (r : RationalData) :
    (pPoly r * n3Poly r).coeff 3 =
      r.mu * n3Coeff3 r + n3Coeff2 r := by
  rw [pPoly, add_mul, coeff_add, coeff_C_mul]
  have hx : (X * n3Poly r).coeff 3 = (n3Poly r).coeff 2 := by
    simpa using coeff_X_mul (n3Poly r) 2
  rw [hx, coeff_n3Poly_three, coeff_n3Poly_two]

theorem coeff_p_mul_n2_three (r : RationalData) :
    (pPoly r * n2Poly r).coeff 3 = n2Coeff2 r := by
  rw [pPoly, add_mul, coeff_add, coeff_C_mul]
  have hzero : (n2Poly r).coeff 3 = 0 := by
    unfold n2Poly pPoly sPoly
    compute_degree!
  have hx : (X * n2Poly r).coeff 3 = (n2Poly r).coeff 2 := by
    simpa using coeff_X_mul (n2Poly r) 2
  simp [hzero, hx, coeff_n2Poly_two]

theorem coeff_qNumerator_mul_delta_three (r : RationalData) :
    (qNumeratorPoly r * deltaPoly r).coeff 3 =
      -4 * qNumeratorCoeff1 r := by
  have hqzero : (qNumeratorPoly r).coeff 3 = 0 := by
    unfold qNumeratorPoly pPoly
    compute_degree!
  simp (config := { maxSteps := 200000 })
    [deltaPoly, Polynomial.coeff_mul, Polynomial.coeff_C,
    Polynomial.coeff_X, Polynomial.coeff_add, Polynomial.coeff_sub, pow_two,
    coeff_qNumeratorPoly_one, hqzero,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] <;> ring

theorem coeff_mixed_mul_n2_three (r : RationalData) :
    (pPoly r * (C r.bu * pPoly r + C (r.bv * r.K)) * n2Poly r).coeff 3 =
      (2 * r.bu * r.mu + r.bv * r.K) * n2Coeff2 r +
        r.bu * n2Coeff1 r := by
  let A : ℝ[X] := pPoly r * (C r.bu * pPoly r + C (r.bv * r.K))
  change (A * n2Poly r).coeff 3 = _
  have hA3 : A.coeff 3 = 0 := by
    dsimp [A]
    unfold pPoly
    compute_degree!
  have hA2 : A.coeff 2 = r.bu := by
    dsimp [A]
    unfold pPoly
    compute_degree! <;> ring
  have hA1 : A.coeff 1 = 2 * r.bu * r.mu + r.bv * r.K := by
    dsimp [A]
    rw [mul_coeff_one]
    simp [pPoly]
    ring
  have hn2zero : (n2Poly r).coeff 3 = 0 := by
    unfold n2Poly pPoly sPoly
    compute_degree!
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  rw [hn2zero, hA1, hA2, hA3, coeff_n2Poly_two, coeff_n2Poly_one]
  ring

theorem coeff_n4Poly_four (r : RationalData) :
    (n4Poly r).coeff 4 = n4Coeff4 r := by
  unfold n4Poly n3Poly n2Poly qNumeratorPoly
  unfold pPoly qPoly sPoly deltaPoly n4Coeff4 numeratorCoeff5
  compute_degree! <;> ring

theorem coeff_n4Poly_three (r : RationalData) :
    (n4Poly r).coeff 3 = n4Coeff3 r := by
  simp only [n4Poly, coeff_add, coeff_sub, coeff_C_mul,
    coeff_pSquare_delta_three, coeff_p_mul_n3_three,
    coeff_mixed_mul_n2_three, coeff_p_mul_n2_three,
    coeff_qNumerator_mul_delta_three]
  unfold n4Coeff3 n3Coeff3 n3Coeff2 n2Coeff2 n2Coeff1
  unfold qNumeratorCoeff1 RationalData.E
  ring

theorem coeff_numeratorPoly_five (r : RationalData) :
    (numeratorPoly r).coeff 5 = numeratorCoeff5 r := by
  unfold numeratorPoly n4Poly n3Poly n2Poly qNumeratorPoly
  unfold pPoly qPoly sPoly deltaPoly numeratorCoeff5
  compute_degree! <;> ring

set_option maxHeartbeats 800000 in
theorem coeff_numeratorPoly_four (r : RationalData) :
    (numeratorPoly r).coeff 4 = numeratorCoeff4 r := by
  have hn3four : (n3Poly r).coeff 4 = 0 :=
    by
      unfold n3Poly pPoly qPoly sPoly
      compute_degree!
  have hn4five : (n4Poly r).coeff 5 = 0 :=
    by
      unfold n4Poly n3Poly n2Poly qNumeratorPoly
      unfold pPoly qPoly sPoly deltaPoly
      compute_degree!
  simp [numeratorPoly, pPoly, sPoly, deltaPoly, numeratorCoeff4,
    Polynomial.coeff_mul, coeff_n3Poly_three, coeff_n4Poly_four,
    coeff_n4Poly_three, n3Coeff3, n4Coeff4, n4Coeff3, numeratorCoeff5,
    RationalData.betaConstant,
    hn3four, hn4five,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_add,
    Polynomial.coeff_sub, pow_two,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] <;>
    ring

theorem coeff_denominatorPoly_four (r : RationalData) :
    (denominatorPoly r).coeff 4 = 48 * r.K ^ 2 := by
  unfold denominatorPoly pPoly
  compute_degree! <;> ring

theorem coeff_denominatorPoly_three (r : RationalData) :
    (denominatorPoly r).coeff 3 = 96 * r.K ^ 2 * r.mu := by
  simp [denominatorPoly, pPoly, Polynomial.coeff_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_add,
    Polynomial.coeff_sub, pow_two,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] <;> ring

theorem natDegree_n3Poly_le (r : RationalData) :
    (n3Poly r).natDegree ≤ 3 := by
  unfold n3Poly pPoly qPoly sPoly
  compute_degree!

theorem natDegree_n2Poly_le (r : RationalData) :
    (n2Poly r).natDegree ≤ 2 := by
  unfold n2Poly pPoly sPoly
  compute_degree!

theorem natDegree_qNumeratorPoly_le (r : RationalData) :
    (qNumeratorPoly r).natDegree ≤ 2 := by
  unfold qNumeratorPoly pPoly
  compute_degree!

theorem natDegree_n4Poly_le (r : RationalData) :
    (n4Poly r).natDegree ≤ 4 := by
  have hn3 := natDegree_n3Poly_le r
  have hn2 := natDegree_n2Poly_le r
  have hq := natDegree_qNumeratorPoly_le r
  unfold n4Poly pPoly deltaPoly
  compute_degree!
  exact ⟨by omega, by exact ⟨by omega, by omega⟩⟩

theorem natDegree_numeratorPoly_le (r : RationalData) :
    (numeratorPoly r).natDegree ≤ 5 := by
  have hn3 := natDegree_n3Poly_le r
  have hn4 := natDegree_n4Poly_le r
  have hmax : max (n3Poly r).natDegree (n4Poly r).natDegree ≤ 4 :=
    max_le (hn3.trans (by norm_num)) hn4
  unfold numeratorPoly pPoly sPoly deltaPoly
  compute_degree!
  omega

theorem natDegree_denominatorPoly_le (r : RationalData) :
    (denominatorPoly r).natDegree ≤ 4 := by
  unfold denominatorPoly pPoly
  compute_degree!

/-- The quotient polynomial after canceling `x+μ` in the balanced case. -/
def balancedNumeratorPoly (r : RationalData) : ℝ[X] :=
  C (-12 * r.K ^ 2 * r.betaConstant) * pPoly r * deltaPoly r -
    C (4 * r.K * r.bA2) * n3Poly r + n4Poly r

def balancedDenominatorPoly (r : RationalData) : ℝ[X] :=
  C (12 * r.K ^ 2) * pPoly r *
    (C 4 * X ^ 2 - C (r.mu ^ 2))

theorem numeratorPoly_eq_pPoly_mul_balanced
    (r : RationalData) (hbalanced : r.d = r.mu) :
    numeratorPoly r = pPoly r * balancedNumeratorPoly r := by
  unfold numeratorPoly balancedNumeratorPoly sPoly
  rw [hbalanced]
  unfold pPoly
  ring

theorem denominatorPoly_eq_pPoly_mul_balanced
    (r : RationalData) (hbalanced : r.d = r.mu) :
    denominatorPoly r = pPoly r * balancedDenominatorPoly r := by
  unfold denominatorPoly balancedDenominatorPoly pPoly
  rw [hbalanced]
  ring

theorem natDegree_balancedNumeratorPoly_le (r : RationalData) :
    (balancedNumeratorPoly r).natDegree ≤ 4 := by
  have hn3 := natDegree_n3Poly_le r
  have hn4 := natDegree_n4Poly_le r
  unfold balancedNumeratorPoly pPoly deltaPoly
  compute_degree!
  exact ⟨hn3.trans (by norm_num), hn4⟩

theorem natDegree_balancedDenominatorPoly_le (r : RationalData) :
    (balancedDenominatorPoly r).natDegree ≤ 3 := by
  unfold balancedDenominatorPoly pPoly
  compute_degree!

theorem balanced_ratio_eq (r : RationalData) {x : ℝ}
    (hbalanced : r.d = r.mu) (hp : r.p1 x ≠ 0) :
    (numeratorPoly r).eval x / (denominatorPoly r).eval x =
      (balancedNumeratorPoly r).eval x /
        (balancedDenominatorPoly r).eval x := by
  rw [numeratorPoly_eq_pPoly_mul_balanced r hbalanced,
    denominatorPoly_eq_pPoly_mul_balanced r hbalanced]
  simp only [eval_mul, eval_pPoly]
  field_simp [hp]

end RationalData

end

end ChemotaxisBifurcation.PolynomialDegree
