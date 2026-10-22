module
public import ChemotaxisBifurcation.BetaQuadratic

@[expose] public section

/-!
# Manuscript p/q decomposition and derivative coefficients

This module supplies the direct bridge to Equations 2.22 and 2.24.  It uses
the already assembled physical coefficient and its proved beta-polynomial
structure; it does not redefine the desired derivatives as answers.
-/

namespace ChemotaxisBifurcation.BetaDecomposition

open ChemotaxisBifurcation

noncomputable section

/-- The paper's `p(beta) = a_{2n0,1}(beta)`. -/
def pTerm (p : PhysicalParams) (x beta : ℝ) : ℝ :=
  secondModeA2 p x beta

/-- The paper's `q(beta) = chiStar(beta) * Gamma_n0^(3)(beta)`. -/
def qTerm (p : PhysicalParams) (x a0 beta : ℝ) : ℝ :=
  chiGamma3 p x beta (quadraticJetData p x beta a0)

/-- Equation 2.22, with an explicit constant graph mode. -/
theorem betaCoefficientAtA0_eq_pq
    (p : PhysicalParams) (x a0 beta : ℝ) :
    betaCoefficientAtA0 p x a0 beta =
      (mobilityScaledTaylor p beta).bAsecond / 2 *
          (4 * a0 + 2 * pTerm p x beta) -
        qTerm p x a0 beta +
        3 * (mobilityScaledTaylor p beta).bAthird / 4 := by
  rfl

/-- `p(beta)` is affine, with the already derived second-mode slope. -/
theorem pTerm_eq_affine
    (p : PhysicalParams) (x beta : ℝ)
    (hW : p.signalOffset ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    pTerm p x beta = pTerm p x 0 + secondModeA2Slope p x * beta := by
  exact secondModeA2_eq_affine p x beta hW hsigma

def qQuadraticA (p : PhysicalParams) (x : ℝ) : ℝ :=
  -betaLeading p x

def qQuadraticB (p : PhysicalParams) (x a0 : ℝ) : ℝ :=
  (mobilityScaledTaylor p 0).bAsecond * secondModeA2Slope p x -
    betaLinearAtA0 p x a0

def qQuadraticC (p : PhysicalParams) (x a0 : ℝ) : ℝ :=
  (mobilityScaledTaylor p 0).bAsecond / 2 *
      (4 * a0 + 2 * pTerm p x 0) +
    3 * (mobilityScaledTaylor p 0).bAthird / 4 -
    betaConstantAtA0 p x a0

/-- The paper's `q(beta)` has degree at most two. -/
theorem qTerm_eq_quadratic
    (p : PhysicalParams) (x a0 beta : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hmux : p.mu + x ≠ 0)
    (hmu4 : p.mu + 4 * x ≠ 0)
    (hC : (mobilityScaledTaylor p 0).Cprime ≠ 0)
    (hx : x ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    qTerm p x a0 beta =
      qQuadraticA p x * beta ^ 2 + qQuadraticB p x a0 * beta +
        qQuadraticC p x a0 := by
  have hcoeff := betaCoefficientAtA0_quadratic p x a0 beta
    hU hW hmu hmux hmu4 hC hx hsigma
  have hpaff := pTerm_eq_affine p x beta hW hsigma
  have hpq := betaCoefficientAtA0_eq_pq p x a0 beta
  rw [hpaff, hcoeff] at hpq
  unfold qQuadraticA qQuadraticB qQuadraticC
  have hbA2 : (mobilityScaledTaylor p beta).bAsecond =
      (mobilityScaledTaylor p 0).bAsecond := rfl
  have hbA3 : (mobilityScaledTaylor p beta).bAthird =
      (mobilityScaledTaylor p 0).bAthird := rfl
  rw [hbA2, hbA3] at hpq
  linarith

private theorem deriv_affine_zero (a b : ℝ) :
    deriv (fun beta : ℝ => a + b * beta) 0 = b := by
  have h : HasDerivAt (fun beta : ℝ => a + b * beta) b 0 := by
    convert (hasDerivAt_const (0 : ℝ) a).add
      ((hasDerivAt_id (0 : ℝ)).const_mul b) using 1
    all_goals try simp only [id_eq]
    all_goals first | rfl | ring
  exact h.deriv

private theorem deriv_quadratic_zero (A B C : ℝ) :
    deriv (fun beta : ℝ => A * beta ^ 2 + B * beta + C) 0 = B := by
  have h := ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul A).add
    ((hasDerivAt_id (0 : ℝ)).const_mul B)).add_const C
  convert h.deriv using 1 <;> norm_num <;> ring

private theorem iterDeriv_two_quadratic_zero (A B C : ℝ) :
    (deriv^[2] (fun beta : ℝ => A * beta ^ 2 + B * beta + C)) 0 = 2 * A := by
  have hfirst : deriv (fun beta : ℝ => A * beta ^ 2 + B * beta + C) =
      fun beta => 2 * A * beta + B := by
    funext beta
    have h := ((((hasDerivAt_id beta).pow 2).const_mul A).add
      ((hasDerivAt_id beta).const_mul B)).add_const C
    convert h.deriv using 1 <;> norm_num <;> ring
  simp only [Function.iterate_succ_apply, hfirst]
  convert (((hasDerivAt_id (0 : ℝ)).const_mul (2 * A)).add_const B).deriv using 1 <;>
    norm_num <;> ring

theorem deriv_pTerm_zero
    (p : PhysicalParams) (x : ℝ)
    (hW : p.signalOffset ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    deriv (pTerm p x) 0 = secondModeA2Slope p x := by
  have hfun : pTerm p x = fun beta =>
      pTerm p x 0 + secondModeA2Slope p x * beta := by
    funext beta
    exact pTerm_eq_affine p x beta hW hsigma
  rw [hfun]
  exact deriv_affine_zero _ _

theorem deriv_qTerm_zero
    (p : PhysicalParams) (x a0 : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hmux : p.mu + x ≠ 0)
    (hmu4 : p.mu + 4 * x ≠ 0)
    (hC : (mobilityScaledTaylor p 0).Cprime ≠ 0)
    (hx : x ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    deriv (qTerm p x a0) 0 = qQuadraticB p x a0 := by
  have hfun : qTerm p x a0 = fun beta =>
      qQuadraticA p x * beta ^ 2 + qQuadraticB p x a0 * beta +
        qQuadraticC p x a0 := by
    funext beta
    exact qTerm_eq_quadratic p x a0 beta hU hW hmu hmux hmu4 hC hx hsigma
  rw [hfun]
  exact deriv_quadratic_zero _ _ _

theorem iterDeriv_two_qTerm_zero
    (p : PhysicalParams) (x a0 : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hmux : p.mu + x ≠ 0)
    (hmu4 : p.mu + 4 * x ≠ 0)
    (hC : (mobilityScaledTaylor p 0).Cprime ≠ 0)
    (hx : x ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    (deriv^[2] (qTerm p x a0)) 0 = 2 * qQuadraticA p x := by
  have hfun : qTerm p x a0 = fun beta =>
      qQuadraticA p x * beta ^ 2 + qQuadraticB p x a0 * beta +
        qQuadraticC p x a0 := by
    funext beta
    exact qTerm_eq_quadratic p x a0 beta hU hW hmu hmux hmu4 hC hx hsigma
  rw [hfun]
  exact iterDeriv_two_quadratic_zero _ _ _

/-- Equation 2.24 coefficient `A = -q''(0)/2`. -/
theorem betaLeading_eq_neg_half_q_second
    (p : PhysicalParams) (x a0 : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hmux : p.mu + x ≠ 0)
    (hmu4 : p.mu + 4 * x ≠ 0)
    (hC : (mobilityScaledTaylor p 0).Cprime ≠ 0)
    (hx : x ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    betaLeading p x = -(deriv^[2] (qTerm p x a0)) 0 / 2 := by
  rw [iterDeriv_two_qTerm_zero p x a0 hU hW hmu hmux hmu4 hC hx hsigma]
  unfold qQuadraticA
  ring

/-- Equation 2.24 coefficient `B = bA'' p'(0) - q'(0)`. -/
theorem betaLinear_eq_bA2_mul_p_deriv_sub_q_deriv
    (p : PhysicalParams) (x a0 : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hmux : p.mu + x ≠ 0)
    (hmu4 : p.mu + 4 * x ≠ 0)
    (hC : (mobilityScaledTaylor p 0).Cprime ≠ 0)
    (hx : x ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    betaLinearAtA0 p x a0 =
      (mobilityScaledTaylor p 0).bAsecond * deriv (pTerm p x) 0 -
        deriv (qTerm p x a0) 0 := by
  rw [deriv_pTerm_zero p x hW hsigma,
    deriv_qTerm_zero p x a0 hU hW hmu hmux hmu4 hC hx hsigma]
  unfold qQuadraticB
  ring

/-- Equation 2.24 constant coefficient. -/
theorem betaConstant_eq_pq_at_zero (p : PhysicalParams) (x a0 : ℝ) :
    betaConstantAtA0 p x a0 =
      (mobilityScaledTaylor p 0).bAsecond / 2 *
          (4 * a0 + 2 * pTerm p x 0) -
        qTerm p x a0 0 + 3 * (mobilityScaledTaylor p 0).bAthird / 4 := by
  exact betaCoefficientAtA0_eq_pq p x a0 0

end

end ChemotaxisBifurcation.BetaDecomposition
