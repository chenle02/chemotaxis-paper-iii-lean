module
public import ChemotaxisBifurcation.PrimitiveDerivatives

@[expose] public section

/-!
# Equilibrium-subtracted logistic derivatives

Equation 2.9 uses the Taylor coefficients of
`x^(1+alpha) - (u*)^alpha x`, not the derivative of the pure power alone.
-/

namespace ChemotaxisBifurcation

open Filter
open scoped Topology

noncomputable def normalizedLogistic
    (alpha uStar x : ℝ) : ℝ :=
  x ^ (1 + alpha) - uStar ^ alpha * x

noncomputable def normalizedLogisticFirst
    (alpha uStar x : ℝ) : ℝ :=
  (1 + alpha) * x ^ alpha - uStar ^ alpha

noncomputable def normalizedLogisticSecond
    (alpha x : ℝ) : ℝ :=
  (1 + alpha) * alpha * x ^ (alpha - 1)

/-- The actual first derivative at the positive equilibrium is the paper's
`A' = alpha (u*)^alpha`. -/
theorem normalizedLogistic_hasDerivAt
    (alpha uStar : ℝ) (hu : 0 < uStar) :
    HasDerivAt (normalizedLogistic alpha uStar)
      (alpha * uStar ^ alpha) uStar := by
  have hp := logistic_hasDerivAt alpha uStar hu
  have hl : HasDerivAt (fun x : ℝ => uStar ^ alpha * x)
      (uStar ^ alpha) uStar := by
    simpa using (hasDerivAt_id uStar).const_mul (uStar ^ alpha)
  have hfun :
      (fun y : ℝ => y ^ (1 + alpha)) - (fun y => uStar ^ alpha * y) =
        normalizedLogistic alpha uStar := by
    funext y
    rfl
  rw [← hfun]
  have hv : (1 + alpha) * uStar ^ alpha - uStar ^ alpha =
      alpha * uStar ^ alpha := by ring
  rw [← hv]
  exact hp.sub hl

/-- The first-derivative formula has the expected second derivative. -/
theorem normalizedLogisticFirst_hasDerivAt
    (alpha uStar : ℝ) (hu : 0 < uStar) :
    HasDerivAt (normalizedLogisticFirst alpha uStar)
      ((1 + alpha) * alpha * uStar ^ (alpha - 1)) uStar := by
  have hp := (rpow_hasDerivAt alpha uStar hu).const_mul (1 + alpha)
  have hc : HasDerivAt (fun _ : ℝ => uStar ^ alpha) 0 uStar :=
    hasDerivAt_const uStar _
  have hfun :
      ((fun _ : ℝ => 1 + alpha) * fun y => y ^ alpha) -
          (fun _ => uStar ^ alpha) = normalizedLogisticFirst alpha uStar := by
    funext y
    simp [normalizedLogisticFirst]
  rw [← hfun]
  have hv : (1 + alpha) * (alpha * uStar ^ (alpha - 1)) - 0 =
      (1 + alpha) * alpha * uStar ^ (alpha - 1) := by ring
  rw [← hv]
  exact hp.sub hc

/-- The second-derivative formula has the expected third derivative. -/
theorem normalizedLogisticSecond_hasDerivAt
    (alpha uStar : ℝ) (hu : 0 < uStar) :
    HasDerivAt (normalizedLogisticSecond alpha)
      ((1 + alpha) * alpha * (alpha - 1) *
        uStar ^ (alpha - 2)) uStar := by
  have hexp : alpha - 1 - 1 = alpha - 2 := by ring
  have h := (rpow_hasDerivAt (alpha - 1) uStar hu).const_mul
    ((1 + alpha) * alpha)
  rw [hexp] at h
  have hfun :
      (fun _ : ℝ => (1 + alpha) * alpha) *
          (fun y => y ^ (alpha - 1)) = normalizedLogisticSecond alpha := by
    funext y
    simp [normalizedLogisticSecond]
  rw [← hfun]
  have hv : ((1 + alpha) * alpha) *
      ((alpha - 1) * uStar ^ (alpha - 2)) =
      (1 + alpha) * alpha * (alpha - 1) * uStar ^ (alpha - 2) := by ring
  rw [← hv]
  exact h

/-- The entered first-derivative formula is the actual derivative on a
positive neighborhood. -/
theorem normalizedLogistic_deriv_eq_first
    (alpha uStar x : ℝ) (hx : 0 < x) :
    deriv (normalizedLogistic alpha uStar) x =
      normalizedLogisticFirst alpha uStar x := by
  rw [(show HasDerivAt (normalizedLogistic alpha uStar)
      (normalizedLogisticFirst alpha uStar x) x by
        have hp := logistic_hasDerivAt alpha x hx
        have hl : HasDerivAt (fun y : ℝ => uStar ^ alpha * y)
            (uStar ^ alpha) x := by
          simpa using (hasDerivAt_id x).const_mul (uStar ^ alpha)
        have hfun :
            (fun y : ℝ => y ^ (1 + alpha)) -
                (fun y => uStar ^ alpha * y) =
              normalizedLogistic alpha uStar := by
          funext y
          rfl
        rw [← hfun]
        have hv : (1 + alpha) * x ^ alpha - uStar ^ alpha =
            normalizedLogisticFirst alpha uStar x := by
          unfold normalizedLogisticFirst
          rfl
        rw [← hv]
        exact hp.sub hl).deriv]

/-- The paper's raw logistic coefficients are the normalized derivative
values with factorials `1`, `1/2`, and `1/6`. -/
theorem rawTaylor_logistic_coefficients
    (p : PhysicalParams) (hu : 0 < p.uStar) :
    (rawTaylorData p 0).Aprime = p.alpha * p.uStar ^ p.alpha ∧
    2 * (rawTaylorData p 0).Asecond =
      (1 + p.alpha) * p.alpha * p.uStar ^ (p.alpha - 1) ∧
    6 * (rawTaylorData p 0).Athird =
      (1 + p.alpha) * p.alpha * (p.alpha - 1) *
        p.uStar ^ (p.alpha - 2) := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp [rawTaylorData] <;> ring

/-- Multiplying the paper's `A'` by `b` gives `a alpha` at a logistic
equilibrium. -/
theorem bAprime_eq_logisticSlope
    (p : PhysicalParams) (hlog : p.LogisticEquilibrium) :
    p.b * (rawTaylorData p 0).Aprime = p.logisticSlope := by
  unfold PhysicalParams.LogisticEquilibrium at hlog
  simp only [rawTaylorData, PhysicalParams.logisticSlope]
  rw [hlog]
  ring

end ChemotaxisBifurcation
