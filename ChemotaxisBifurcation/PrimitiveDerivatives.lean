module
public import ChemotaxisBifurcation.Taylor

@[expose] public section

/-!
# Positive-base derivative witnesses

The earlier scalar identities used Lean's totalized `deriv`.  This module adds
the differentiability witnesses needed to interpret those values as actual
Taylor coefficients at the positive manuscript equilibrium.
-/

namespace ChemotaxisBifurcation

/-- A real power has the expected derivative at a positive base. -/
theorem rpow_hasDerivAt
    (r x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ r) (r * x ^ (r - 1)) x := by
  exact Real.hasDerivAt_rpow_const (p := r) (Or.inl hx.ne')

/-- A real power is three-times continuously differentiable at a positive
base, supporting the manuscript coefficients through cubic order. -/
theorem rpow_contDiffAt_three
    (r x : ℝ) (hx : 0 < x) :
    ContDiffAt ℝ 3 (fun y : ℝ => y ^ r) x := by
  exact Real.contDiffAt_rpow_const (p := r) (Or.inl hx.ne')

/-- Positive-base witness for the density mobility `u^m`. -/
theorem mobility_hasDerivAt
    (m u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun y : ℝ => y ^ m) (m * u ^ (m - 1)) u :=
  rpow_hasDerivAt m u hu

/-- Positive-base cubic regularity of the density mobility. -/
theorem mobility_contDiffAt_three
    (m u : ℝ) (hu : 0 < u) :
    ContDiffAt ℝ 3 (fun y : ℝ => y ^ m) u :=
  rpow_contDiffAt_three m u hu

/-- Positive-base witness for the sensitivity weight `(1+v)^(-beta)`. -/
theorem sensitivity_hasDerivAt
    (beta w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun y : ℝ => y ^ (-beta))
      (-beta * w ^ (-beta - 1)) w := by
  exact rpow_hasDerivAt (-beta) w hw

/-- Positive-base cubic regularity of the sensitivity weight. -/
theorem sensitivity_contDiffAt_three
    (beta w : ℝ) (hw : 0 < w) :
    ContDiffAt ℝ 3 (fun y : ℝ => y ^ (-beta)) w :=
  rpow_contDiffAt_three (-beta) w hw

/-- Positive-base witness for the logistic power `u^(1+alpha)`. -/
theorem logistic_hasDerivAt
    (alpha u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun y : ℝ => y ^ (1 + alpha))
      ((1 + alpha) * u ^ alpha) u := by
  have hexp : 1 + alpha - 1 = alpha := by ring
  simpa only [hexp] using rpow_hasDerivAt (1 + alpha) u hu

/-- Positive-base cubic regularity of the logistic power. -/
theorem logistic_contDiffAt_three
    (alpha u : ℝ) (hu : 0 < u) :
    ContDiffAt ℝ 3 (fun y : ℝ => y ^ (1 + alpha)) u :=
  rpow_contDiffAt_three (1 + alpha) u hu

/-- Positive-base witness for the physical signal source `nu*u^gamma`. -/
theorem signal_source_hasDerivAt
    (nu gamma u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun y : ℝ => nu * y ^ gamma)
      (nu * gamma * u ^ (gamma - 1)) u := by
  simpa [mul_assoc] using (rpow_hasDerivAt gamma u hu).const_mul nu

/-- Positive-base cubic regularity of the physical signal source. -/
theorem signal_source_contDiffAt_three
    (nu gamma u : ℝ) (hu : 0 < u) :
    ContDiffAt ℝ 3 (fun y : ℝ => nu * y ^ gamma) u :=
  contDiffAt_const.mul (rpow_contDiffAt_three gamma u hu)

end ChemotaxisBifurcation
