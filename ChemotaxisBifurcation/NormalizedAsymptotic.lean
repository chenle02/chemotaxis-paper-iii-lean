module
public import ChemotaxisBifurcation.NormalizedSpecialization

@[expose] public section

/-!
# Large-eigenvalue asymptotic of the normalized coefficient (Eq. 3.7)

The 44-page manuscript states, for `a = b = μ = ν = m = α = γ = 1` and
`λ = λ_{n₀}`,
`β_{n₀} = (7/12 - β/4) λ + O(1)` as `λ → ∞` (label `E:new-beta-eq1`).

Subtracting the linear term from the exact ratio `P/Q` leaves a cubic over the
cubic `Q = 96(1+λ)(4λ²-1)`, which is bounded for `λ ≥ 1`.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.NormalizedAsymptotic

open Filter Asymptotics SpecializedPolynomial

noncomputable section

/-- The slope of the linear term in Eq. 3.7. -/
def slope (beta : ℝ) : ℝ := 7 / 12 - beta / 4

/-- The cubic remainder left after subtracting the linear term from `P`. -/
def remainderNumerator (lambda beta : ℝ) : ℝ :=
  (-32 - 56 * beta) * lambda ^ 3 + (64 - 128 * beta - 16 * beta ^ 2) * lambda ^ 2
    + (152 - 52 * beta - 8 * beta ^ 2) * lambda + (56 + 11 * beta - beta ^ 2)

theorem numerator_eq_slope_mul_add (lambda beta : ℝ) :
    numerator lambda beta =
      slope beta * lambda * denominator lambda + remainderNumerator lambda beta := by
  unfold numerator denominator slope remainderNumerator
  ring

/-- Exact identity behind Eq. 3.7 on the admissible half-line. -/
theorem coefficient_sub_linear {lambda beta : ℝ} (hlambda : 1 / 2 < lambda) :
    coefficient lambda beta - slope beta * lambda =
      remainderNumerator lambda beta / denominator lambda := by
  have hD : denominator lambda ≠ 0 := ne_of_gt (denominator_pos hlambda)
  rw [coefficient, numerator_eq_slope_mul_add, eq_div_iff hD]
  field_simp
  ring

/-- Explicit bound: for `λ ≥ 1` the remainder is at most `C/288`, with `C` the
sum of the absolute values of the remainder's coefficients. -/
theorem abs_coefficient_sub_linear_le {lambda beta : ℝ} (hlambda : 1 ≤ lambda) :
    |coefficient lambda beta - slope beta * lambda| ≤
      (|-32 - 56 * beta| + |64 - 128 * beta - 16 * beta ^ 2|
        + |152 - 52 * beta - 8 * beta ^ 2| + |56 + 11 * beta - beta ^ 2|) / 288 := by
  have hpos : 0 < lambda := by linarith
  have hD : 0 < denominator lambda := denominator_pos (by linarith)
  rw [coefficient_sub_linear (by linarith), abs_div, abs_of_pos hD,
    div_le_div_iff₀ hD (by norm_num : (0 : ℝ) < 288)]
  set c3 := -32 - 56 * beta
  set c2 := 64 - 128 * beta - 16 * beta ^ 2
  set c1 := 152 - 52 * beta - 8 * beta ^ 2
  set c0 := 56 + 11 * beta - beta ^ 2
  have h1 : lambda ≤ lambda ^ 3 := by
    simpa using pow_le_pow_right₀ hlambda (by norm_num : 1 ≤ 3)
  have h2 : lambda ^ 2 ≤ lambda ^ 3 := pow_le_pow_right₀ hlambda (by norm_num)
  have h3 : (1 : ℝ) ≤ lambda ^ 3 := one_le_pow₀ hlambda
  have hR : |remainderNumerator lambda beta| ≤ (|c3| + |c2| + |c1| + |c0|) * lambda ^ 3 := by
    have e : remainderNumerator lambda beta = c3 * lambda ^ 3 + c2 * lambda ^ 2 + c1 * lambda + c0 := by
      simp only [remainderNumerator, c3, c2, c1, c0]
    rw [e]
    have t3 : |c3 * lambda ^ 3| = |c3| * lambda ^ 3 := by
      rw [abs_mul, abs_of_pos (pow_pos hpos 3)]
    have t2 : |c2 * lambda ^ 2| = |c2| * lambda ^ 2 := by
      rw [abs_mul, abs_of_pos (pow_pos hpos 2)]
    have t1 : |c1 * lambda| = |c1| * lambda := by
      rw [abs_mul, abs_of_pos hpos]
    calc |c3 * lambda ^ 3 + c2 * lambda ^ 2 + c1 * lambda + c0|
        ≤ |c3 * lambda ^ 3| + |c2 * lambda ^ 2| + |c1 * lambda| + |c0| := by
          have := abs_add_three (c3 * lambda ^ 3) (c2 * lambda ^ 2) (c1 * lambda)
          have := abs_add_le (c3 * lambda ^ 3 + c2 * lambda ^ 2 + c1 * lambda) c0
          linarith
      _ = |c3| * lambda ^ 3 + |c2| * lambda ^ 2 + |c1| * lambda + |c0| := by rw [t3, t2, t1]
      _ ≤ (|c3| + |c2| + |c1| + |c0|) * lambda ^ 3 := by
          have := abs_nonneg c2
          have := abs_nonneg c1
          have := abs_nonneg c0
          nlinarith
  have hDlow : 288 * lambda ^ 3 ≤ denominator lambda := by
    unfold denominator
    nlinarith
  have hC : 0 ≤ |c3| + |c2| + |c1| + |c0| := by positivity
  nlinarith

/-- Eq. 3.7 for the normalized coefficient: `P/Q - (7/12 - β/4) λ = O(1)`. -/
theorem coefficient_sub_linear_isBigO (beta : ℝ) :
    (fun lambda => coefficient lambda beta - slope beta * lambda) =O[atTop]
      (fun _ => (1 : ℝ)) := by
  refine IsBigO.of_bound
    ((|-32 - 56 * beta| + |64 - 128 * beta - 16 * beta ^ 2|
        + |152 - 52 * beta - 8 * beta ^ 2| + |56 + 11 * beta - beta ^ 2|) / 288) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with lambda hlambda
  simpa [Real.norm_eq_abs] using abs_coefficient_sub_linear_le (beta := beta) hlambda

/-- Eq. 3.7 for the physical all-ones logistic cubic coefficient. -/
theorem logisticBetaCoefficient_allOnes_isBigO (beta : ℝ) :
    (fun lambda => logisticBetaCoefficient NormalizedSpecialization.allOnesParams lambda beta
        - (7 / 12 - beta / 4) * lambda) =O[atTop] (fun _ => (1 : ℝ)) := by
  refine (coefficient_sub_linear_isBigO beta).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 / 2 : ℝ)] with lambda hlambda
  rw [NormalizedSpecialization.logisticBetaCoefficient_allOnes hlambda, slope]

end

end ChemotaxisBifurcation.NormalizedAsymptotic
