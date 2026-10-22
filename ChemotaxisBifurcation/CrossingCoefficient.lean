module
public import ChemotaxisBifurcation.PhysicalModeGuards

@[expose] public section

/-!
# The crossing coefficient `α_{n₀}` (Eq. 2.44, label `E:alpha_n0`)

The manuscript states
`α_{n₀} = ∂_{χ₀} σ_{n₀}(χ*) = νγ (u*)^{m+γ-1} / (1+v*)^β · λ_{n₀}/(μ+λ_{n₀}) > 0`.
The physical modal growth rate is affine in the sensitivity, so its derivative
is the same at every sensitivity, in particular at the threshold `χ*`.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.CrossingCoefficient

open PhysicalModeGuards

noncomputable section

/-- The physical modal growth rate is affine in the sensitivity, with slope
`alphaN0`. -/
theorem modalGrowth_eq_affine (p : PhysicalParams) (chi x beta : ℝ) :
    LinearRegime.modalGrowth chi (p.thresholdK beta) p.logisticSlope p.mu x =
      p.alphaN0 x beta * chi + (-x - p.logisticSlope) := by
  unfold LinearRegime.modalGrowth Eigenmodes.growthRate PhysicalParams.alphaN0
  ring

/-- The sensitivity derivative of the physical modal growth rate is `alphaN0`
at every sensitivity. -/
theorem hasDerivAt_modalGrowth_chi (p : PhysicalParams) (x beta chi : ℝ) :
    HasDerivAt (fun c => LinearRegime.modalGrowth c (p.thresholdK beta) p.logisticSlope p.mu x)
      (p.alphaN0 x beta) chi := by
  have h : (fun c => LinearRegime.modalGrowth c (p.thresholdK beta) p.logisticSlope p.mu x) =
      fun c => p.alphaN0 x beta * c + (-x - p.logisticSlope) := by
    funext c
    exact modalGrowth_eq_affine p c x beta
  rw [h]
  simpa using ((hasDerivAt_id chi).const_mul (p.alphaN0 x beta)).add_const (-x - p.logisticSlope)

/-- `α_{n₀} = ∂_{χ₀} σ_{n₀}(χ*)`: the first equality of Eq. 2.44. -/
theorem deriv_modalGrowth_at_chiStar (p : PhysicalParams) (x beta : ℝ) :
    deriv (fun c => LinearRegime.modalGrowth c (p.thresholdK beta) p.logisticSlope p.mu x)
      (p.chiStar x beta) = p.alphaN0 x beta :=
  (hasDerivAt_modalGrowth_chi p x beta _).deriv

/-- The explicit value in Eq. 2.44: `νγ (u*)^{m+γ-1}/(1+v*)^β · x/(μ+x)`. -/
theorem alphaN0_eq_explicit (p : PhysicalParams) (x beta : ℝ) (hu : 0 < p.uStar) :
    p.alphaN0 x beta =
      p.nu * p.gamma * p.uStar ^ (p.m + p.gamma - 1) / p.signalOffset ^ beta *
        (x / (p.mu + x)) := by
  unfold PhysicalParams.alphaN0 PhysicalParams.thresholdK PhysicalParams.mobilityB0
    PhysicalParams.signalC1Physical
  rw [show p.m + p.gamma - 1 = p.m + (p.gamma - 1) by ring, Real.rpow_add hu]
  ring

/-- Eq. 2.44 in full at a positive eigenvalue: the derivative identification,
the explicit formula, and positivity. -/
theorem alpha_n0_display (p : PhysicalParams) (x beta : ℝ)
    (hp : PositiveModeParameters p) (hx : 0 < x) :
    deriv (fun c => LinearRegime.modalGrowth c (p.thresholdK beta) p.logisticSlope p.mu x)
        (p.chiStar x beta) =
      p.nu * p.gamma * p.uStar ^ (p.m + p.gamma - 1) / p.signalOffset ^ beta *
        (x / (p.mu + x)) ∧
      0 < p.alphaN0 x beta := by
  refine ⟨?_, alphaN0_pos p x beta hp hx⟩
  rw [deriv_modalGrowth_at_chiStar, alphaN0_eq_explicit p x beta hp.u_pos]

end

end ChemotaxisBifurcation.CrossingCoefficient
