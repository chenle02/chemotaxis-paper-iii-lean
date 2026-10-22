module
public import ChemotaxisBifurcation.PhysicalLinearRegime
public import ChemotaxisBifurcation.QuadraticModeSupport

@[expose] public section

/-!
# Physical vanishing of all other quadratic graph modes

The quadratic forcing has support only in modes zero and `2*n0`.  For every
other positive noncritical mode, strict criticality makes the modal growth
nonzero and the invariance balance forces its graph coefficient to vanish.
-/

namespace ChemotaxisBifurcation

open PhysicalModeGuards PhysicalLinearRegime

noncomputable section

theorem physical_other_quadratic_mode_zero
    (p : PhysicalParams) (d : ModeData) (beta c0 c2 ak : ℝ) (k : ℕ)
    (hp : PositiveModeParameters p) (hs : StrictCriticalMode p d beta)
    (hk : 0 < k) (hkcrit : k ≠ d.n0) (hk2 : k ≠ 2 * d.n0)
    (hbalance :
      LinearRegime.modalGrowth (p.chiStar d.eigenvalue beta) (p.thresholdK beta)
          p.logisticSlope p.mu (Semidiscrete.continuumLam d.L k) * ak +
        2 / d.L * (∫ y in (0 : ℝ)..d.L,
          quadraticForcingProfile c0 c2 d.L d.n0 y * neumannMode d.L k y) = 0) :
    ak = 0 := by
  have hproj := quadraticForcing_other_mode_projection_zero
    c0 c2 d.L d.n0 k hs.1 hk hk2
  rw [hproj, add_zero] at hbalance
  exact other_quadratic_coefficient_zero p d beta ak k hp hs hk hkcrit hbalance

end

end ChemotaxisBifurcation
