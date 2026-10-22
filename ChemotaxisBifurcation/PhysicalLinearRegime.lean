module
public import ChemotaxisBifurcation.PhysicalModeGuards

@[expose] public section

/-!
# Physical consumers of modal growth and minimizer algebra

These results instantiate the ordered-field modal calculations with the
manuscript's physical coefficients. Semigroup and nonlinear PDE stability
remain outside this finite interface.
-/

namespace ChemotaxisBifurcation.PhysicalLinearRegime

open PhysicalModeGuards Thresholds

noncomputable section

theorem criticalSensitivity_eq_chiStar (p : PhysicalParams) (x beta : ℝ) :
    LinearRegime.criticalSensitivity (p.thresholdK beta) p.logisticSlope p.mu x =
      p.chiStar x beta := by
  unfold LinearRegime.criticalSensitivity Thresholds.modeThreshold Thresholds.modeFactor
    PhysicalParams.chiStar
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem physicalGrowth_eq_coupled (p : PhysicalParams) (chi x beta : ℝ) :
    LinearRegime.modalGrowth chi (p.thresholdK beta) p.logisticSlope p.mu x =
      Eigenmodes.growthRate (chi * p.mobilityB0 beta) p.signalC1Physical p.mu p.logisticSlope x := by
  unfold LinearRegime.modalGrowth Eigenmodes.growthRate PhysicalParams.thresholdK
  ring

theorem physicalGrowth_neg_iff (p : PhysicalParams) (chi x beta : ℝ)
    (hp : PositiveModeParameters p) (hx : 0 < x) :
    LinearRegime.modalGrowth chi (p.thresholdK beta) p.logisticSlope p.mu x < 0 ↔
      chi < p.chiStar x beta := by
  rw [LinearRegime.modalGrowth_neg_iff chi (p.thresholdK beta) p.logisticSlope p.mu x
    (thresholdK_pos p beta hp) hp.mu_pos.le hx,
    criticalSensitivity_eq_chiStar p x beta]

theorem physicalGrowth_pos_iff (p : PhysicalParams) (chi x beta : ℝ)
    (hp : PositiveModeParameters p) (hx : 0 < x) :
    0 < LinearRegime.modalGrowth chi (p.thresholdK beta) p.logisticSlope p.mu x ↔
      p.chiStar x beta < chi := by
  rw [LinearRegime.modalGrowth_pos_iff chi (p.thresholdK beta) p.logisticSlope p.mu x
    (thresholdK_pos p beta hp) hp.mu_pos.le hx,
    criticalSensitivity_eq_chiStar p x beta]

theorem physicalGrowth_zero_iff (p : PhysicalParams) (chi x beta : ℝ)
    (hp : PositiveModeParameters p) (hx : 0 < x) :
    LinearRegime.modalGrowth chi (p.thresholdK beta) p.logisticSlope p.mu x = 0 ↔
      chi = p.chiStar x beta := by
  rw [LinearRegime.modalGrowth_eq_zero_iff chi (p.thresholdK beta) p.logisticSlope p.mu x
    (thresholdK_pos p beta hp) hp.mu_pos.le hx,
    criticalSensitivity_eq_chiStar p x beta]

theorem strictCriticalMode_other_growth_neg (p : PhysicalParams) (d : ModeData)
    (beta : ℝ) (k : ℕ) (hp : PositiveModeParameters p)
    (hs : StrictCriticalMode p d beta) (hk : 0 < k) (hne : k ≠ d.n0) :
    LinearRegime.modalGrowth (p.chiStar d.eigenvalue beta) (p.thresholdK beta)
      p.logisticSlope p.mu (Semidiscrete.continuumLam d.L k) < 0 := by
  exact (physicalGrowth_neg_iff p _ _ beta hp (continuumLam_pos d.L k hs.1 hk)).mpr
    (hs.2.2 k hk hne)

/-- Zero forcing and a noncritical modal growth rate force the quadratic
coefficient to vanish; forcing support is supplied by the projection module. -/
theorem other_quadratic_coefficient_zero (p : PhysicalParams) (d : ModeData)
    (beta a : ℝ) (k : ℕ) (hp : PositiveModeParameters p)
    (hs : StrictCriticalMode p d beta) (hk : 0 < k) (hne : k ≠ d.n0)
    (hbalance : LinearRegime.modalGrowth (p.chiStar d.eigenvalue beta) (p.thresholdK beta)
      p.logisticSlope p.mu (Semidiscrete.continuumLam d.L k) * a = 0) : a = 0 := by
  have hg := strictCriticalMode_other_growth_neg p d beta k hp hs hk hne
  exact (mul_eq_zero.mp hbalance).resolve_left hg.ne

theorem chiStar_le_iff_modeFactor_le (p : PhysicalParams) (x y beta : ℝ)
    (hp : PositiveModeParameters p) :
    p.chiStar x beta ≤ p.chiStar y beta ↔
      modeFactor p.logisticSlope p.mu x ≤ modeFactor p.logisticSlope p.mu y := by
  rw [Semidiscrete.chiStar_eq_physical_modeThreshold p x beta hp.nu_pos hp.gamma_pos hp.u_pos hp.v_pos,
    Semidiscrete.chiStar_eq_physical_modeThreshold p y beta hp.nu_pos hp.gamma_pos hp.u_pos hp.v_pos]
  change Semidiscrete.physicalPrefactor p beta * modeFactor p.logisticSlope p.mu x ≤
      Semidiscrete.physicalPrefactor p beta * modeFactor p.logisticSlope p.mu y ↔ _
  exact mul_le_mul_iff_right₀ (Semidiscrete.physicalPrefactor_pos p beta
    hp.nu_pos hp.gamma_pos hp.u_pos hp.v_pos)

def MinimizingMode (p : PhysicalParams) (d : ModeData) (beta : ℝ) : Prop :=
  0 < d.L ∧ 0 < d.n0 ∧ ∀ k : ℕ, 0 < k →
    p.chiStar d.eigenvalue beta ≤ p.chiStar (Semidiscrete.continuumLam d.L k) beta

/-- The minimizing-mode predicate, including ties, is independent of beta. -/
theorem minimizingMode_beta_iff (p : PhysicalParams) (d : ModeData) (beta1 beta2 : ℝ)
    (hp : PositiveModeParameters p) :
    MinimizingMode p d beta1 ↔ MinimizingMode p d beta2 := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro k hk
    exact (chiStar_le_iff_modeFactor_le p _ _ beta2 hp).mpr
      ((chiStar_le_iff_modeFactor_le p _ _ beta1 hp).mp (h.2.2 k hk))
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro k hk
    exact (chiStar_le_iff_modeFactor_le p _ _ beta1 hp).mpr
      ((chiStar_le_iff_modeFactor_le p _ _ beta2 hp).mp (h.2.2 k hk))

end

end ChemotaxisBifurcation.PhysicalLinearRegime
