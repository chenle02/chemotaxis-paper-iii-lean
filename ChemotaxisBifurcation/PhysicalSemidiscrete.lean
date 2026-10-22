module
public import ChemotaxisBifurcation.SemidiscreteLimit
public import ChemotaxisBifurcation.Model

@[expose] public section

/-!
# Physical-parameter instances of threshold convergence

The prefactor here is the manuscript's positive multiplier. It is the reciprocal
of `PhysicalParams.thresholdK`, which occurs in the denominator of `chiStar`.
Both the logistic and fixed-mass parameter assumptions give the general
minimum-convergence theorem's hypotheses.
-/

namespace ChemotaxisBifurcation.Semidiscrete

open Filter
open scoped Topology

noncomputable section

def physicalPrefactor (p : PhysicalParams) (beta : ℝ) : ℝ :=
  p.signalOffset ^ beta / (p.nu * p.gamma * p.uStar ^ (p.m + p.gamma - 1))

theorem physicalPrefactor_pos (p : PhysicalParams) (beta : ℝ)
    (hnu : 0 < p.nu) (hgamma : 0 < p.gamma)
    (hu : 0 < p.uStar) (hv : 0 < p.vStar) :
    0 < physicalPrefactor p beta := by
  have hw : 0 < p.signalOffset := by unfold PhysicalParams.signalOffset; linarith
  unfold physicalPrefactor
  exact div_pos (Real.rpow_pos_of_pos hw _) (mul_pos (mul_pos hnu hgamma)
    (Real.rpow_pos_of_pos hu _))

theorem physicalPrefactor_eq_inv_thresholdK (p : PhysicalParams) (beta : ℝ)
    (hnu : 0 < p.nu) (hgamma : 0 < p.gamma)
    (hu : 0 < p.uStar) (hv : 0 < p.vStar) :
    physicalPrefactor p beta = 1 / p.thresholdK beta := by
  have hw : 0 < p.signalOffset := by unfold PhysicalParams.signalOffset; linarith
  have hum : p.uStar ^ p.m ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
  have hug : p.uStar ^ (p.gamma - 1) ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
  have hwb : p.signalOffset ^ beta ≠ 0 := (Real.rpow_pos_of_pos hw _).ne'
  unfold physicalPrefactor PhysicalParams.thresholdK PhysicalParams.mobilityB0
    PhysicalParams.signalC1Physical
  rw [show p.m + p.gamma - 1 = p.m + (p.gamma - 1) by ring, Real.rpow_add hu]
  field_simp [hnu.ne', hgamma.ne', hum, hug, hwb] <;> ring

theorem chiStar_eq_physical_modeThreshold (p : PhysicalParams) (x beta : ℝ)
    (hnu : 0 < p.nu) (hgamma : 0 < p.gamma)
    (hu : 0 < p.uStar) (hv : 0 < p.vStar) :
    p.chiStar x beta = modeThreshold (physicalPrefactor p beta) p.logisticSlope p.mu x := by
  rw [physicalPrefactor_eq_inv_thresholdK p beta hnu hgamma hu hv]
  unfold PhysicalParams.chiStar modeThreshold
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- The literal physical threshold minima converge in the logistic model. -/
theorem logistic_discreteCritical_tendsto (p : PhysicalParams) (beta L : ℝ)
    (hp : p.LogisticAdmissible) (hL : 0 < L) :
    Tendsto (discreteCritical (physicalPrefactor p beta) p.logisticSlope p.mu L)
      atTop (𝓝 (continuumCritical (physicalPrefactor p beta) p.logisticSlope p.mu L)) := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  apply discreteCritical_tendsto_continuumCritical
    (physicalPrefactor p beta) p.logisticSlope p.mu L
    (physicalPrefactor_pos p beta hnu hgamma hu hv) _ hmu.le hL
  exact mul_nonneg ha.le halpha.le

/-- The fixed-mass model has zero logistic slope, with the constant mode
excluded by the positive-mode definitions in both minima. -/
theorem fixedMass_discreteCritical_tendsto (p : PhysicalParams) (beta L : ℝ)
    (hp : p.FixedMassAdmissible) (hL : 0 < L) :
    Tendsto (discreteCritical (physicalPrefactor p beta) p.logisticSlope p.mu L)
      atTop (𝓝 (continuumCritical (physicalPrefactor p beta) p.logisticSlope p.mu L)) := by
  rcases hp with ⟨ha, hb, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  apply discreteCritical_tendsto_continuumCritical
    (physicalPrefactor p beta) p.logisticSlope p.mu L
    (physicalPrefactor_pos p beta hnu hgamma hu hv) _ hmu.le hL
  simp [PhysicalParams.logisticSlope, ha]

end

end ChemotaxisBifurcation.Semidiscrete
