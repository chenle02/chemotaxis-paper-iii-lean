module
public import ChemotaxisBifurcation.BetaRegimes
public import ChemotaxisBifurcation.PhysicalModeGuards

@[expose] public section

/-!
# Physical beta-quadratic regimes

This module discharges the algebraic side conditions of `BetaQuadratic` from
primitive model positivity and a strict critical Neumann mode.  Its case
theorems use the constructed discriminant roots from `BetaRegimes`; no root or
negative-leading-coefficient premise is supplied externally.
-/

namespace ChemotaxisBifurcation

open PhysicalModeGuards

noncomputable section

def physicalBetaA (p : PhysicalParams) (d : ModeData) : ℝ :=
  betaLeading p d.eigenvalue

def physicalBetaB (p : PhysicalParams) (d : ModeData) (a0 : ℝ) : ℝ :=
  betaLinearAtA0 p d.eigenvalue a0

def physicalBetaC (p : PhysicalParams) (d : ModeData) (a0 : ℝ) : ℝ :=
  betaConstantAtA0 p d.eigenvalue a0

theorem physicalBetaCoefficientAtA0_quadratic
    (p : PhysicalParams) (d : ModeData) (betaRef a0 beta : ℝ)
    (hp : PositiveModeParameters p) (hc : StrictCriticalMode p d betaRef) :
    betaCoefficientAtA0 p d.eigenvalue a0 beta =
      betaQuadratic (physicalBetaA p d) (physicalBetaB p d a0)
        (physicalBetaC p d a0) beta := by
  have hx := mode_eigenvalue_pos d hc.1 hc.2.1
  have hw := signalOffset_pos p hp
  have hmuX : 0 < p.mu + d.eigenvalue := add_pos hp.mu_pos hx
  have hmu4 : 0 < p.mu + 4 * d.eigenvalue :=
    add_pos hp.mu_pos (mul_pos (by norm_num) hx)
  have hC := scaledCprime_pos p hp
  have hsigma := strictCriticalMode_sigma2_neg p d betaRef hp hc
  simpa [physicalBetaA, physicalBetaB, physicalBetaC, betaQuadratic] using
    betaCoefficientAtA0_quadratic p d.eigenvalue a0 beta
      hp.u_pos.ne' hw.ne' hp.mu_pos.ne' hmuX.ne' hmu4.ne' hC.ne'
      hx.ne' hsigma.ne

theorem logisticBetaCoefficient_physical_quadratic
    (p : PhysicalParams) (d : ModeData) (betaRef beta : ℝ)
    (hp : p.LogisticAdmissible) (hc : StrictCriticalMode p d betaRef) :
    logisticBetaCoefficient p d.eigenvalue beta =
      betaQuadratic (physicalBetaA p d)
        (physicalBetaB p d (logisticA0 p))
        (physicalBetaC p d (logisticA0 p)) beta := by
  exact physicalBetaCoefficientAtA0_quadratic p d betaRef (logisticA0 p) beta
    (logistic_positive_parameters p hp) hc

theorem fixedMassBetaCoefficient_physical_quadratic
    (p : PhysicalParams) (d : ModeData) (betaRef beta : ℝ)
    (hp : p.FixedMassAdmissible) (hc : StrictCriticalMode p d betaRef) :
    fixedMassBetaCoefficient p d.eigenvalue beta =
      betaQuadratic (physicalBetaA p d)
        (physicalBetaB p d fixedMassA0)
        (physicalBetaC p d fixedMassA0) beta := by
  exact physicalBetaCoefficientAtA0_quadratic p d betaRef fixedMassA0 beta
    (fixedMass_positive_parameters p hp) hc

theorem physicalBetaA_neg
    (p : PhysicalParams) (d : ModeData) (betaRef : ℝ)
    (hp : PositiveModeParameters p) (hc : StrictCriticalMode p d betaRef) :
    physicalBetaA p d < 0 := by
  have hx := mode_eigenvalue_pos d hc.1 hc.2.1
  have hw := signalOffset_pos p hp
  have hchi := chiStarTimesB0_pos p d.eigenvalue hp hx
  have hF := signalMode1_pos p d.eigenvalue hp hx
  have hx4 : 0 < 4 * d.eigenvalue := by positivity
  have hF4 := signalMode1_pos p (4 * d.eigenvalue) hp hx4
  have hsigma := strictCriticalMode_sigma2_neg p d betaRef hp hc
  have ha2 := secondModeA2Slope_neg p d.eigenvalue hx hchi hF hw hsigma
  have hG := cubicGSlope_neg p d.eigenvalue hF4 ha2
  exact betaLeading_neg p d.eigenvalue hx hchi hF hw hG

/-- Physical case (i), with its positive root constructed internally. -/
theorem physical_regime_case_i
    (p : PhysicalParams) (d : ModeData) (betaRef a0 : ℝ)
    (hp : PositiveModeParameters p) (hc : StrictCriticalMode p d betaRef)
    (hC : 0 < physicalBetaC p d a0) :
    (∀ beta, 0 ≤ beta →
      beta < betaPlus (physicalBetaA p d) (physicalBetaB p d a0)
        (physicalBetaC p d a0) →
      0 < betaCoefficientAtA0 p d.eigenvalue a0 beta) ∧
    (∀ beta,
      betaPlus (physicalBetaA p d) (physicalBetaB p d a0)
        (physicalBetaC p d a0) < beta →
      betaCoefficientAtA0 p d.eigenvalue a0 beta < 0) := by
  have hA := physicalBetaA_neg p d betaRef hp hc
  have hreg := regime_case_i (physicalBetaA p d) (physicalBetaB p d a0)
    (physicalBetaC p d a0) hA hC
  refine ⟨?_, ?_⟩
  · intro beta hbeta hlt
    rw [physicalBetaCoefficientAtA0_quadratic p d betaRef a0 beta hp hc]
    exact hreg.1 beta hbeta hlt
  · intro beta hgt
    rw [physicalBetaCoefficientAtA0_quadratic p d betaRef a0 beta hp hc]
    exact hreg.2.1 beta hgt

/-- Physical case (ii), with both nonnegative roots constructed internally. -/
theorem physical_regime_case_ii
    (p : PhysicalParams) (d : ModeData) (betaRef a0 : ℝ)
    (hp : PositiveModeParameters p) (hc : StrictCriticalMode p d betaRef)
    (hB : 0 < physicalBetaB p d a0) (hC : physicalBetaC p d a0 ≤ 0)
    (hD : 0 < betaDiscriminant (physicalBetaA p d)
      (physicalBetaB p d a0) (physicalBetaC p d a0)) :
    (∀ beta, 0 ≤ beta →
      beta < betaMinus (physicalBetaA p d) (physicalBetaB p d a0)
        (physicalBetaC p d a0) →
      betaCoefficientAtA0 p d.eigenvalue a0 beta < 0) ∧
    (∀ beta,
      betaMinus (physicalBetaA p d) (physicalBetaB p d a0)
          (physicalBetaC p d a0) < beta →
      beta < betaPlus (physicalBetaA p d) (physicalBetaB p d a0)
          (physicalBetaC p d a0) →
      0 < betaCoefficientAtA0 p d.eigenvalue a0 beta) ∧
    (∀ beta,
      betaPlus (physicalBetaA p d) (physicalBetaB p d a0)
          (physicalBetaC p d a0) < beta →
      betaCoefficientAtA0 p d.eigenvalue a0 beta < 0) := by
  have hA := physicalBetaA_neg p d betaRef hp hc
  have hreg := regime_case_ii (physicalBetaA p d) (physicalBetaB p d a0)
    (physicalBetaC p d a0) hA hB hC hD
  refine ⟨?_, ?_, ?_⟩
  · intro beta hbeta hlt
    rw [physicalBetaCoefficientAtA0_quadratic p d betaRef a0 beta hp hc]
    exact hreg.1 beta hbeta hlt
  · intro beta hlo hhi
    rw [physicalBetaCoefficientAtA0_quadratic p d betaRef a0 beta hp hc]
    exact hreg.2.1 beta hlo hhi
  · intro beta hhi
    rw [physicalBetaCoefficientAtA0_quadratic p d betaRef a0 beta hp hc]
    exact hreg.2.2 beta hhi

/-- Physical double-root part of case (iii). -/
theorem physical_regime_case_iii_double
    (p : PhysicalParams) (d : ModeData) (betaRef a0 : ℝ)
    (hp : PositiveModeParameters p) (hc : StrictCriticalMode p d betaRef)
    (hB : 0 < physicalBetaB p d a0)
    (hD : betaDiscriminant (physicalBetaA p d)
      (physicalBetaB p d a0) (physicalBetaC p d a0) = 0) :
    ∀ beta, 0 ≤ beta →
      beta ≠ betaDouble (physicalBetaA p d) (physicalBetaB p d a0) →
      betaCoefficientAtA0 p d.eigenvalue a0 beta < 0 := by
  have hA := physicalBetaA_neg p d betaRef hp hc
  have hreg := regime_case_iii_double (physicalBetaA p d)
    (physicalBetaB p d a0) (physicalBetaC p d a0) hA hB hD
  intro beta hbeta hne
  rw [physicalBetaCoefficientAtA0_quadratic p d betaRef a0 beta hp hc]
  exact hreg.1 beta hbeta hne

/-- Physical zero-root part of case (iii). -/
theorem physical_regime_case_iii_zero
    (p : PhysicalParams) (d : ModeData) (betaRef a0 : ℝ)
    (hp : PositiveModeParameters p) (hc : StrictCriticalMode p d betaRef)
    (hB : physicalBetaB p d a0 ≤ 0) (hC : physicalBetaC p d a0 = 0) :
    ∀ beta, 0 < beta → betaCoefficientAtA0 p d.eigenvalue a0 beta < 0 := by
  have hA := physicalBetaA_neg p d betaRef hp hc
  have hreg := regime_zero_root (physicalBetaA p d) (physicalBetaB p d a0)
    (physicalBetaC p d a0) hA hB hC
  intro beta hbeta
  rw [physicalBetaCoefficientAtA0_quadratic p d betaRef a0 beta hp hc]
  exact hreg.1 beta hbeta

/-- Physical everywhere-negative case when `B≤0` and `C<0`. -/
theorem physical_regime_case_iv_B_nonpos
    (p : PhysicalParams) (d : ModeData) (betaRef a0 : ℝ)
    (hp : PositiveModeParameters p) (hc : StrictCriticalMode p d betaRef)
    (hB : physicalBetaB p d a0 ≤ 0) (hC : physicalBetaC p d a0 < 0) :
    ∀ beta, 0 ≤ beta → betaCoefficientAtA0 p d.eigenvalue a0 beta < 0 := by
  have hA := physicalBetaA_neg p d betaRef hp hc
  intro beta hbeta
  rw [physicalBetaCoefficientAtA0_quadratic p d betaRef a0 beta hp hc]
  exact regime_everywhere_neg_of_B_nonpos _ _ _ hA hB hC beta hbeta

/-- Physical everywhere-negative case when the discriminant is negative. -/
theorem physical_regime_case_iv_discriminant_neg
    (p : PhysicalParams) (d : ModeData) (betaRef a0 : ℝ)
    (hp : PositiveModeParameters p) (hc : StrictCriticalMode p d betaRef)
    (hD : betaDiscriminant (physicalBetaA p d)
      (physicalBetaB p d a0) (physicalBetaC p d a0) < 0) :
    ∀ beta, betaCoefficientAtA0 p d.eigenvalue a0 beta < 0 := by
  have hA := physicalBetaA_neg p d betaRef hp hc
  intro beta
  rw [physicalBetaCoefficientAtA0_quadratic p d betaRef a0 beta hp hc]
  exact regime_everywhere_neg_of_discriminant_neg _ _ _ hA hD beta

end

end ChemotaxisBifurcation
