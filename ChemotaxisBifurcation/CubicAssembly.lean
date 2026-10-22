module
public import ChemotaxisBifurcation.FiniteProjection
public import ChemotaxisBifurcation.QuadraticJet

@[expose] public section

/-!
# Mobility-scaled cubic coefficient assembly

This module provides the shared all-parameter definitions consumed by the
polynomial proof.  Separate projection theorems must derive these formulas
from the primitive Taylor data and four finite harmonic projections.
-/

namespace ChemotaxisBifurcation

/-- Raw quadratic projection data reconstructed from `B₀` and the audited
mobility-scaled coefficients. -/
noncomputable def quadraticProjectionData
    (p : PhysicalParams) (x beta : ℝ) : QuadraticProjectionData :=
  let t := mobilityScaledTaylor p beta
  let B0 := p.mobilityB0 beta
  {
    B0 := B0
    Bu := B0 * t.BuOverB0
    Bv := B0 * t.BvOverB0
    F := signalMode1 p x
    C2second := signalMode2 p (4 * x)
  }

/-- The raw quadratic projection bracket is `B₀` times the scaled bracket used
by `chiGamma2`. -/
theorem quadraticProjection_bracket_eq_scaled
    (p : PhysicalParams) (x beta : ℝ) :
    (quadraticProjectionData p x beta).bracket =
      p.mobilityB0 beta *
        (4 * signalMode2 p (4 * x) +
          (mobilityScaledTaylor p beta).BuOverB0 * signalMode1 p x +
          (mobilityScaledTaylor p beta).BvOverB0 * signalMode1 p x ^ 2) := by
  unfold quadraticProjectionData QuadraticProjectionData.bracket
    QuadraticProjectionData.linearMobility
  ring

/-- Physical threshold times the independently projected quadratic bracket is
the product `χ* Γ_{2n₀}` consumed by the center-jet equation. -/
theorem chiGamma2_eq_projected
    (p : PhysicalParams) (x beta : ℝ)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset)
    (hnu : 0 < p.nu) (hgamma : 0 < p.gamma)
    (hx : x ≠ 0) (hsig : p.SignalEquilibrium) :
    p.chiStar x beta * x * (quadraticProjectionData p x beta).bracket =
      chiGamma2 p x beta := by
  rw [quadraticProjection_bracket_eq_scaled]
  have hchi := chiStar_mul_B0_eq_scaled p x beta hu hw hnu hgamma hx hsig
  unfold chiGamma2
  rw [← hchi]
  ring

/-- Constant quadratic signal correction. -/
noncomputable def cubicE
    (p : PhysicalParams) (jet : QuadraticJetData) : ℝ :=
  signalMode1 p 0 * jet.a0 + signalMode2 p 0

/-- Critical first-order signal coefficient. -/
noncomputable def cubicF (p : PhysicalParams) (x : ℝ) : ℝ :=
  signalMode1 p x

/-- Second-harmonic quadratic signal correction. -/
noncomputable def cubicG
    (p : PhysicalParams) (x : ℝ) (jet : QuadraticJetData) : ℝ :=
  signalMode1 p (4 * x) * jet.a2 + signalMode2 p (4 * x)

/-- Critical cubic signal correction. -/
noncomputable def cubicH
    (p : PhysicalParams) (x : ℝ) (jet : QuadraticJetData) : ℝ :=
  2 * signalMode2 p x * (2 * jet.a0 + jet.a2) +
    3 * signalMode3 p x

/-- Manuscript mobility aggregate `Q`, divided by `B₀`. -/
noncomputable def cubicQOverB0
    (p : PhysicalParams) (x beta : ℝ) : ℝ :=
  let t := mobilityScaledTaylor p beta
  let F := cubicF p x
  t.BuuOverB0 + t.BuvOverB0 * F + t.BvvOverB0 * F ^ 2

/-- Manuscript aggregate `R`, divided by `B₀`. -/
noncomputable def cubicROverB0
    (p : PhysicalParams) (x beta : ℝ) (jet : QuadraticJetData) : ℝ :=
  let t := mobilityScaledTaylor p beta
  t.BuOverB0 * jet.a0 + t.BvOverB0 * cubicE p jet +
    cubicQOverB0 p x beta / 2

/-- Manuscript aggregate `S`, divided by `B₀`. -/
noncomputable def cubicSOverB0
    (p : PhysicalParams) (x beta : ℝ) (jet : QuadraticJetData) : ℝ :=
  let t := mobilityScaledTaylor p beta
  t.BuOverB0 * jet.a2 + t.BvOverB0 * cubicG p x jet +
    cubicQOverB0 p x beta / 2

/-- The physical product `χ* Γ_n₀^(3)` after canceling the common `B₀`. -/
noncomputable def chiGamma3
    (p : PhysicalParams) (x beta : ℝ) (jet : QuadraticJetData) : ℝ :=
  let t := mobilityScaledTaylor p beta
  let F := cubicF p x
  x * chiStarTimesB0 p x *
    (cubicH p x jet + (t.BuOverB0 + t.BvOverB0 * F) * cubicG p x jet +
      F * (cubicROverB0 p x beta jet - cubicSOverB0 p x beta jet / 2))

/-- Corrected physical cubic coefficient assembled independently of any final
polynomial numerator. -/
noncomputable def betaCoefficient
    (p : PhysicalParams) (x beta : ℝ) (jet : QuadraticJetData) : ℝ :=
  let t := mobilityScaledTaylor p beta
  t.bAsecond / 2 * (4 * jet.a0 + 2 * jet.a2) -
    chiGamma3 p x beta jet + 3 * t.bAthird / 4

/-- All cubic intermediates collected for downstream algebra. -/
noncomputable def cubicData
    (p : PhysicalParams) (x beta : ℝ) (jet : QuadraticJetData) : CubicData where
  E := cubicE p jet
  F := cubicF p x
  G := cubicG p x jet
  H := cubicH p x jet
  QOverB0 := cubicQOverB0 p x beta
  ROverB0 := cubicROverB0 p x beta jet
  SOverB0 := cubicSOverB0 p x beta jet
  chiGamma3 := chiGamma3 p x beta jet
  betaCoeff := betaCoefficient p x beta jet

/-- Non-minimal coefficient interface with the logistic constant mode. -/
noncomputable def logisticBetaCoefficient
    (p : PhysicalParams) (x beta : ℝ) : ℝ :=
  betaCoefficient p x beta (logisticQuadraticJet p x beta)

/-- Fixed-mass minimal coefficient interface with zero constant mode. -/
noncomputable def fixedMassBetaCoefficient
    (p : PhysicalParams) (x beta : ℝ) : ℝ :=
  betaCoefficient p x beta (fixedMassQuadraticJet p x beta)

/-- Raw four-channel cubic projection data reconstructed from `B₀` and the
scaled coefficient interface. -/
noncomputable def rawCubicProjectionData
    (p : PhysicalParams) (x beta : ℝ)
    (jet : QuadraticJetData) : RawCubicProjectionData :=
  let t := mobilityScaledTaylor p beta
  let B0 := p.mobilityB0 beta
  {
    B0 := B0
    Bu := B0 * t.BuOverB0
    Bv := B0 * t.BvOverB0
    Buu := B0 * t.BuuOverB0
    Buv := B0 * t.BuvOverB0
    Bvv := B0 * t.BvvOverB0
    a0 := jet.a0
    a2 := jet.a2
    E := cubicE p jet
    F := cubicF p x
    G := cubicG p x jet
    H := cubicH p x jet
  }

/-- The raw four-channel critical bracket is `B₀` times the scaled bracket in
the all-parameter assembly. -/
theorem rawCubic_criticalBracket_eq_scaled
    (p : PhysicalParams) (x beta : ℝ) (jet : QuadraticJetData) :
    (rawCubicProjectionData p x beta jet).criticalBracket =
      p.mobilityB0 beta *
        (cubicH p x jet +
          ((mobilityScaledTaylor p beta).BuOverB0 +
            (mobilityScaledTaylor p beta).BvOverB0 * cubicF p x) *
              cubicG p x jet +
          cubicF p x *
            (cubicROverB0 p x beta jet -
              cubicSOverB0 p x beta jet / 2)) := by
  unfold rawCubicProjectionData RawCubicProjectionData.criticalBracket
    RawCubicProjectionData.linearMobility
    RawCubicProjectionData.R RawCubicProjectionData.S RawCubicProjectionData.Q
    cubicROverB0 cubicSOverB0 cubicQOverB0
  ring

/-- The physical threshold applied to the independently assembled raw cubic
projection equals `chiGamma3`. -/
theorem chiGamma3_eq_projected
    (p : PhysicalParams) (x beta : ℝ) (jet : QuadraticJetData)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset)
    (hnu : 0 < p.nu) (hgamma : 0 < p.gamma)
    (hx : x ≠ 0) (hsig : p.SignalEquilibrium) :
    p.chiStar x beta * x *
        (rawCubicProjectionData p x beta jet).criticalBracket =
      chiGamma3 p x beta jet := by
  rw [rawCubic_criticalBracket_eq_scaled]
  have hchi := chiStar_mul_B0_eq_scaled p x beta hu hw hnu hgamma hx hsig
  unfold chiGamma3
  rw [← hchi]
  ring

/-- The corrected reduced coefficient is the independently projected logistic
channel minus the projected chemotactic channel. -/
theorem betaCoefficient_eq_projected
    (p : PhysicalParams) (x beta : ℝ) (jet : QuadraticJetData)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset)
    (hnu : 0 < p.nu) (hgamma : 0 < p.gamma)
    (hx : x ≠ 0) (hsig : p.SignalEquilibrium) :
    (mobilityScaledTaylor p beta).bAsecond / 2 *
        (4 * jet.a0 + 2 * jet.a2) -
      p.chiStar x beta * x *
        (rawCubicProjectionData p x beta jet).criticalBracket +
      3 * (mobilityScaledTaylor p beta).bAthird / 4 =
        betaCoefficient p x beta jet := by
  rw [chiGamma3_eq_projected p x beta jet hu hw hnu hgamma hx hsig]
  unfold betaCoefficient
  rfl

/-- Manuscript-facing physical assembly: the logistic Taylor coefficients are
derived from the primitive reaction and the chemotactic channel from the raw
four-term flux projection. -/
theorem betaCoefficient_eq_physical_projected
    (p : PhysicalParams) (x beta : ℝ) (jet : QuadraticJetData)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset)
    (hnu : 0 < p.nu) (hgamma : 0 < p.gamma)
    (hx : x ≠ 0) (hlog : p.LogisticEquilibrium)
    (hsig : p.SignalEquilibrium) :
    p.b * (rawTaylorData p 0).Asecond / 2 *
        (4 * jet.a0 + 2 * jet.a2) -
      p.chiStar x beta * x *
        (rawCubicProjectionData p x beta jet).criticalBracket +
      3 * (p.b * (rawTaylorData p 0).Athird) / 4 =
        betaCoefficient p x beta jet := by
  rw [bAsecond_eq_scaled p hu hlog, bAthird_eq_scaled p hu hlog]
  exact betaCoefficient_eq_projected
    p x beta jet hu hw hnu hgamma hx hsig

/-- Non-minimal manuscript coefficient assembled from the physical Taylor and
raw projection data. -/
theorem logisticBetaCoefficient_eq_physical_projected
    (p : PhysicalParams) (x beta : ℝ)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset)
    (hnu : 0 < p.nu) (hgamma : 0 < p.gamma)
    (hx : x ≠ 0) (hlog : p.LogisticEquilibrium)
    (hsig : p.SignalEquilibrium) :
    p.b * (rawTaylorData p 0).Asecond / 2 *
        (4 * (logisticQuadraticJet p x beta).a0 +
          2 * (logisticQuadraticJet p x beta).a2) -
      p.chiStar x beta * x *
        (rawCubicProjectionData p x beta
          (logisticQuadraticJet p x beta)).criticalBracket +
      3 * (p.b * (rawTaylorData p 0).Athird) / 4 =
        logisticBetaCoefficient p x beta := by
  exact betaCoefficient_eq_physical_projected p x beta
    (logisticQuadraticJet p x beta) hu hw hnu hgamma hx hlog hsig

/-- In the fixed-mass model both logistic channels vanish, so the corrected
coefficient is the negative projected chemotactic product. -/
theorem fixedMassBetaCoefficient_eq_neg_chiGamma3
    (p : PhysicalParams) (x beta : ℝ)
    (hfix : p.FixedMassAdmissible) :
    fixedMassBetaCoefficient p x beta =
      -chiGamma3 p x beta (fixedMassQuadraticJet p x beta) := by
  rcases hfix with ⟨ha, _hb, _hm, _hg, _hnu, _hmu, _hu, _hv, _hsig⟩
  unfold fixedMassBetaCoefficient betaCoefficient mobilityScaledTaylor
  simp [ha]

end ChemotaxisBifurcation
