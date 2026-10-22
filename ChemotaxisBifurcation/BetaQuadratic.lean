module
public import ChemotaxisBifurcation.CubicAssembly

@[expose] public section

/-!
# Quadratic dependence on the sensitivity exponent

The coefficient in this module is the assembled current coefficient with an
arbitrary constant quadratic graph mode `a0`.  The non-minimal and fixed-mass
models are separate specializations of this common calculation.
-/

namespace ChemotaxisBifurcation

noncomputable section

/-- The assembled coefficient with a constant-mode value supplied explicitly. -/
noncomputable def betaCoefficientAtA0
    (p : PhysicalParams) (x a0 beta : ℝ) : ℝ :=
  betaCoefficient p x beta (quadraticJetData p x beta a0)

/-- Slope of the corrected second-harmonic graph coefficient in `beta`. -/
noncomputable def secondModeA2Slope
    (p : PhysicalParams) (x : ℝ) : ℝ :=
  x * chiStarTimesB0 p x * cubicF p x ^ 2 /
    (p.signalOffset * sigma2 p x)

/-- Slope of the second-harmonic signal correction in `beta`. -/
noncomputable def cubicGSlope
    (p : PhysicalParams) (x : ℝ) : ℝ :=
  signalMode1 p (4 * x) * secondModeA2Slope p x

/-- Explicit leading coefficient of the quadratic in `beta`. -/
noncomputable def betaLeading
    (p : PhysicalParams) (x : ℝ) : ℝ :=
  -x * chiStarTimesB0 p x *
    (-cubicF p x * cubicGSlope p x / (2 * p.signalOffset) +
      cubicF p x ^ 3 / (8 * p.signalOffset ^ 2))

/-- Constant coefficient, evaluated from the independently assembled formula. -/
noncomputable def betaConstantAtA0
    (p : PhysicalParams) (x a0 : ℝ) : ℝ :=
  betaCoefficientAtA0 p x a0 0

/-- Linear coefficient, recovered after subtracting the explicit leading and
constant coefficients at `beta=1`. -/
noncomputable def betaLinearAtA0
    (p : PhysicalParams) (x a0 : ℝ) : ℝ :=
  betaCoefficientAtA0 p x a0 1 - betaConstantAtA0 p x a0 -
    betaLeading p x

/-- Abstract coefficient data after the affine quadratic-jet quantities have
been separated from `beta`. -/
structure BetaAssemblyData where
  W : ℝ
  bA2 : ℝ
  bA3 : ℝ
  xChi : ℝ
  F : ℝ
  E : ℝ
  h0 : ℝ
  h1 : ℝ
  bu : ℝ
  a0 : ℝ
  a20 : ℝ
  a21 : ℝ
  g0 : ℝ
  g1 : ℝ
  q0 : ℝ
  q1 : ℝ
  q2 : ℝ

namespace BetaAssemblyData

def a2 (d : BetaAssemblyData) (beta : ℝ) : ℝ := d.a20 + d.a21 * beta
def G (d : BetaAssemblyData) (beta : ℝ) : ℝ := d.g0 + d.g1 * beta
def H (d : BetaAssemblyData) (beta : ℝ) : ℝ := d.h0 + d.h1 * beta
def Q (d : BetaAssemblyData) (beta : ℝ) : ℝ :=
  d.q0 + d.q1 * beta + d.q2 * beta ^ 2
def R (d : BetaAssemblyData) (beta : ℝ) : ℝ :=
  d.bu * d.a0 - beta / d.W * d.E + d.Q beta / 2
def S (d : BetaAssemblyData) (beta : ℝ) : ℝ :=
  d.bu * d.a2 beta - beta / d.W * d.G beta + d.Q beta / 2
def bracket (d : BetaAssemblyData) (beta : ℝ) : ℝ :=
  d.H beta + (d.bu - beta / d.W * d.F) * d.G beta +
    d.F * (d.R beta - d.S beta / 2)
def coeff (d : BetaAssemblyData) (beta : ℝ) : ℝ :=
  d.bA2 / 2 * (4 * d.a0 + 2 * d.a2 beta) -
    d.xChi * d.bracket beta + 3 * d.bA3 / 4
def leading (d : BetaAssemblyData) : ℝ :=
  -d.xChi * (-d.F * d.g1 / (2 * d.W) + d.F * d.q2 / 4)
def constant (d : BetaAssemblyData) : ℝ := d.coeff 0
def linear (d : BetaAssemblyData) : ℝ := d.coeff 1 - d.constant - d.leading

theorem coeff_quadratic (d : BetaAssemblyData) (beta : ℝ) (hW : d.W ≠ 0) :
    d.coeff beta = d.leading * beta ^ 2 + d.linear * beta + d.constant := by
  unfold linear constant
  unfold coeff leading bracket R S Q H G a2
  field_simp [hW]
  ring

end BetaAssemblyData

/-- Concrete current coefficient data presented to the abstract quadratic
collector. -/
noncomputable def betaAssemblyData
    (p : PhysicalParams) (x a0 : ℝ) : BetaAssemblyData where
  W := p.signalOffset
  bA2 := (mobilityScaledTaylor p 0).bAsecond
  bA3 := (mobilityScaledTaylor p 0).bAthird
  xChi := x * chiStarTimesB0 p x
  F := cubicF p x
  E := cubicE p (quadraticJetData p x 0 a0)
  h0 := cubicH p x (quadraticJetData p x 0 a0)
  h1 := 2 * signalMode2 p x * secondModeA2Slope p x
  bu := (mobilityScaledTaylor p 0).BuOverB0
  a0 := a0
  a20 := secondModeA2 p x 0
  a21 := secondModeA2Slope p x
  g0 := cubicG p x (quadraticJetData p x 0 a0)
  g1 := cubicGSlope p x
  q0 := (mobilityScaledTaylor p 0).BuuOverB0
  q1 := -(p.m * cubicF p x) / (p.uStar * p.signalOffset) +
    cubicF p x ^ 2 / (2 * p.signalOffset ^ 2)
  q2 := cubicF p x ^ 2 / (2 * p.signalOffset ^ 2)

/-- The corrected second-harmonic coefficient is affine in `beta`. -/
theorem secondModeA2_eq_affine
    (p : PhysicalParams) (x beta : ℝ)
    (hW : p.signalOffset ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    secondModeA2 p x beta = secondModeA2 p x 0 +
      secondModeA2Slope p x * beta := by
  simp only [secondModeA2, secondModeA2Slope, chiGamma2, cubicF,
    mobilityScaledTaylor]
  field_simp [hW, hsigma]
  ring

/-- The second-harmonic signal correction is affine in `beta`. -/
theorem cubicG_eq_affine
    (p : PhysicalParams) (x a0 beta : ℝ)
    (hW : p.signalOffset ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    cubicG p x (quadraticJetData p x beta a0) =
      cubicG p x (quadraticJetData p x 0 a0) + cubicGSlope p x * beta := by
  unfold cubicG cubicGSlope quadraticJetData
  rw [secondModeA2_eq_affine p x beta hW hsigma]
  ring

theorem cubicE_eq_at_zero
    (p : PhysicalParams) (x a0 beta : ℝ) :
    cubicE p (quadraticJetData p x beta a0) =
      cubicE p (quadraticJetData p x 0 a0) := by
  rfl

theorem cubicH_eq_affine
    (p : PhysicalParams) (x a0 beta : ℝ)
    (hW : p.signalOffset ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    cubicH p x (quadraticJetData p x beta a0) =
      cubicH p x (quadraticJetData p x 0 a0) +
        2 * signalMode2 p x * secondModeA2Slope p x * beta := by
  unfold cubicH quadraticJetData
  rw [secondModeA2_eq_affine p x beta hW hsigma]
  ring

set_option maxHeartbeats 800000 in
theorem betaCoefficientAtA0_eq_assembly
    (p : PhysicalParams) (x a0 beta : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hsigma : sigma2 p x ≠ 0) :
    betaCoefficientAtA0 p x a0 beta =
      (betaAssemblyData p x a0).coeff beta := by
  unfold betaCoefficientAtA0 betaCoefficient chiGamma3
    cubicROverB0 cubicSOverB0 cubicQOverB0
  rw [cubicE_eq_at_zero p x a0 beta,
    cubicH_eq_affine p x a0 beta hW hsigma]
  rw [cubicG_eq_affine p x a0 beta hW hsigma]
  unfold quadraticJetData
  rw [secondModeA2_eq_affine p x beta hW hsigma]
  simp only [betaAssemblyData, BetaAssemblyData.coeff,
    BetaAssemblyData.bracket, BetaAssemblyData.R, BetaAssemblyData.S,
    BetaAssemblyData.Q, BetaAssemblyData.H, BetaAssemblyData.G,
    BetaAssemblyData.a2, cubicE, cubicG, cubicH, quadraticJetData,
    mobilityScaledTaylor]
  field_simp [hU, hW]
  ring

theorem betaAssemblyData_leading
    (p : PhysicalParams) (x a0 : ℝ) :
    (betaAssemblyData p x a0).leading = betaLeading p x := by
  unfold betaAssemblyData BetaAssemblyData.leading betaLeading
  ring

theorem betaAssemblyData_constant
    (p : PhysicalParams) (x a0 : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hsigma : sigma2 p x ≠ 0) :
    (betaAssemblyData p x a0).constant = betaConstantAtA0 p x a0 := by
  unfold BetaAssemblyData.constant betaConstantAtA0
  exact (betaCoefficientAtA0_eq_assembly p x a0 0 hU hW hsigma).symm

theorem betaAssemblyData_linear
    (p : PhysicalParams) (x a0 : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hsigma : sigma2 p x ≠ 0) :
    (betaAssemblyData p x a0).linear = betaLinearAtA0 p x a0 := by
  unfold BetaAssemblyData.linear betaLinearAtA0
  rw [betaAssemblyData_constant p x a0 hU hW hsigma,
    betaAssemblyData_leading]
  rw [← betaCoefficientAtA0_eq_assembly p x a0 1 hU hW hsigma]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 10000 in
/-- The current assembled coefficient is exactly quadratic in `beta`, for an
arbitrary constant graph mode. -/
theorem betaCoefficientAtA0_quadratic
    (p : PhysicalParams) (x a0 beta : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hmux : p.mu + x ≠ 0)
    (hmu4 : p.mu + 4 * x ≠ 0)
    (hC : (mobilityScaledTaylor p 0).Cprime ≠ 0)
    (hx : x ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    betaCoefficientAtA0 p x a0 beta =
      betaLeading p x * beta ^ 2 + betaLinearAtA0 p x a0 * beta +
        betaConstantAtA0 p x a0 := by
  rw [betaCoefficientAtA0_eq_assembly p x a0 beta hU hW hsigma,
    BetaAssemblyData.coeff_quadratic (betaAssemblyData p x a0) beta hW,
    betaAssemblyData_leading,
    betaAssemblyData_linear p x a0 hU hW hsigma,
    betaAssemblyData_constant p x a0 hU hW hsigma]

/-- Non-minimal specialization of the quadratic identity. -/
theorem logisticBetaCoefficient_quadratic
    (p : PhysicalParams) (x beta : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hmux : p.mu + x ≠ 0)
    (hmu4 : p.mu + 4 * x ≠ 0)
    (hC : (mobilityScaledTaylor p 0).Cprime ≠ 0)
    (hx : x ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    logisticBetaCoefficient p x beta =
      betaLeading p x * beta ^ 2 +
        betaLinearAtA0 p x (logisticA0 p) * beta +
        betaConstantAtA0 p x (logisticA0 p) := by
  exact betaCoefficientAtA0_quadratic p x (logisticA0 p) beta
    hU hW hmu hmux hmu4 hC hx hsigma

/-- Fixed-mass specialization of the quadratic identity. -/
theorem fixedMassBetaCoefficient_quadratic
    (p : PhysicalParams) (x beta : ℝ)
    (hU : p.uStar ≠ 0) (hW : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hmux : p.mu + x ≠ 0)
    (hmu4 : p.mu + 4 * x ≠ 0)
    (hC : (mobilityScaledTaylor p 0).Cprime ≠ 0)
    (hx : x ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    fixedMassBetaCoefficient p x beta =
      betaLeading p x * beta ^ 2 +
        betaLinearAtA0 p x fixedMassA0 * beta +
        betaConstantAtA0 p x fixedMassA0 := by
  exact betaCoefficientAtA0_quadratic p x fixedMassA0 beta
    hU hW hmu hmux hmu4 hC hx hsigma

/-- The second-mode graph slope is negative under the spectral sign and
positive primitive factors. -/
theorem secondModeA2Slope_neg
    (p : PhysicalParams) (x : ℝ)
    (hx : 0 < x) (hchi : 0 < chiStarTimesB0 p x)
    (hF : 0 < cubicF p x) (hW : 0 < p.signalOffset)
    (hsigma : sigma2 p x < 0) :
    secondModeA2Slope p x < 0 := by
  unfold secondModeA2Slope
  have hnum : 0 < x * chiStarTimesB0 p x * cubicF p x ^ 2 := by positivity
  have hden : p.signalOffset * sigma2 p x < 0 :=
    mul_neg_of_pos_of_neg hW hsigma
  exact div_neg_of_pos_of_neg hnum hden

/-- The second-harmonic signal slope is negative. -/
theorem cubicGSlope_neg
    (p : PhysicalParams) (x : ℝ)
    (hF4 : 0 < signalMode1 p (4 * x))
    (ha2 : secondModeA2Slope p x < 0) :
    cubicGSlope p x < 0 := by
  unfold cubicGSlope
  exact mul_neg_of_pos_of_neg hF4 ha2

/-- The leading quadratic coefficient is strictly negative. -/
theorem betaLeading_neg
    (p : PhysicalParams) (x : ℝ)
    (hx : 0 < x) (hchi : 0 < chiStarTimesB0 p x)
    (hF : 0 < cubicF p x) (hW : 0 < p.signalOffset)
    (hG : cubicGSlope p x < 0) :
    betaLeading p x < 0 := by
  have hfirst :
      0 < -cubicF p x * cubicGSlope p x / (2 * p.signalOffset) := by
    have hnum : 0 < -cubicF p x * cubicGSlope p x :=
      mul_pos_of_neg_of_neg (neg_lt_zero.mpr hF) hG
    have hden : 0 < 2 * p.signalOffset := by positivity
    exact div_pos hnum hden
  have hsecond :
      0 < cubicF p x ^ 3 / (8 * p.signalOffset ^ 2) := by
    have hnum : 0 < cubicF p x ^ 3 := by positivity
    have hden : 0 < 8 * p.signalOffset ^ 2 := by positivity
    exact div_pos hnum hden
  unfold betaLeading
  have hbracket :
      0 < -cubicF p x * cubicGSlope p x / (2 * p.signalOffset) +
        cubicF p x ^ 3 / (8 * p.signalOffset ^ 2) := by linarith
  have hpref : 0 < x * chiStarTimesB0 p x := mul_pos hx hchi
  nlinarith

/-- The leading coefficient in the exact closed form displayed in Equation
2.25, using `x * chiStarTimesB0` for `(u*)^m Π`. -/
theorem betaLeading_eq_manuscript
    (p : PhysicalParams) (x : ℝ)
    (hW : p.signalOffset ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    betaLeading p x =
      cubicF p x ^ 3 * (x * chiStarTimesB0 p x) *
        (4 * signalMode1 p (4 * x) * (x * chiStarTimesB0 p x) -
          sigma2 p x) /
        (8 * sigma2 p x * p.signalOffset ^ 2) := by
  unfold betaLeading cubicGSlope secondModeA2Slope
  field_simp [hW, hsigma]
  ring

/-- The scaled manuscript factor `(u*)^m Π` is exactly
`x * chiStarTimesB0`. -/
theorem uPow_mul_PiScaled
    (p : PhysicalParams) (x : ℝ) (hu : 0 < p.uStar) :
    p.uStar ^ p.m * PiScaled p x = x * chiStarTimesB0 p x := by
  unfold PiScaled
  have hupow : p.uStar ^ p.m ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
  field_simp [hupow]

/-- Equation 2.25 in the paper's literal `(u*)^m Π` notation. -/
theorem betaLeading_eq_manuscript_Pi
    (p : PhysicalParams) (x : ℝ) (hu : 0 < p.uStar)
    (hW : p.signalOffset ≠ 0) (hsigma : sigma2 p x ≠ 0) :
    betaLeading p x =
      cubicF p x ^ 3 * (p.uStar ^ p.m * PiScaled p x) *
        (4 * signalMode1 p (4 * x) * (p.uStar ^ p.m * PiScaled p x) -
          sigma2 p x) /
        (8 * sigma2 p x * p.signalOffset ^ 2) := by
  rw [uPow_mul_PiScaled p x hu]
  exact betaLeading_eq_manuscript p x hW hsigma

end

end ChemotaxisBifurcation
