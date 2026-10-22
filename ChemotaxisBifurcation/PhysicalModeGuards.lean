module
public import ChemotaxisBifurcation.LinearRegime
public import ChemotaxisBifurcation.PhysicalSemidiscrete
public import ChemotaxisBifurcation.RationalCoefficient

@[expose] public section

/-!
# Physical positivity and strict-critical-mode denominator guards

The strict-minimizer hypothesis is stated in actual Neumann mode indices.
The doubled-mode comparison then gives the negative second-harmonic growth
rate used by the coefficient and beta-regime proofs.
-/

namespace ChemotaxisBifurcation.PhysicalModeGuards

structure PositiveModeParameters (p : PhysicalParams) : Prop where
  mu_pos : 0 < p.mu
  gamma_pos : 0 < p.gamma
  nu_pos : 0 < p.nu
  u_pos : 0 < p.uStar
  v_pos : 0 < p.vStar
  slope_nonneg : 0 ≤ p.logisticSlope

theorem logistic_positive_parameters (p : PhysicalParams) (hp : p.LogisticAdmissible) :
    PositiveModeParameters p := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  exact ⟨hmu, hgamma, hnu, hu, hv, mul_nonneg ha.le halpha.le⟩

theorem fixedMass_positive_parameters (p : PhysicalParams) (hp : p.FixedMassAdmissible) :
    PositiveModeParameters p := by
  rcases hp with ⟨ha, hb, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  refine ⟨hmu, hgamma, hnu, hu, hv, ?_⟩
  simp [PhysicalParams.logisticSlope, ha]

theorem signalOffset_pos (p : PhysicalParams) (hp : PositiveModeParameters p) :
    0 < p.signalOffset := by
  unfold PhysicalParams.signalOffset
  linarith [hp.v_pos]

theorem scaledCprime_pos (p : PhysicalParams) (hp : PositiveModeParameters p) :
    0 < (mobilityScaledTaylor p 0).Cprime := by
  exact div_pos (mul_pos (mul_pos hp.mu_pos hp.gamma_pos) hp.v_pos) hp.u_pos

theorem thresholdK_pos (p : PhysicalParams) (beta : ℝ) (hp : PositiveModeParameters p) :
    0 < p.thresholdK beta := by
  unfold PhysicalParams.thresholdK PhysicalParams.mobilityB0 PhysicalParams.signalC1Physical
  exact mul_pos
    (div_pos (Real.rpow_pos_of_pos hp.u_pos _)
      (Real.rpow_pos_of_pos (signalOffset_pos p hp) _))
    (mul_pos (mul_pos hp.nu_pos hp.gamma_pos) (Real.rpow_pos_of_pos hp.u_pos _))

theorem signalMode1_pos (p : PhysicalParams) (x : ℝ)
    (hp : PositiveModeParameters p) (hx : 0 < x) : 0 < signalMode1 p x :=
  div_pos (scaledCprime_pos p hp) (add_pos hp.mu_pos hx)

theorem chiStarTimesB0_pos (p : PhysicalParams) (x : ℝ)
    (hp : PositiveModeParameters p) (hx : 0 < x) : 0 < chiStarTimesB0 p x := by
  exact div_pos
    (mul_pos (add_pos_of_pos_of_nonneg hx hp.slope_nonneg) (add_pos hp.mu_pos hx))
    (mul_pos (scaledCprime_pos p hp) hx)

theorem alphaN0_pos (p : PhysicalParams) (x beta : ℝ)
    (hp : PositiveModeParameters p) (hx : 0 < x) : 0 < p.alphaN0 x beta :=
  div_pos (mul_pos (thresholdK_pos p beta hp) hx) (add_pos hp.mu_pos hx)

theorem chiStar_doubled_difference (p : PhysicalParams) (x beta : ℝ)
    (hK : p.thresholdK beta ≠ 0) (hx : x ≠ 0) :
    p.chiStar (4 * x) beta - p.chiStar x beta =
      3 * (4 * x ^ 2 - p.logisticSlope * p.mu) / (4 * p.thresholdK beta * x) := by
  unfold PhysicalParams.chiStar
  field_simp [hK, hx] <;> ring

theorem delta_neg_of_doubled_comparison (p : PhysicalParams) (x beta : ℝ)
    (hp : PositiveModeParameters p) (hx : 0 < x)
    (hcmp : p.chiStar x beta < p.chiStar (4 * x) beta) :
    p.logisticSlope * p.mu - 4 * x ^ 2 < 0 := by
  have hK := thresholdK_pos p beta hp
  have hd : 0 < 4 * p.thresholdK beta * x := by positivity
  have hdiff := sub_pos.mpr hcmp
  rw [chiStar_doubled_difference p x beta hK.ne' hx.ne'] at hdiff
  have hnum := (lt_div_iff₀ hd).mp hdiff
  nlinarith

theorem sigma2_eq_delta (p : PhysicalParams) (x : ℝ) (hq : p.mu + 4 * x ≠ 0) :
    sigma2 p x = 3 * (p.logisticSlope * p.mu - 4 * x ^ 2) / (p.mu + 4 * x) := by
  exact RationalCoefficient.RationalData.sigma2_eq
    (RationalCoefficient.physicalRationalData p 0) hq

theorem sigma2_neg_of_delta_neg (p : PhysicalParams) (x : ℝ)
    (hp : PositiveModeParameters p) (hx : 0 < x)
    (hdelta : p.logisticSlope * p.mu - 4 * x ^ 2 < 0) : sigma2 p x < 0 := by
  have hq : 0 < p.mu + 4 * x := by nlinarith [hp.mu_pos]
  rw [sigma2_eq_delta p x hq.ne']
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hdelta) hq

def StrictCriticalMode (p : PhysicalParams) (d : ModeData) (beta : ℝ) : Prop :=
  0 < d.L ∧ 0 < d.n0 ∧ ∀ n : ℕ, 0 < n → n ≠ d.n0 →
    p.chiStar d.eigenvalue beta < p.chiStar (Semidiscrete.continuumLam d.L n) beta

theorem mode_eigenvalue_pos (d : ModeData) (hL : 0 < d.L) (hn : 0 < d.n0) :
    0 < d.eigenvalue := by
  unfold ModeData.eigenvalue
  positivity

theorem doubled_mode_eigenvalue (d : ModeData) :
    Semidiscrete.continuumLam d.L (2 * d.n0) = 4 * d.eigenvalue := by
  simp only [Semidiscrete.continuumLam, ModeData.eigenvalue, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem strictCriticalMode_doubled_comparison (p : PhysicalParams) (d : ModeData) (beta : ℝ)
    (hc : StrictCriticalMode p d beta) :
    p.chiStar d.eigenvalue beta < p.chiStar (4 * d.eigenvalue) beta := by
  have hn : 0 < d.n0 := hc.2.1
  have h := hc.2.2 (2 * d.n0) (by omega) (by omega)
  rw [doubled_mode_eigenvalue d] at h
  exact h

theorem strictCriticalMode_delta_neg (p : PhysicalParams) (d : ModeData) (beta : ℝ)
    (hp : PositiveModeParameters p) (hc : StrictCriticalMode p d beta) :
    p.logisticSlope * p.mu - 4 * d.eigenvalue ^ 2 < 0 :=
  delta_neg_of_doubled_comparison p d.eigenvalue beta hp
    (mode_eigenvalue_pos d hc.1 hc.2.1) (strictCriticalMode_doubled_comparison p d beta hc)

theorem strictCriticalMode_sigma2_neg (p : PhysicalParams) (d : ModeData) (beta : ℝ)
    (hp : PositiveModeParameters p) (hc : StrictCriticalMode p d beta) :
    sigma2 p d.eigenvalue < 0 :=
  sigma2_neg_of_delta_neg p d.eigenvalue hp (mode_eigenvalue_pos d hc.1 hc.2.1)
    (strictCriticalMode_delta_neg p d beta hp hc)

theorem physical_Pi_eq_scaled (p : PhysicalParams) (x beta : ℝ)
    (hp : PositiveModeParameters p) (hx : 0 < x) (hsig : p.SignalEquilibrium) :
    p.chiStar x beta * x / p.signalOffset ^ beta = PiScaled p x := by
  have hw := signalOffset_pos p hp
  have hchi := chiStar_mul_B0_eq_scaled p x beta hp.u_pos hw hp.nu_pos hp.gamma_pos hx.ne' hsig
  have huPow : p.uStar ^ p.m ≠ 0 := (Real.rpow_pos_of_pos hp.u_pos _).ne'
  have hwPow : p.signalOffset ^ beta ≠ 0 := (Real.rpow_pos_of_pos hw _).ne'
  unfold PiScaled
  rw [← hchi]
  unfold PhysicalParams.mobilityB0
  field_simp [huPow, hwPow] <;> ring

end ChemotaxisBifurcation.PhysicalModeGuards
