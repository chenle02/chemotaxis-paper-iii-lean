module
public import ChemotaxisBifurcation.Taylor

@[expose] public section

/-!
# Corrected quadratic center-jet data

The definitions in this module expose the rational coefficient interface early
so the all-parameter polynomial proof can proceed in parallel.  The projection
and invariance-residual theorems that justify these definitions are separate
proof obligations.
-/

namespace ChemotaxisBifurcation

/-- Degree-two scalar residual for one stable graph mode. -/
def quadraticJetResidual
    (delta source a1 a2 a3 amplitude eta : ℝ) : ℝ :=
  delta * (a1 * amplitude ^ 2 + a2 * eta * amplitude + a3 * eta ^ 2) -
    source * amplitude ^ 2

/-- A vanishing quadratic invariance residual forces all three coefficients.

This is the conditional finite core of the center-graph calculation; it does
not assert existence of the graph. -/
theorem coefficients_of_quadratic_jet_residual
    (delta source a1 a2 a3 : ℝ) (hdelta : delta ≠ 0)
    (hres : ∀ amplitude eta : ℝ,
      quadraticJetResidual delta source a1 a2 a3 amplitude eta = 0) :
    a1 = source / delta ∧ a2 = 0 ∧ a3 = 0 := by
  have h10 := hres 1 0
  have h01 := hres 0 1
  have h11 := hres 1 1
  simp [quadraticJetResidual] at h10 h01 h11
  have ha1mul : a1 * delta = source := by
    nlinarith [h10]
  have ha1 : a1 = source / delta := (eq_div_iff hdelta).2 ha1mul
  have ha3 : a3 = 0 := h01.resolve_left hdelta
  have hda2 : delta * a2 = 0 := by
    rw [ha3] at h11
    nlinarith [h10, h11]
  have ha2 : a2 = 0 := (mul_eq_zero.mp hda2).resolve_left hdelta
  exact ⟨ha1, ha2, ha3⟩

/-- First-order elliptic signal coefficient at eigenvalue `x`. -/
noncomputable def signalMode1
    (p : PhysicalParams) (x : ℝ) : ℝ :=
  (mobilityScaledTaylor p 0).Cprime / (p.mu + x)

/-- Factorial-normalized second-order elliptic signal coefficient. -/
noncomputable def signalMode2
    (p : PhysicalParams) (x : ℝ) : ℝ :=
  (mobilityScaledTaylor p 0).Csecond / (2 * (p.mu + x))

/-- Factorial-normalized third-order elliptic signal coefficient. -/
noncomputable def signalMode3
    (p : PhysicalParams) (x : ℝ) : ℝ :=
  (mobilityScaledTaylor p 0).Cthird / (4 * (p.mu + x))

/-- The second-harmonic growth rate evaluated at the critical sensitivity. -/
noncomputable def sigma2 (p : PhysicalParams) (x : ℝ) : ℝ :=
  -4 * x - p.logisticSlope +
    4 * (x + p.logisticSlope) * (p.mu + x) / (p.mu + 4 * x)

/-- The physical product `χ* Γ_{2n₀}`, with the common `B₀` canceled. -/
noncomputable def chiGamma2
    (p : PhysicalParams) (x beta : ℝ) : ℝ :=
  let t := mobilityScaledTaylor p beta
  let F := signalMode1 p x
  x * chiStarTimesB0 p x *
    (4 * signalMode2 p (4 * x) + t.BuOverB0 * F + t.BvOverB0 * F ^ 2)

/-- Constant quadratic graph coefficient in the non-minimal logistic model. -/
noncomputable def logisticA0 (p : PhysicalParams) : ℝ :=
  -(mobilityScaledTaylor p 0).bAsecond / (2 * p.logisticSlope)

/-- Constant quadratic graph coefficient on the fixed-mass minimal space. -/
def fixedMassA0 : ℝ := 0

/-- Corrected second-harmonic graph coefficient.

The numerator contains the mandatory logistic source `b A'' / 2`. -/
noncomputable def secondModeA2
    (p : PhysicalParams) (x beta : ℝ) : ℝ :=
  ((mobilityScaledTaylor p beta).bAsecond / 2 - chiGamma2 p x beta) /
    sigma2 p x

/-- Generic quadratic jet with an explicit constant-mode choice. -/
noncomputable def quadraticJetData
    (p : PhysicalParams) (x beta a0 : ℝ) : QuadraticJetData where
  sigma2 := sigma2 p x
  chiGamma2 := chiGamma2 p x beta
  a0 := a0
  a2 := secondModeA2 p x beta

/-- Non-minimal quadratic jet.  Applicability requires the named logistic
admissibility and nonzero-denominator hypotheses in its later theorem wrapper.
-/
noncomputable def logisticQuadraticJet
    (p : PhysicalParams) (x beta : ℝ) : QuadraticJetData :=
  quadraticJetData p x beta (logisticA0 p)

/-- Fixed-mass minimal quadratic jet.  The zero constant mode is imposed by
the phase space rather than obtained as a logistic limit. -/
noncomputable def fixedMassQuadraticJet
    (p : PhysicalParams) (x beta : ℝ) : QuadraticJetData :=
  quadraticJetData p x beta fixedMassA0

/-- The non-minimal constant-mode definition solves the current scalar
invariance equation. -/
theorem logisticA0_residual
    (p : PhysicalParams) (hd : p.logisticSlope ≠ 0) :
    -p.logisticSlope * logisticA0 p -
      (mobilityScaledTaylor p 0).bAsecond / 2 = 0 := by
  unfold logisticA0
  field_simp [hd]
  ring

/-- Physical form of the non-minimal constant-mode invariance equation. -/
theorem logisticA0_physical_residual
    (p : PhysicalParams) (hu : 0 < p.uStar)
    (hlog : p.LogisticEquilibrium) (hd : p.logisticSlope ≠ 0) :
    -p.logisticSlope * logisticA0 p -
      p.b * (rawTaylorData p 0).Asecond / 2 = 0 := by
  rw [bAsecond_eq_scaled p hu hlog]
  exact logisticA0_residual p hd

/-- The corrected second-mode definition solves the current invariance
equation and visibly retains the `b A'' / 2` source. -/
theorem secondModeA2_residual
    (p : PhysicalParams) (x beta : ℝ) (hsigma : sigma2 p x ≠ 0) :
    sigma2 p x * secondModeA2 p x beta -
      (mobilityScaledTaylor p beta).bAsecond / 2 +
      chiGamma2 p x beta = 0 := by
  unfold secondModeA2
  field_simp [hsigma]
  ring

/-- Physical form of the corrected second-mode invariance equation. -/
theorem secondModeA2_physical_residual
    (p : PhysicalParams) (x beta : ℝ)
    (hu : 0 < p.uStar) (hlog : p.LogisticEquilibrium)
    (hsigma : sigma2 p x ≠ 0) :
    sigma2 p x * secondModeA2 p x beta -
      p.b * (rawTaylorData p 0).Asecond / 2 +
      chiGamma2 p x beta = 0 := by
  rw [bAsecond_eq_scaled p hu hlog]
  exact secondModeA2_residual p x beta hsigma

/-- The fixed-mass constant mode is zero by definition of the phase-space
wrapper, rather than by a singular logistic specialization. -/
theorem fixedMassA0_eq_zero : fixedMassA0 = 0 := rfl

end ChemotaxisBifurcation
