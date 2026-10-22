module
public import Mathlib

@[expose] public section

/-!
# Paper III finite coefficient interface

This module fixes the shared data model for the finite algebraic verification.
It carries the equilibrium values `uStar` and `vStar` explicitly, so the same
coefficient interface applies to the non-minimal logistic model and the
fixed-mass minimal model.  In particular, the minimal model is never obtained
by evaluating `(a / b)^(1 / alpha)` at `a = b = 0`.

The critical eigenvalue `x` and sensitivity exponent `beta` are function
arguments.  This keeps the all-parameter polynomial development independent of
the later mode wrapper `x = (n₀ π / L)²`.
-/

namespace ChemotaxisBifurcation

/-- Physical parameters and a positive constant equilibrium candidate.

This is data only.  Positivity and the two equilibrium relations are supplied
through named predicates in theorem hypotheses. -/
structure PhysicalParams where
  a : ℝ
  b : ℝ
  alpha : ℝ
  m : ℝ
  gamma : ℝ
  nu : ℝ
  mu : ℝ
  uStar : ℝ
  vStar : ℝ

namespace PhysicalParams

/-- `1 + v*`, the positive signal offset in the sensitivity. -/
def signalOffset (p : PhysicalParams) : ℝ := 1 + p.vStar

/-- The product `a α` used in the modal threshold. -/
def logisticSlope (p : PhysicalParams) : ℝ := p.a * p.alpha

/-- Logistic equilibrium relation `a = b (u*)^α`. -/
def LogisticEquilibrium (p : PhysicalParams) : Prop :=
  p.a = p.b * p.uStar ^ p.alpha

/-- Signal equilibrium relation `μ v* = ν (u*)^γ`. -/
def SignalEquilibrium (p : PhysicalParams) : Prop :=
  p.mu * p.vStar = p.nu * p.uStar ^ p.gamma

/-- The two constant-equilibrium relations used by the non-minimal model. -/
def EquilibriumRelations (p : PhysicalParams) : Prop :=
  p.LogisticEquilibrium ∧ p.SignalEquilibrium

/-- Primitive positivity assumptions for the non-minimal logistic model. -/
def LogisticAdmissible (p : PhysicalParams) : Prop :=
  0 < p.a ∧ 0 < p.b ∧ 0 < p.alpha ∧ 0 < p.m ∧
    0 < p.gamma ∧ 0 < p.nu ∧ 0 < p.mu ∧
    0 < p.uStar ∧ 0 < p.vStar ∧ p.EquilibriumRelations

/-- Primitive assumptions for the fixed-mass minimal model.

The population equilibrium `uStar` is free and positive.  The signal
equilibrium remains enforced, while the logistic parameters are exactly zero.
-/
def FixedMassAdmissible (p : PhysicalParams) : Prop :=
  p.a = 0 ∧ p.b = 0 ∧ 0 < p.m ∧ 0 < p.gamma ∧
    0 < p.nu ∧ 0 < p.mu ∧ 0 < p.uStar ∧ 0 < p.vStar ∧
    p.SignalEquilibrium

/-- The physical mobility constant `B₀=(u*)^m/(1+v*)^β`. -/
noncomputable def mobilityB0 (p : PhysicalParams) (beta : ℝ) : ℝ :=
  p.uStar ^ p.m / p.signalOffset ^ beta

/-- The physical first signal coefficient `C'=νγ(u*)^(γ-1)`. -/
noncomputable def signalC1Physical (p : PhysicalParams) : ℝ :=
  p.nu * p.gamma * p.uStar ^ (p.gamma - 1)

/-- The positive threshold prefactor `K=B₀ C'`. -/
noncomputable def thresholdK (p : PhysicalParams) (beta : ℝ) : ℝ :=
  p.mobilityB0 beta * p.signalC1Physical

/-- The physical modal threshold at an eigenvalue `x`.

The denominator conditions and positivity are theorem hypotheses, not hidden in
this totalized field expression. -/
noncomputable def chiStar (p : PhysicalParams) (x beta : ℝ) : ℝ :=
  (x + p.logisticSlope) * (p.mu + x) / (p.thresholdK beta * x)

/-- The crossing coefficient `α_n₀` written directly at eigenvalue `x`. -/
noncomputable def alphaN0 (p : PhysicalParams) (x beta : ℝ) : ℝ :=
  p.thresholdK beta * x / (p.mu + x)

end PhysicalParams

/-- Natural-mode data used only to connect coefficient algebra to a domain. -/
structure ModeData where
  L : ℝ
  n0 : ℕ

namespace ModeData

/-- Neumann eigenvalue `(n₀ π / L)²`. -/
noncomputable def eigenvalue (d : ModeData) : ℝ :=
  (((d.n0 : ℝ) * Real.pi) / d.L) ^ 2

end ModeData

/-- One evaluation point for the coefficient chain. -/
structure CoefficientPoint where
  physical : PhysicalParams
  x : ℝ
  beta : ℝ

/-- Taylor data before any mobility scaling.

The next proof wave derives these fields from the primitive physical functions;
downstream projection lemmas consume the structure without re-expanding them.
-/
structure RawTaylorData where
  B0 : ℝ
  Bu : ℝ
  Bv : ℝ
  Buu : ℝ
  Buv : ℝ
  Bvv : ℝ
  Aprime : ℝ
  Asecond : ℝ
  Athird : ℝ
  Cprime : ℝ
  Csecond : ℝ
  Cthird : ℝ

/-- Rational data after dividing mobility derivatives by the positive `B₀`.

This is a symbolic scaling valid for arbitrary physical parameters.  It is not
the all-ones normalized example from the manuscript.  Under the equilibrium
relations, the signal and logistic coefficients also have the rational forms
stored here. -/
structure MobilityScaledTaylorData where
  BuOverB0 : ℝ
  BvOverB0 : ℝ
  BuuOverB0 : ℝ
  BuvOverB0 : ℝ
  BvvOverB0 : ℝ
  bAsecond : ℝ
  bAthird : ℝ
  Cprime : ℝ
  Csecond : ℝ
  Cthird : ℝ

/-- Output of the corrected quadratic center-jet calculation.

`chiGamma2` is the product `χ* Γ_{2n₀}`.  Storing the product avoids
reintroducing the canceled mobility power in later field algebra. -/
structure QuadraticJetData where
  sigma2 : ℝ
  chiGamma2 : ℝ
  a0 : ℝ
  a2 : ℝ

/-- Mobility-scaled cubic aggregates used in the critical projection.

`QOverB0`, `ROverB0`, and `SOverB0` are the manuscript `Q`, `R`, and `S`
divided by `B₀`.  `chiGamma3` is the physical product `χ* Γ_n₀^(3)`.
-/
structure CubicData where
  E : ℝ
  F : ℝ
  G : ℝ
  H : ℝ
  QOverB0 : ℝ
  ROverB0 : ℝ
  SOverB0 : ℝ
  chiGamma3 : ℝ
  betaCoeff : ℝ

/-- Rational mobility-scaled Taylor data at exponent `beta`.

The physical-to-scaled bridge is a proof target of `Taylor.lean`; this
definition is the common algebraic interface used by the general polynomial
calculations. -/
noncomputable def mobilityScaledTaylor
    (p : PhysicalParams) (beta : ℝ) : MobilityScaledTaylorData where
  BuOverB0 := p.m / p.uStar
  BvOverB0 := -beta / p.signalOffset
  BuuOverB0 := p.m * (p.m - 1) / (2 * p.uStar ^ 2)
  BuvOverB0 := -(p.m * beta) / (p.uStar * p.signalOffset)
  BvvOverB0 := beta * (beta + 1) / (2 * p.signalOffset ^ 2)
  bAsecond := p.a * p.alpha * (1 + p.alpha) / (2 * p.uStar)
  bAthird :=
    p.a * p.alpha * (1 + p.alpha) * (p.alpha - 1) /
      (6 * p.uStar ^ 2)
  Cprime := p.mu * p.gamma * p.vStar / p.uStar
  Csecond :=
    p.mu * p.gamma * (p.gamma - 1) * p.vStar /
      (2 * p.uStar ^ 2)
  Cthird :=
    p.mu * p.gamma * (p.gamma - 1) * (p.gamma - 2) * p.vStar /
      (6 * p.uStar ^ 3)

/-- `χ* B₀`, expressed through the rational signal coefficient `C'`.

This scaled threshold removes the common real-power factor while retaining all
physical parameters. -/
noncomputable def chiStarTimesB0 (p : PhysicalParams) (x : ℝ) : ℝ :=
  let t := mobilityScaledTaylor p 0
  (x + p.logisticSlope) * (p.mu + x) / (t.Cprime * x)

/-- Manuscript `Π = χ* λ/(1+v*)^β`, expressed rationally using equilibrium
data.  It differs from `χ* B₀ λ` by the factor `(u*)^m`. -/
noncomputable def PiScaled (p : PhysicalParams) (x : ℝ) : ℝ :=
  chiStarTimesB0 p x * x / p.uStar ^ p.m

end ChemotaxisBifurcation
