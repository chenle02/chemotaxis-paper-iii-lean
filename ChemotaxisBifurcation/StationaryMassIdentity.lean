module
public import ChemotaxisBifurcation.IntervalMoments
public import ChemotaxisBifurcation.NoAtomLimit
public import ChemotaxisBifurcation.MinimalFlux
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Logistic mass balance from the stationary equation

Integrating the derivative of the total population flux derives the mass
identity consumed by the interval-moment bounds. Only the differential
equation, regularity and endpoint data are inputs; the identity is not.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.StationaryMassIdentity

open Real Set MeasureTheory
open scoped NNReal

noncomputable section

/-- Integrate the conservative stationary equation with zero total flux. -/
theorem logistic_mass_identity {L a b alpha : ℝ} (hL : 0 ≤ L) (halpha : 0 ≤ alpha)
    {u F : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 L))
    (hF : ContinuousOn F (Icc 0 L))
    (heq : ∀ x ∈ Ioo 0 L,
      HasDerivAt F (b * u x ^ (1 + alpha) - a * u x) x)
    (h0 : F 0 = 0) (h1 : F L = 0) :
    a * (∫ x in (0 : ℝ)..L, u x) =
      b * (∫ x in (0 : ℝ)..L, u x ^ (1 + alpha)) := by
  have hp : ContinuousOn (fun x => u x ^ (1 + alpha)) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr (by linarith)
  have hiU : IntervalIntegrable u volume 0 L := hu.intervalIntegrable_of_Icc hL
  have hiP : IntervalIntegrable (fun x => u x ^ (1 + alpha)) volume 0 L :=
    hp.intervalIntegrable_of_Icc hL
  have hi := (hiP.const_mul b).sub (hiU.const_mul a)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL hF heq hi
  rw [intervalIntegral.integral_sub (hiP.const_mul b) (hiU.const_mul a),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    h0, h1] at h
  linarith

/-- Derive the total-flux equation from the two displayed derivative terms.
The chemotactic flux is supplied as `J`; no specific power law is assumed. -/
theorem logistic_mass_identity_of_stationary {L a b alpha : ℝ}
    (hL : 0 ≤ L) (halpha : 0 ≤ alpha) {u du ddu J dJ : ℝ → ℝ}
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ContinuousOn du (Icc 0 L))
    (hJ : ContinuousOn J (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hdJ : ∀ x ∈ Ioo 0 L, HasDerivAt J (dJ x) x)
    (heq : ∀ x ∈ Ioo 0 L, ddu x - dJ x + a * u x - b * u x ^ (1 + alpha) = 0)
    (hdu0 : du 0 = 0) (hduL : du L = 0) (hJ0 : J 0 = 0) (hJL : J L = 0) :
    a * (∫ x in (0 : ℝ)..L, u x) =
      b * (∫ x in (0 : ℝ)..L, u x ^ (1 + alpha)) := by
  apply logistic_mass_identity hL halpha hu (hdu.sub hJ)
  · intro x hx
    convert (hddu x hx).sub (hdJ x hx) using 1
    linarith [heq x hx]
  · simp [hdu0, hJ0]
  · simp [hduL, hJL]

/-- Classical population-equation data. The constitutive flux is the literal
chemotactic flux; all derivative witnesses and Neumann data are explicit.
Neither mass balance nor any moment estimate is a field. The signal equation
is unnecessary for the conclusions in this module. -/
structure ClassicalProfile (L a b alpha chi m beta : ℝ) where
  u : ℝ → ℝ
  v : ℝ → ℝ
  du : ℝ → ℝ
  ddu : ℝ → ℝ
  dv : ℝ → ℝ
  dJ : ℝ → ℝ
  continuous_u : ContinuousOn u (Icc 0 L)
  continuous_du : ContinuousOn du (Icc 0 L)
  continuous_flux : ContinuousOn (MinimalFlux.flux chi m beta u v dv) (Icc 0 L)
  derivative_u : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x
  derivative_du : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x
  derivative_v : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x
  derivative_flux : ∀ x ∈ Ioo 0 L,
    HasDerivAt (MinimalFlux.flux chi m beta u v dv) (dJ x) x
  stationary : ∀ x ∈ Ioo 0 L,
    ddu x - dJ x + a * u x - b * u x ^ (1 + alpha) = 0
  neumann_u_left : du 0 = 0
  neumann_u_right : du L = 0
  neumann_v_left : dv 0 = 0
  neumann_v_right : dv L = 0

namespace ClassicalProfile

variable {L a b alpha chi m beta : ℝ}

theorem mass_balance (p : ClassicalProfile L a b alpha chi m beta)
    (hL : 0 ≤ L) (halpha : 0 ≤ alpha) :
    a * (∫ x in (0 : ℝ)..L, p.u x) =
      b * (∫ x in (0 : ℝ)..L, p.u x ^ (1 + alpha)) :=
  logistic_mass_identity_of_stationary hL halpha p.continuous_u p.continuous_du
    p.continuous_flux p.derivative_du p.derivative_flux p.stationary
    p.neumann_u_left p.neumann_u_right
    (by simp [MinimalFlux.flux, p.neumann_v_left])
    (by simp [MinimalFlux.flux, p.neumann_v_right])

/-- The full interval-moment deduction with the mass-identity assumption
discharged by the original population equation. -/
theorem interval_bounds (p : ClassicalProfile L a b alpha chi m beta)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, p.u x ≠ p.u y) :
    (∃ x₀ ∈ Icc 0 L, IsMinOn p.u (Icc 0 L) x₀ ∧ 0 < p.u x₀ ∧
        p.u x₀ < (a / b) ^ (1 / alpha)) ∧
      (∃ x₁ ∈ Icc 0 L, IsMaxOn p.u (Icc 0 L) x₁ ∧ (a / b) ^ (1 / alpha) < p.u x₁) ∧
      ∫ x in (0 : ℝ)..L, p.u x < L * (a / b) ^ (1 / alpha) ∧
      ∫ x in (0 : ℝ)..L, p.u x ^ (1 + alpha) <
        L * ((a / b) ^ (1 / alpha)) ^ (1 + alpha) :=
  IntervalMoments.logistic_interval_bounds a b alpha L p.u ha hb halpha hL
    p.continuous_u hpos hnonconst (p.mass_balance hL.le halpha.le)

/-- The manuscript's quantitative local-mass inequality for a given classical
stationary profile; no separate mass-identity premise remains. -/
theorem window_mass_bounds (p : ClassicalProfile L a b alpha chi m beta)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, p.u x ≠ p.u y)
    (xstar delta : ℝ) (hdelta : 0 < delta) :
    (∫ x in NoDiracMass.window L xstar delta, p.u x) ≤
        (2 * delta) ^ (alpha / (1 + alpha)) *
          (∫ x in (0 : ℝ)..L, p.u x ^ (1 + alpha)) ^ (1 / (1 + alpha)) ∧
      (∫ x in NoDiracMass.window L xstar delta, p.u x) <
        (a / b) ^ (1 / alpha) * L ^ (1 / (1 + alpha)) *
          (2 * delta) ^ (alpha / (1 + alpha)) :=
  NoDiracMass.window_mass_bounds a b alpha L p.u ha hb halpha hL p.continuous_u
    hpos hnonconst (p.mass_balance hL.le halpha.le) xstar delta hdelta

/-- Actual population profiles obey the concave lower-moment estimate;
the higher logistic moment is derived from their equation, not assumed. -/
theorem power_moment (p : ClassicalProfile L a b alpha chi m beta)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, p.u x ≠ p.u y)
    (gamma : ℝ) (hg0 : 0 < gamma) (hg1 : gamma ≤ 1+alpha) :
    ∫ x in (0 : ℝ)..L, p.u x^gamma ≤ L*((a/b)^(1/alpha))^gamma := by
  exact IntervalMoments.logistic_power_integral_le L ((a/b)^(1/alpha)) alpha gamma p.u
    hL halpha (Real.rpow_pos_of_pos (div_pos ha hb) _).le hg0 hg1 p.continuous_u
    (fun x hx => (hpos x hx).le) (p.interval_bounds ha hb halpha hL hpos hnonconst).2.2.2.le

end ClassicalProfile

/-- Uniform local-mass decay for classical profiles, with mass balance
derived rather than supplied independently for each index. -/
theorem window_mass_decay_of_classical_profiles {ι : Type*} {L a b alpha : ℝ}
    {chi m beta : ι → ℝ}
    (p : ∀ i, ClassicalProfile L a b alpha (chi i) (m i) (beta i))
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hpos : ∀ i, ∀ x ∈ Icc 0 L, 0 < (p i).u x)
    (hnonconst : ∀ i, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, (p i).u x ≠ (p i).u y) :
    TendstoUniformly (fun delta (ix : ι × ℝ) =>
      ∫ x in NoDiracMass.window L ix.2 delta, (p ix.1).u x) (fun _ => 0)
      (nhdsWithin 0 (Ioi 0)) :=
  NoDiracMass.window_mass_tendstoUniformly a b alpha L (fun i => (p i).u)
    ha hb halpha hL (fun i => (p i).continuous_u) hpos hnonconst
    (fun i => (p i).mass_balance hL.le halpha.le)

/-- Weak limits have no atoms for a family of actual classical population
equations. Sensitivity and mobility parameters may vary with the index;
the logistic parameters and domain are common. Weak convergence is an
ordinary premise, not a compactness or subsequence-existence assertion. -/
theorem no_atoms_of_classical_profiles {ι : Type*} {L a b alpha : ℝ}
    {chi m beta : ι → ℝ}
    (p : ∀ i, ClassicalProfile L a b alpha (chi i) (m i) (beta i))
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hpos : ∀ i, ∀ x ∈ Icc 0 L, 0 < (p i).u x)
    (hnonconst : ∀ i, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, (p i).u x ≠ (p i).u y)
    {l : Filter ι} [l.NeBot]
    {mu : FiniteMeasure (EndpointConcentration.ClosedInterval L)}
    (hlim : Filter.Tendsto (fun i => IntervalConcentration.densityFiniteMeasure L
      (p i).u hL.le (p i).continuous_u (fun x hx => (hpos i x hx).le)) l
      (nhds mu)) (x : EndpointConcentration.ClosedInterval L) :
    (mu : Measure (EndpointConcentration.ClosedInterval L)) {x} = 0 :=
  NoAtomLimit.densityFiniteMeasure_singleton_eq_zero a b alpha L (fun i => (p i).u)
    ha hb halpha hL (fun i => (p i).continuous_u) hpos hnonconst
    (fun i => (p i).mass_balance hL.le halpha.le) hlim x

/-- No subsequence of classical stationary densities can converge to a
nonzero Dirac mass, including at either endpoint. -/
theorem no_dirac_subsequence_of_classical_profiles {L a b alpha : ℝ}
    {chi m beta : ℕ → ℝ}
    (p : ∀ i, ClassicalProfile L a b alpha (chi i) (m i) (beta i))
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hpos : ∀ i, ∀ x ∈ Icc 0 L, 0 < (p i).u x)
    (hnonconst : ∀ i, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, (p i).u x ≠ (p i).u y)
    (phi : ℕ → ℕ) (c : ℝ≥0) (hc : 0 < c) (xstar : EndpointConcentration.ClosedInterval L) :
    ¬ Filter.Tendsto (fun k => IntervalConcentration.densityFiniteMeasure L
      (p (phi k)).u hL.le (p (phi k)).continuous_u
      (fun x hx => (hpos (phi k) x hx).le)) Filter.atTop
      (nhds (c • (MeasureTheory.diracProba xstar).toFiniteMeasure)) :=
  NoAtomLimit.not_subseq_tendsto_smul_dirac a b alpha L (fun i => (p i).u)
    ha hb halpha hL (fun i => (p i).continuous_u) hpos hnonconst
    (fun i => (p i).mass_balance hL.le halpha.le) phi c hc xstar

end
end ChemotaxisBifurcation.StationaryMassIdentity
