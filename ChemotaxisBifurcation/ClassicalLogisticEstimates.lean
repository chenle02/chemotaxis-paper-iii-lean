module
public import ChemotaxisBifurcation.StationaryMassIdentity
public import ChemotaxisBifurcation.SpikeEstimatesLogistic
public import ChemotaxisBifurcation.SignalTesting
public import ChemotaxisBifurcation.LogisticGronwall

@[expose] public section

/-!
# Classical-solution logistic estimates with derived moment inputs

The population profile supplies the original stationary equation, literal
chemotactic flux and Neumann data. The signal data below supply the second
stationary equation. Mass balance, strict moment bounds and the signal gradient
estimate are derived before the existing energy and C1 consumers are applied.
Existence, compactness and the higher Schauder estimate are not claimed.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.ClassicalLogisticEstimates

open Real Set MeasureTheory StationaryMassIdentity

noncomputable section

/-- Classical data for the second stationary equation of a population profile. -/
structure SignalData {L a b alpha chi m beta : ℝ}
    (p : ClassicalProfile L a b alpha chi m beta) (mu nu gamma : ℝ) where
  ddv : ℝ → ℝ
  continuous_v : ContinuousOn p.v (Icc 0 L)
  nonnegative_v : ∀ x ∈ Icc 0 L, 0 ≤ p.v x
  continuous_dv : ContinuousOn p.dv (Icc 0 L)
  derivative_dv : ∀ x ∈ Ioo 0 L, HasDerivAt p.dv (ddv x) x
  stationary : ∀ x ∈ Ioo 0 L, ddv x - mu * p.v x + nu * p.u x ^ gamma = 0

/-- The explicit C1 envelope; it has no sensitivity, beta or mu argument. -/
def c1Envelope (L a b alpha gamma nu Xbar m : ℝ) : ℝ :=
  let uStar := (a / b) ^ (1 / alpha)
  let B := uStar + sqrt (2 * SpikeEstimates.energyConstant Xbar a b alpha gamma nu L m uStar * L)
  max B (Xbar * B ^ m * (2 * nu * L * uStar ^ gamma) + 2 * a * L * uStar)

/-- The full classical C1 deduction without separately assumed mass,
mean or power-moment bounds. -/
theorem c1_bound {L a b alpha gamma mu nu chi Xbar m beta : ℝ}
    (p : ClassicalProfile L a b alpha chi m beta) (s : SignalData p mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1 + alpha) (hm0 : 0 < m)
    (hm2 : 2 * m < alpha + 2) (hbeta : 0 ≤ beta) (hmu : 0 ≤ mu) (hnu : 0 ≤ nu)
    (hchi : |chi| ≤ Xbar)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, p.u x ≠ p.u y) :
    ∀ x ∈ Icc 0 L,
      |p.u x| ≤ c1Envelope L a b alpha gamma nu Xbar m ∧
      |p.du x| ≤ c1Envelope L a b alpha gamma nu Xbar m := by
  have hI := p.interval_bounds ha hb halpha hL hpos hnonconst
  have huStar : 0 ≤ (a / b) ^ (1 / alpha) :=
    (Real.rpow_pos_of_pos (div_pos ha hb) _).le
  have h := SpikeEstimates.logistic_C1_chain L a b alpha gamma mu nu chi Xbar m beta
    ((a / b) ^ (1 / alpha)) p.u p.v p.du p.ddu p.dv s.ddv p.dJ
    hL ha hb halpha hgamma0 hgamma1 hm0 hm2 hbeta hmu hnu huStar hchi
    p.continuous_u hpos p.derivative_u p.continuous_du p.derivative_du
    s.continuous_v s.nonnegative_v s.continuous_dv s.derivative_dv s.stationary
    p.continuous_flux p.derivative_flux p.stationary
    p.neumann_u_left p.neumann_u_right p.neumann_v_left p.neumann_v_right
    (p.mass_balance hL.le halpha.le) hI.2.2.1.le hI.2.2.2.le
  intro x hx
  rw [abs_of_pos (hpos x hx)]
  exact h x hx

/-- The quantitative signal W2q estimate, with actual norms and with the
population moment, testing, Holder and Minkowski premises all discharged.
The inputs are the two classical stationary equations and positive profiles. -/
theorem w2q_bound {L a b alpha gamma mu nu chi m beta q : ℝ}
    (p : ClassicalProfile L a b alpha chi m beta) (s : SignalData p mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hq : 1 < q)
    (hgq : gamma * q = 1 + alpha)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, p.u x ≠ p.u y)
    (hvpos : ∀ x ∈ Icc 0 L, 0 < p.v x)
    (hddv : ContinuousOn s.ddv (Icc 0 L)) :
    (∫ x in (0 : ℝ)..L, |p.v x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |p.dv x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |s.ddv x| ^ q) ^ (1 / q) ≤
      L ^ (1 / q) * ((a / b) ^ (1 / alpha)) ^ gamma *
        (nu / mu + 2 * nu + 2 * nu * L) := by
  have hI := p.interval_bounds ha hb halpha hL hpos hnonconst
  exact SpikeEstimates.logistic_W2q_actual L mu nu gamma alpha ((a / b) ^ (1 / alpha)) q
    p.u p.v p.dv s.ddv hL hmu hnu halpha hgamma
    (Real.rpow_nonneg (div_nonneg ha.le hb.le) _) hq hgq
    p.continuous_u (fun x hx => (hpos x hx).le) s.continuous_v hvpos
    s.continuous_dv hddv p.derivative_v s.derivative_dv s.stationary
    p.neumann_v_left p.neumann_v_right hI.2.2.2.le

/-- Full v2 mobility range C1 envelope from the logarithmic Gronwall proof.
Its arguments exclude the individual sensitivity, mu and beta. -/
def gronwallC1Envelope (L a b alpha gamma nu Xbar m : ℝ) : ℝ :=
  let uStar := (a / b) ^ (1 / alpha)
  let B := SpikeEstimates.gronwallPopulationBound L a gamma nu Xbar m uStar
  max B (Xbar * B ^ m * (2 * nu * L * uStar ^ gamma) + 2 * a * L * uStar)

/-- The given classical stationary system obeys a uniform C1 bound for
every `1 ≤ m ≤ alpha+2`, with no independently assumed mass or moment bounds.
The higher Holder/Schauder assertion is not part of this theorem. -/
theorem c1_gronwall_bound {L a b alpha gamma mu nu chi Xbar m beta : ℝ}
    (p : ClassicalProfile L a b alpha chi m beta) (s : SignalData p mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1 + alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha + 2) (hbeta : 0 ≤ beta)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hchi : |chi| ≤ Xbar)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, p.u x ≠ p.u y) :
    ∀ x ∈ Icc 0 L,
      |p.u x| ≤ gronwallC1Envelope L a b alpha gamma nu Xbar m ∧
      |p.du x| ≤ gronwallC1Envelope L a b alpha gamma nu Xbar m := by
  have hI := p.interval_bounds ha hb halpha hL hpos hnonconst
  exact SpikeEstimates.logistic_C1_gronwall_chain L a b alpha gamma mu nu chi Xbar m beta
    ((a / b) ^ (1 / alpha)) p.u p.v p.du p.ddu p.dv s.ddv p.dJ
    hL ha hb halpha hgamma0 hgamma1 hm hm1 hbeta hmu hnu
    (Real.rpow_nonneg (div_nonneg ha.le hb.le) _) hchi
    p.continuous_u hpos p.derivative_u p.continuous_du p.derivative_du
    s.continuous_v s.nonnegative_v s.continuous_dv s.derivative_dv s.stationary
    p.continuous_flux p.derivative_flux p.stationary
    p.neumann_u_left p.neumann_u_right p.neumann_v_left p.neumann_v_right
    (p.mass_balance hL.le halpha.le) hI.2.2.1.le hI.2.2.2.le

end
end ChemotaxisBifurcation.ClassicalLogisticEstimates
