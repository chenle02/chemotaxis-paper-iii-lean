module
public import ChemotaxisBifurcation.ClassicalLogisticEstimates

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalMinimalEstimates
open Real Set MeasureTheory StationaryMassIdentity
noncomputable section

/-- The literal minimal population equation supplies its first integral. -/
theorem flux_identity {L alpha chi m beta : ℝ}
    (p : ClassicalProfile L 0 0 alpha chi m beta) :
    ∀ x ∈ Icc 0 L, p.du x = chi * (p.u x ^ m / (1+p.v x)^beta) * p.dv x := by
  apply MinimalFlux.minimal_flux_identity L chi m beta p.u p.v p.du p.ddu p.dv p.dJ
    p.continuous_du p.derivative_du p.continuous_flux p.derivative_flux
    _ p.neumann_u_left p.neumann_v_left
  intro x hx
  simpa using p.stationary x hx

/-- Fixed-mass Jensen supplies every concave moment of the actual profile. -/
theorem power_moment {L alpha chi m beta uStar r : ℝ}
    (p : ClassicalProfile L 0 0 alpha chi m beta) (hL : 0 < L)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hmass : ∫ x in (0 : ℝ)..L, p.u x = L*uStar) :
    ∫ x in (0 : ℝ)..L, p.u x^r ≤ L*uStar^r :=
  IntervalMoments.minimal_power_integral_le L uStar r p.u hL hr0 hr1
    p.continuous_u (fun x hx => (hpos x hx).le) hmass

def populationEnvelope (L uStar gamma nu Xbar m : ℝ) : ℝ :=
  (uStar+1)*exp ((Xbar*(2*nu*L*uStar^gamma))*(L*uStar^(m-1)))

/-- Uniform classical C1 estimates throughout the current minimal mobility
range, including m=2. The prescribed mass is a hypothesis of the model;
first-integral, moment, signal-gradient and Gronwall bounds are derived. -/
theorem c1_gronwall_bound {L alpha gamma mu nu chi Xbar m beta uStar : ℝ}
    (p : ClassicalProfile L 0 0 alpha chi m beta)
    (s : ClassicalLogisticEstimates.SignalData p mu nu gamma)
    (hL : 0 < L) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (hm : 1 ≤ m) (hm2 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hchi : |chi| ≤ Xbar)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hmass : ∫ x in (0 : ℝ)..L, p.u x = L*uStar) :
    ∀ x ∈ Icc 0 L,
      |p.u x| ≤ populationEnvelope L uStar gamma nu Xbar m ∧
      |p.du x| ≤ Xbar*(populationEnvelope L uStar gamma nu Xbar m)^m*
        (2*nu*L*uStar^gamma) := by
  have hu0 : ∀ x ∈ Icc 0 L, 0 ≤ p.u x := fun x hx => (hpos x hx).le
  have hX : 0 ≤ Xbar := (abs_nonneg chi).trans hchi
  have huStar : 0 ≤ uStar := by
    have hh := intervalIntegral.integral_nonneg (μ := volume) hL.le hu0
    rw [hmass] at hh
    nlinarith
  have hK : 0 ≤ 2*nu*L*uStar^gamma := by positivity
  have hmoment := power_moment p hL (show 0 ≤ m-1 by linarith)
    (show m-1 ≤ 1 by linarith) hpos hmass
  have hsource := power_moment p hL hg0 hg1 hpos hmass
  have hgrad := SpikeEstimates.signal_gradient_le_two L mu nu gamma p.u p.v p.dv s.ddv
    hL.le hmu hnu hg0 p.continuous_u hu0 s.continuous_v s.nonnegative_v
    s.continuous_dv s.derivative_dv s.stationary p.neumann_v_left p.neumann_v_right
  have hvx : ∀ x ∈ Icc 0 L, |p.dv x| ≤ 2*nu*L*uStar^gamma := by
    intro x hx
    calc |p.dv x| ≤ 2*nu*(∫ y in (0 : ℝ)..L, p.u y^gamma) := hgrad x hx
      _ ≤ 2*nu*(L*uStar^gamma) := mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by ring
  have hf : ∀ x ∈ Icc 0 L, |p.du x| ≤ Xbar*(p.u x)^m*(2*nu*L*uStar^gamma) := by
    intro x hx
    have hh := SpikeEstimates.flux_abs_le chi m beta (2*nu*L*uStar^gamma)
      (p.u x) (p.v x) (p.du x) (p.dv x) (hu0 x hx) (s.nonnegative_v x hx)
      hbeta (flux_identity p x hx) (hvx x hx)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hchi (Real.rpow_nonneg (hu0 x hx) _)) hK)
  have hB := SpikeEstimates.sup_le_of_derivative_power_bound L uStar
    (Xbar*(2*nu*L*uStar^gamma)) 0 m (L*uStar^(m-1)) p.u p.du hL
    (mul_nonneg hX hK) le_rfl hm p.continuous_u hpos p.derivative_u
    (fun x hx => by have hh := hf x (Ioo_subset_Icc_self hx); nlinarith)
    hmass.le hmoment
  have hbound : ∀ x ∈ Icc 0 L, p.u x ≤ populationEnvelope L uStar gamma nu Xbar m := by
    simpa only [populationEnvelope, zero_mul, add_zero] using hB
  intro x hx
  refine ⟨by simpa only [abs_of_pos (hpos x hx)] using hbound x hx, (hf x hx).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hu0 x hx) (hbound x hx) (by linarith)) hX) hK

/-- Actual prescribed-mass classical solutions satisfy the strict interval
bounds, with no separately supplied extremum or moment identity. -/
theorem interval_bounds {L alpha chi m beta uStar : ℝ}
    (p : ClassicalProfile L 0 0 alpha chi m beta) (hL : 0 < L)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, p.u x ≠ p.u y)
    (hmass : ∫ x in (0 : ℝ)..L, p.u x = L*uStar) :
    (∃ x₀ ∈ Icc 0 L, IsMinOn p.u (Icc 0 L) x₀ ∧ 0 < p.u x₀ ∧ p.u x₀ < uStar) ∧
      (∃ x₁ ∈ Icc 0 L, IsMaxOn p.u (Icc 0 L) x₁ ∧ uStar < p.u x₁) ∧
      L*uStar^2 < ∫ x in (0 : ℝ)..L, p.u x^2 :=
  IntervalMoments.minimal_interval_bounds L uStar p.u hL p.continuous_u hpos hnonconst hmass

/-- Actual signal sup/L1 component bound with the manuscript's exact constant. -/
theorem signal_sobolev_bound {L alpha chi m beta gamma mu nu : ℝ}
    (p : ClassicalProfile L 0 0 alpha chi m beta)
    (s : ClassicalLogisticEstimates.SignalData p mu nu gamma)
    (hL : 0 < L) (hmu : 0 < mu) (hnu : 0 ≤ nu) (hg : 0 ≤ gamma)
    (hu : ∀ x ∈ Icc 0 L, 0 ≤ p.u x) :
    ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L,
      (|p.v x|+|p.dv y|)+((∫ t in (0 : ℝ)..L, |p.v t|)+
        (∫ t in (0 : ℝ)..L, |p.dv t|)+∫ t in (0 : ℝ)..L, |s.ddv t|) ≤
      nu*(1/(mu*L)+2*L+2+1/mu+2*L+2)*(∫ t in (0 : ℝ)..L, p.u t^gamma) :=
  SpikeEstimates.signal_sobolev_le L mu nu gamma p.u p.v p.dv s.ddv hL hmu hnu hg
    p.continuous_u hu s.continuous_v s.nonnegative_v p.derivative_v
    s.continuous_dv s.derivative_dv s.stationary p.neumann_v_left p.neumann_v_right

/-- Exact power envelope of the manuscript for 0<m<2; the source moment,
first integral and signal-gradient bound are actual derived quantities. -/
theorem sup_bounds {L alpha chi m beta uStar gamma mu nu : ℝ}
    (p : ClassicalProfile L 0 0 alpha chi m beta)
    (s : ClassicalLogisticEstimates.SignalData p mu nu gamma)
    (hL : 0 < L) (hm : 0 < m) (hm2 : m < 2) (hbeta : 0 ≤ beta)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hg : 0 ≤ gamma)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hmass : ∫ x in (0 : ℝ)..L, p.u x = L*uStar) :
    let M := ∫ t in (0 : ℝ)..L, p.u t^gamma
    ∀ x ∈ Icc 0 L,
      p.u x^(2-m) ≤ uStar^(2-m)+2*(2-m)*|chi| *nu*L*uStar*M ∧
      p.u x ≤ (uStar^(2-m)+2*(2-m)*|chi| *nu*L*uStar*M)^(1/(2-m)) ∧
      |p.du x| ≤ 2*|chi| *nu*M*((uStar^(2-m)+2*(2-m)*|chi| *nu*L*uStar*M)^(1/(2-m)))^m := by
  apply SpikeEstimates.minimal_sup_bounds L uStar chi m beta nu
    (∫ t in (0 : ℝ)..L, p.u t^gamma) p.u p.v p.du p.dv hL hm hm2 hbeta
    p.continuous_u hpos p.derivative_u s.nonnegative_v (flux_identity p) _ hmass
  exact SpikeEstimates.signal_gradient_le_two L mu nu gamma p.u p.v p.dv s.ddv
    hL.le hmu hnu hg p.continuous_u (fun x hx => (hpos x hx).le)
    s.continuous_v s.nonnegative_v s.continuous_dv s.derivative_dv s.stationary
    p.neumann_v_left p.neumann_v_right

/-- The exact integrating factor is continuous for the actual signal data. -/
theorem continuous_signal_factor {L alpha chi m beta gamma mu nu : ℝ}
    (p : ClassicalProfile L 0 0 alpha chi m beta)
    (s : ClassicalLogisticEstimates.SignalData p mu nu gamma) :
    ContinuousOn (fun y => chi*p.dv y/(1+p.v y)^beta) (Icc 0 L) := by
  have hbase : ∀ y ∈ Icc 0 L, 0 < 1+p.v y := by
    intro y hy; linarith [s.nonnegative_v y hy]
  exact (continuousOn_const.mul s.continuous_dv).div
    ((continuousOn_const.add s.continuous_v).rpow_const (fun y hy => Or.inl (hbase y hy).ne'))
    (fun y hy => (Real.rpow_pos_of_pos (hbase y hy) beta).ne')

/-- Actual classical m=1 exponential representation, without an assumed flux
identity or an independently supplied integrating-factor regularity premise. -/
theorem exp_representation {L alpha chi beta gamma mu nu : ℝ}
    (p : ClassicalProfile L 0 0 alpha chi 1 beta)
    (s : ClassicalLogisticEstimates.SignalData p mu nu gamma)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x) :
    ∀ x₀ ∈ Icc 0 L, ∀ x ∈ Icc 0 L,
      p.u x = p.u x₀*exp (∫ y in x₀..x, chi*p.dv y/(1+p.v y)^beta) := by
  apply MinimalFlux.minimal_exp_representation L chi beta p.u p.v p.du p.dv
    p.continuous_u hpos p.derivative_u _ (continuous_signal_factor p s)
  intro x hx
  simpa only [Real.rpow_one] using flux_identity p x (Ioo_subset_Icc_self hx)

/-- Exact m=1 exponential envelope from the actual stationary equations,
signal gradient and prescribed mass. -/
theorem exp_sup_bound {L alpha chi Xbar beta uStar gamma mu nu : ℝ}
    (p : ClassicalProfile L 0 0 alpha chi 1 beta)
    (s : ClassicalLogisticEstimates.SignalData p mu nu gamma)
    (hL : 0 < L) (hbeta : 0 ≤ beta) (hchi : |chi| ≤ Xbar)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hg : 0 ≤ gamma)
    (hpos : ∀ x ∈ Icc 0 L, 0 < p.u x)
    (hmass : ∫ x in (0 : ℝ)..L, p.u x = L*uStar) :
    ∀ x ∈ Icc 0 L,
      p.u x ≤ uStar*exp (2*Xbar*nu*(∫ t in (0 : ℝ)..L, p.u t^gamma)*L) := by
  apply SpikeEstimates.minimal_exp_sup_bound L uStar chi Xbar beta nu
    (∫ t in (0 : ℝ)..L, p.u t^gamma) p.u p.v p.du p.dv hL hbeta hchi
    p.continuous_u hpos p.derivative_u _ (continuous_signal_factor p s) s.nonnegative_v _ hmass
  · intro x hx
    simpa only [Real.rpow_one] using flux_identity p x (Ioo_subset_Icc_self hx)
  · exact SpikeEstimates.signal_gradient_le_two L mu nu gamma p.u p.v p.dv s.ddv
      hL.le hmu hnu hg p.continuous_u (fun x hx => (hpos x hx).le)
      s.continuous_v s.nonnegative_v s.continuous_dv s.derivative_dv s.stationary
      p.neumann_v_left p.neumann_v_right

end
end ChemotaxisBifurcation.ClassicalMinimalEstimates
