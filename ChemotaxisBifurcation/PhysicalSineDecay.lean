module
public import ChemotaxisBifurcation.MonotoneSineBound
public import ChemotaxisBifurcation.PhysicalClassicalAdapter
public import ChemotaxisBifurcation.MinimalLocalUniqueness
public import ChemotaxisBifurcation.IntervalConcentration

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.PhysicalSineDecay
open Real Set MeasureTheory Filter Topology MonotoneLocusGeneral
noncomputable section

/-- The actual minimal population PDE gives the first-order stationary
system used by the existing general-mobility monotonicity/ODE uniqueness proof.
No flux identity or differentiated signal equation is assumed. -/
theorem toStationarySolution {L chi m beta mu nu gamma : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L 0 0 0 chi m beta)
    (hL : 0 < L) (hm : 1 ≤ m) (hgamma : 0 ≤ gamma)
    (hu : ∀ x ∈ Icc 0 L, 0 < q.u x) (hv : ∀ x ∈ Icc 0 L, 0 ≤ q.v x)
    (hN0 : q.dv 0 = 0) (hNL : q.dv L = 0)
    (heq : ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) :
    StationarySolution chi mu nu gamma beta m L q.u q.v q.dv := by
  let p := PhysicalClassicalAdapter.toClassicalProfile q hm hv hN0 hNL
  let s := PhysicalClassicalAdapter.toSignalData q hm hv hN0 hNL heq
  have hfield := ClassicalStationaryC2Limit.field_eq_actual_derivatives p s hL hm le_rfl hgamma
    (fun x hx => (hu x hx).le) q.continuous_ddu q.continuous_ddv
  have hsig : ∀ x ∈ Icc 0 L, mu*q.v x-nu*q.u x^gamma = q.ddv x := by
    intro x hx
    exact congrArg (fun z : StationaryODEState.State => z.2.2.2) (hfield x hx)
  have hflux := MinimalLocalUniqueness.flux_identity q hm hv hN0
  refine {
    u_pos := hu
    v_pos := fun x hx => by linarith [hv x hx]
    deriv_u := ?_
    deriv_v := q.derivative_v
    deriv_y := ?_
    bc_left := hN0
    bc_right := hNL }
  · intro x hx
    rw [← show q.du x = chi*(q.u x^m/(1+q.v x)^beta)*q.dv x from hflux x hx]
    exact q.derivative_u x hx
  · intro x hx
    rw [hsig x hx]
    exact q.derivative_dv x hx

def signalEnvelope (L mu nu gamma uStar : ℝ) : ℝ :=
  nu*(uStar^gamma)/mu+2*nu*L^2*uStar^gamma

/-- The actual signal sup bound is uniform in sensitivity, from the actual
signal equation and prescribed-mass concave-power Jensen estimate. -/
theorem signal_le_envelope {L chi m beta mu nu gamma uStar : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L 0 0 0 chi m beta)
    (hL : 0 < L) (hm : 1 ≤ m) (hmu : 0 < mu) (hnu : 0 ≤ nu)
    (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hu : ∀ x ∈ Icc 0 L, 0 < q.u x) (hv : ∀ x ∈ Icc 0 L, 0 ≤ q.v x)
    (hN0 : q.dv 0 = 0) (hNL : q.dv L = 0)
    (heq : ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0)
    (hmass : ∫ x in (0 : ℝ)..L, q.u x = L*uStar) :
    ∀ x ∈ Icc 0 L, q.v x ≤ signalEnvelope L mu nu gamma uStar := by
  let p := PhysicalClassicalAdapter.toClassicalProfile q hm hv hN0 hNL
  let s := PhysicalClassicalAdapter.toSignalData q hm hv hN0 hNL heq
  have hmoment := ClassicalMinimalEstimates.power_moment p hL hgamma hgamma1 hu hmass
  have hsup := SpikeEstimates.signal_sup_le L mu nu gamma q.u q.v q.dv q.ddv hL hmu hnu hgamma
    p.continuous_u (fun x hx => (hu x hx).le) s.continuous_v hv p.derivative_v s.continuous_dv
    s.derivative_dv heq hN0 hNL
  intro x hx
  have h1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmoment hnu) (mul_nonneg hmu.le hL.le)
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmoment
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnu)) hL.le
  calc q.v x ≤ nu*(∫ y in (0 : ℝ)..L, q.u y^gamma)/(mu*L)+2*nu*(∫ y in (0 : ℝ)..L, q.u y^gamma)*L := (hsup x hx).2
    _ ≤ nu*(L*uStar^gamma)/(mu*L)+2*nu*(L*uStar^gamma)*L := add_le_add h1 h2
    _ = signalEnvelope L mu nu gamma uStar := by
      dsimp [signalEnvelope]
      field_simp

/-- Actual minimal stationary equations, monotonicity, fixed mass and large
sensitivity force interior population values to vanish. No sine-test estimate,
pointwise decay, tail bound or concentration conclusion is an input. -/
theorem interior_tendsto_zero {L m beta mu nu gamma uStar : ℝ}
    (chi : ℕ → ℝ)
    (q : ∀ n, PhysicalStrongPositivity.StationaryProfile L 0 0 0 (chi n) m beta)
    (hL : 0 < L) (hm : 1 ≤ m) (hbeta : 0 ≤ beta) (hmu : 0 < mu) (hnu : 0 < nu)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hu : ∀ n x, x ∈ Icc 0 L → 0 < (q n).u x)
    (hv : ∀ n x, x ∈ Icc 0 L → 0 ≤ (q n).v x)
    (hN0 : ∀ n, (q n).dv 0 = 0) (hNL : ∀ n, (q n).dv L = 0)
    (heq : ∀ n x, x ∈ Ioo 0 L → (q n).ddv x-mu*(q n).v x+nu*(q n).u x^gamma = 0)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, (q n).u x = L*uStar)
    (hanti : ∀ n, StrictAntiOn (q n).u (Icc 0 L))
    (hchi : Tendsto chi atTop atTop) :
    ∀ delta ∈ Ioo 0 L, Tendsto (fun n => (q n).u delta) atTop (nhds 0) := by
  intro delta hdelta
  let V := signalEnvelope L mu nu gamma uStar
  let D := (mu+(Real.pi/(delta-delta/2))^2)*(1+V)^beta
  have hpow : 0 ≤ m+gamma-1 := by linarith
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  let A := nu*gamma*epsilon^(m+gamma-1)
  have hA : 0 < A := by dsimp [A]; positivity
  filter_upwards [hchi.eventually_gt_atTop (max 0 ((D+1)/A))] with n hn
  have hchipos : 0 < chi n := (le_max_left _ _).trans_lt hn
  have hlarge : D+1 < chi n*A := (div_lt_iff₀ hA).mp ((le_max_right _ _).trans_lt hn)
  have hnc : ¬IsConstOn (q n).u L := by
    intro hh
    have hlt := hanti n ⟨le_rfl,hL.le⟩ ⟨hL.le,le_rfl⟩ hL
    rw [hh L ⟨hL.le,le_rfl⟩] at hlt
    exact (lt_irrefl _ hlt)
  have hineq := MonotoneSineBound.interior_power_bound
    (toStationarySolution (q n) hL hm hgamma.le (hu n) (hv n) (hN0 n) (hNL n) (heq n))
    hchipos hmu.le hnu hgamma hm hbeta (hanti n).antitoneOn hnc hdelta
    (signal_le_envelope (q n) hL hm hmu hnu.le hgamma.le hgamma1
      (hu n) (hv n) (hN0 n) (hNL n) (heq n) (hmass n))
  rw [Real.dist_eq,sub_zero,abs_of_pos (hu n delta (Ioo_subset_Icc_self hdelta))]
  by_contra hnot
  have hp := Real.rpow_le_rpow hepsilon.le (le_of_not_gt hnot) hpow
  have hc : 0 ≤ chi n*nu*gamma := by positivity
  have hh := mul_le_mul_of_nonneg_left hp hc
  change chi n*nu*gamma*(q n).u delta^(m+gamma-1) ≤ D at hineq
  dsimp [A] at hlarge
  nlinarith

theorem interior_tendsto_zero_increasing {L m beta mu nu gamma uStar : ℝ}
    (chi : ℕ → ℝ)
    (q : ∀ n, PhysicalStrongPositivity.StationaryProfile L 0 0 0 (chi n) m beta)
    (hL : 0 < L) (hm : 1 ≤ m) (hbeta : 0 ≤ beta) (hmu : 0 < mu) (hnu : 0 < nu)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hu : ∀ n x, x ∈ Icc 0 L → 0 < (q n).u x)
    (hv : ∀ n x, x ∈ Icc 0 L → 0 ≤ (q n).v x)
    (hN0 : ∀ n, (q n).dv 0 = 0) (hNL : ∀ n, (q n).dv L = 0)
    (heq : ∀ n x, x ∈ Ioo 0 L → (q n).ddv x-mu*(q n).v x+nu*(q n).u x^gamma = 0)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, (q n).u x = L*uStar)
    (hmono : ∀ n, StrictMonoOn (q n).u (Icc 0 L))
    (hchi : Tendsto chi atTop atTop) :
    ∀ delta ∈ Ioo 0 L, Tendsto (fun n => (q n).u delta) atTop (nhds 0) := by
  intro delta hdelta
  let V := signalEnvelope L mu nu gamma uStar
  let D := (mu+(Real.pi/((delta+L)/2-delta))^2)*(1+V)^beta
  have hpow : 0 ≤ m+gamma-1 := by linarith
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  let A := nu*gamma*epsilon^(m+gamma-1)
  have hA : 0 < A := by dsimp [A]; positivity
  filter_upwards [hchi.eventually_gt_atTop (max 0 ((D+1)/A))] with n hn
  have hchipos : 0 < chi n := (le_max_left _ _).trans_lt hn
  have hlarge : D+1 < chi n*A := (div_lt_iff₀ hA).mp ((le_max_right _ _).trans_lt hn)
  have hnc : ¬IsConstOn (q n).u L := by
    intro hh
    have hlt := hmono n ⟨le_rfl,hL.le⟩ ⟨hL.le,le_rfl⟩ hL
    rw [hh L ⟨hL.le,le_rfl⟩] at hlt
    exact (lt_irrefl _ hlt)
  have hineq := MonotoneSineBound.interior_power_bound_right
    (toStationarySolution (q n) hL hm hgamma.le (hu n) (hv n) (hN0 n) (hNL n) (heq n))
    hchipos hmu.le hnu hgamma hm hbeta (hmono n).monotoneOn hnc hdelta
    (signal_le_envelope (q n) hL hm hmu hnu.le hgamma.le hgamma1
      (hu n) (hv n) (hN0 n) (hNL n) (heq n) (hmass n))
  rw [Real.dist_eq,sub_zero,abs_of_pos (hu n delta (Ioo_subset_Icc_self hdelta))]
  by_contra hnot
  have hp := Real.rpow_le_rpow hepsilon.le (le_of_not_gt hnot) hpow
  have hc : 0 ≤ chi n*nu*gamma := by positivity
  have hh := mul_le_mul_of_nonneg_left hp hc
  change chi n*nu*gamma*(q n).u delta^(m+gamma-1) ≤ D at hineq
  dsimp [A] at hlarge
  nlinarith

end
end ChemotaxisBifurcation.PhysicalSineDecay
