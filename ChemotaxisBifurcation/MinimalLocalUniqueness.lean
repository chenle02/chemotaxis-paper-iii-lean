module
public import ChemotaxisBifurcation.PhysicalLocalUniqueness

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.MinimalLocalUniqueness
open Set Filter Topology MeasureTheory
noncomputable section

/-- A prescribed mean and a derivative bound control every deviation from
that mean, without assuming a crossing point or a Poincare inequality. -/
theorem deviation_le_of_mass {L U B : ℝ} {u du : ℝ → ℝ}
    (hL : 0 < L) (hu : ContinuousOn u (Icc 0 L))
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hB : 0 ≤ B) (hb : ∀ x ∈ Ioo 0 L, |du x| ≤ B)
    (hmass : ∫ x in (0 : ℝ)..L, u x = L * U) :
    ∀ x ∈ Icc 0 L, |u x - U| ≤ L * B := by
  obtain ⟨lo, hlo, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hu
  obtain ⟨hi, hhi, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hL.le) hu
  have hl : u lo ≤ U := by
    have h := IntervalMoments.le_integral_of_le hL.le hu (fun x hx => hmin hx)
    rw [hmass] at h
    exact le_of_mul_le_mul_left h hL
  have hh : U ≤ u hi := by
    have h := IntervalMoments.integral_le_of_le hL.le hu (fun x hx => hmax hx)
    rw [hmass] at h
    exact le_of_mul_le_mul_left h hL
  intro x hx
  have hupper := SpikeEstimates.le_add_integral_of_abs_deriv_le hu hdu
    (continuousOn_const (c := B)) (fun _ _ => hB) hb x hx lo hlo
  have hlower := SpikeEstimates.le_add_integral_of_abs_deriv_le hu hdu
    (continuousOn_const (c := B)) (fun _ _ => hB) hb hi hhi x hx
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hupper hlower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual literal minimal equation has zero integration constant. -/
theorem flux_identity {L alpha chi m beta : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L 0 0 alpha chi m beta)
    (hm : 1 ≤ m) (hv : ∀ x ∈ Icc 0 L, 0 ≤ q.v x) (hv0 : q.dv 0 = 0) :
    ∀ x ∈ Icc 0 L, q.du x = MinimalFlux.flux chi m beta q.u q.v q.dv x := by
  have hu : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
  have hdu : ContinuousOn q.du (Icc 0 L) := fun x hx => (q.derivative_du x hx).continuousWithinAt
  have hvc : ContinuousOn q.v (Icc 0 L) := fun x hx => (q.derivative_v x hx).continuousWithinAt
  have hdv : ContinuousOn q.dv (Icc 0 L) := fun x hx => (q.derivative_dv x hx).continuousWithinAt
  have hbase : ∀ x ∈ Icc 0 L, 0 < 1 + q.v x := fun x hx => by linarith [hv x hx]
  let J := MinimalFlux.flux chi m beta q.u q.v q.dv
  have hJ : ContinuousOn J (Icc 0 L) :=
    ((continuousOn_const.mul ((hu.rpow_const fun _ _ => Or.inr (by linarith : 0 ≤ m)).div
      ((continuousOn_const.add hvc).rpow_const fun x hx => Or.inl (hbase x hx).ne')
      (fun x hx => (Real.rpow_pos_of_pos (hbase x hx) beta).ne'))).mul hdv)
  have hz := MinimalFlux.eq_left_of_hasDerivAt_zero (hdu.sub hJ) (fun x hx => by
    have hx' := Ioo_subset_Icc_self hx
    have hdJ : HasDerivAt J (deriv J x) x :=
      ((PhysicalStrongPositivity.flux_hasDerivWithinAt (chi := chi) (beta := beta) hm hbase hx'
        (q.derivative_u x hx') (q.derivative_v x hx') (q.derivative_dv x hx')).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)).differentiableAt.hasDerivAt
    have hd := ((q.derivative_du x hx').hasDerivAt (Icc_mem_nhds hx.1 hx.2)).sub hdJ
    convert hd using 1
    have hs := q.stationary x hx
    change q.ddu x - deriv J x + 0 * q.u x - 0 * q.u x ^ (1 + alpha) = 0 at hs
    simpa using hs.symm)
  intro x hx
  have h := hz x hx
  change q.du x - J x = q.du 0 - J 0 at h
  simp only [q.neumann_left, J, MinimalFlux.flux, hv0, mul_zero, sub_zero] at h
  exact sub_eq_zero.mp h

/-- Small sensitivity forces the prescribed-mass minimal profile to be
constant. Both PDEs, the literal flux, and source Lipschitz control are used;
no local-uniqueness, energy, or crossing-point premise is assumed. -/
theorem exists_physical_uniqueness_radius (p : PhysicalParams) {L beta : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu)
    (hm : 1 ≤ p.m) (hbeta : 0 ≤ beta) (hsigequil : p.SignalEquilibrium) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ chi : ℝ, |chi| < epsilon →
      ∀ q : PhysicalStrongPositivity.StationaryProfile L 0 0 p.alpha chi p.m beta,
      (∀ x ∈ Icc 0 L, |q.u x - p.uStar| ≤ p.uStar/2) →
      (∀ x ∈ Icc 0 L, 0 ≤ q.v x) → q.dv 0 = 0 → q.dv L = 0 →
      (∀ x ∈ Ioo 0 L, q.ddv x - p.mu*q.v x + p.nu*q.u x ^ p.gamma = 0) →
      (∫ x in (0 : ℝ)..L, q.u x = L*p.uStar) →
      ∀ x ∈ Icc 0 L, q.u x = p.uStar := by
  obtain ⟨K, hK, hLip⟩ := signalSource_local_lipschitz p hu
  let M := (3*p.uStar/2) ^ p.m
  have hM : 0 ≤ M := Real.rpow_nonneg (by positivity) _
  let C := 2*M*L^2*K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨1/(C+1), by positivity, ?_⟩
  intro chi hchi q hsmall hv hv0 hvL hsig hmass
  have hucont : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
  have hpos : ∀ x ∈ Icc 0 L, 0 < q.u x := by
    intro x hx
    have h := (abs_le.mp (hsmall x hx)).1
    linarith
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hL.le)
    (hucont.sub continuousOn_const).abs
  let D := |q.u z-p.uStar|
  have hD : 0 ≤ D := abs_nonneg _
  have hDb : ∀ x ∈ Icc 0 L, |q.u x-p.uStar| ≤ D := fun x hx => hmax hx
  let sig := LocalStationaryEnergy.shiftedSignalProfile q hsigequil hsig hv0 hvL
  have hF : ContinuousOn (fun x => p.nu*(q.u x ^ p.gamma-p.uStar ^ p.gamma)) (Icc 0 L) :=
    continuousOn_const.mul ((hucont.rpow_const (fun x hx => Or.inl (hpos x hx).ne')).sub continuousOn_const)
  have hsource : ∀ x ∈ Icc 0 L, |p.nu*(q.u x ^ p.gamma-p.uStar ^ p.gamma)| ≤ K*D := by
    intro x hx
    have h := hLip (q.u x-p.uStar) (hsmall x hx)
    have h' : |p.nu*(q.u x ^ p.gamma-p.uStar ^ p.gamma)| ≤ K*|q.u x-p.uStar| := by
      simpa only [add_sub_cancel, mul_sub] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (hDb x hx) hK)
  have hdv := sig.derivative_bound hL hmu hF (mul_nonneg hK hD) hsource
  have hflux := flux_identity q hm hv hv0
  have hmob : ∀ x ∈ Icc 0 L, |q.u x ^ p.m/(1+q.v x)^beta| ≤ M := by
    intro x hx
    apply LocalStationaryEnergy.mobility_bound (hpos x hx).le _ (hv x hx) (by linarith) hbeta
    have h := (abs_le.mp (hsmall x hx)).2
    linarith
  have hderiv : ∀ x ∈ Ioo 0 L, |q.du x| ≤ |chi| *M*(2*L*(K*D)) := by
    intro x hx
    have hx' := Ioo_subset_Icc_self hx
    rw [hflux x hx', MinimalFlux.flux, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hmob x hx') (abs_nonneg chi))
      (hdv x hx') (abs_nonneg _) (mul_nonneg (abs_nonneg chi) hM)
  have hdev := deviation_le_of_mass hL hucont
    (fun x hx => (q.derivative_u x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (by positivity : 0 ≤ |chi| *M*(2*L*(K*D))) hderiv hmass z hz
  have hcontract : |chi| *C < 1 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < C+1)).mp hchi
    nlinarith [abs_nonneg chi]
  have hzero : D = 0 := by
    have hineq : D ≤ |chi| *C*D := by dsimp [D, C] at *; nlinarith [hdev]
    nlinarith
  intro x hx
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (by simpa [hzero] using hDb x hx) (abs_nonneg _)))

/-- The minimal fixed-mass local uniqueness input for AmbientClosure, derived
from actual profiles and continuity/injectivity of their phase-space map. -/
theorem eventually_trivial_of_physical_profiles
    {E : Type*} [TopologicalSpace E]
    (p : PhysicalParams) {L beta : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu)
    (hm : 1 ≤ p.m) (hbeta : 0 ≤ beta) (hsigequil : p.SignalEquilibrium)
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {uStar : E} {Sol : Set (ℝ × E)}
    (hProf : Continuous prof) (hInj : Function.Injective prof)
    (hconst : ∀ x, prof uStar x = p.uStar)
    (data : ∀ z ∈ Sol,
      PhysicalStrongPositivity.StationaryProfile L 0 0 p.alpha z.1 p.m beta)
    (hRep : ∀ z (hz : z ∈ Sol) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = prof z.2 ⟨x, hx⟩)
    (hV : ∀ z (hz : z ∈ Sol) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hV0 : ∀ z (hz : z ∈ Sol), (data z hz).dv 0 = 0)
    (hVL : ∀ z (hz : z ∈ Sol), (data z hz).dv L = 0)
    (hSignal : ∀ z (hz : z ∈ Sol) x, x ∈ Ioo 0 L →
      (data z hz).ddv x - p.mu * (data z hz).v x + p.nu * (data z hz).u x ^ p.gamma = 0)
    (hMass : ∀ z (hz : z ∈ Sol), ∫ x in (0 : ℝ)..L, (data z hz).u x = L*p.uStar) :
    ∀ᶠ z in nhds ((0 : ℝ), uStar), z ∈ Sol → z.2 = uStar := by
  obtain ⟨epsilon, heps, huni⟩ := exists_physical_uniqueness_radius p
    hL hu hmu hm hbeta hsigequil
  have hclose : ∀ᶠ z : ℝ × E in nhds ((0 : ℝ), uStar),
      dist (prof z.2) (prof uStar) < p.uStar/2 := by
    exact ((hProf.comp continuous_snd).tendsto ((0 : ℝ), uStar)).eventually
      (Metric.ball_mem_nhds _ (by positivity))
  have hchi : ∀ᶠ z : ℝ × E in nhds ((0 : ℝ), uStar), dist z.1 0 < epsilon :=
    (continuous_fst.tendsto ((0 : ℝ), uStar)).eventually (Metric.ball_mem_nhds _ heps)
  filter_upwards [hclose, hchi] with z hzclose hzchi
  intro hz
  have hsmall : ∀ x ∈ Icc 0 L, |(data z hz).u x - p.uStar| ≤ p.uStar/2 := by
    intro x hx
    rw [hRep z hz x hx]
    have hdist := ContinuousMap.dist_apply_le_dist (f := prof z.2) (g := prof uStar) ⟨x, hx⟩
    rw [hconst, Real.dist_eq] at hdist
    exact (hdist.trans_lt hzclose).le
  have hup := huni z.1 (by simpa only [Real.dist_eq, sub_zero] using hzchi)
    (data z hz) hsmall (hV z hz) (hV0 z hz) (hVL z hz) (hSignal z hz) (hMass z hz)
  apply hInj
  ext x
  rw [hconst]
  have hx := hup x x.property
  rwa [hRep z hz x x.property] at hx

end
end ChemotaxisBifurcation.MinimalLocalUniqueness
