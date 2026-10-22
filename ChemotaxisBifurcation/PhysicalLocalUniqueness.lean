module
public import ChemotaxisBifurcation.LocalStationaryEnergy
public import ChemotaxisBifurcation.SignalLipschitz

@[expose] public section

/-! Small-sensitivity uniqueness for actual physical stationary profiles.
Source Lipschitz, mobility, reaction coercivity and the sensitivity radius are
derived. Classical regularity and the two actual PDEs remain standing data. -/
set_option autoImplicit false
namespace ChemotaxisBifurcation.PhysicalLocalUniqueness
open Set Filter Topology MeasureTheory
noncomputable section

/-- Local uniqueness in the actual physical parameters with the source
Lipschitz constant discharged. The radius is uniform before chi and profiles. -/
theorem exists_physical_uniqueness_radius (p : PhysicalParams) (L beta : ℝ)
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu)
    (hm : 1 ≤ p.m) (hbeta : 0 ≤ beta) (halpha : 0 < p.alpha) (hb : 0 < p.b)
    (hequil : p.LogisticEquilibrium) (hsigequil : p.SignalEquilibrium) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ chi : ℝ, |chi| < epsilon →
      ∀ q : PhysicalStrongPositivity.StationaryProfile L p.a p.b p.alpha chi p.m beta,
      (∀ x ∈ Icc 0 L, |q.u x - p.uStar| ≤ p.uStar/2) →
      (∀ x ∈ Icc 0 L, 0 ≤ q.v x) → q.dv 0 = 0 → q.dv L = 0 →
      (∀ x ∈ Ioo 0 L, q.ddv x - p.mu * q.v x + p.nu * q.u x ^ p.gamma = 0) →
      ∀ x ∈ Icc 0 L, q.u x = p.uStar := by
  obtain ⟨K, hK, hLip⟩ := signalSource_local_lipschitz p hu
  have hell : 0 < p.uStar/2 := by positivity
  have hLH : p.uStar/2 ≤ 3*p.uStar/2 := by linarith
  have hU : p.uStar ∈ Icc (p.uStar/2) (3*p.uStar/2) := by constructor <;> linarith
  obtain ⟨epsilon, heps, huni⟩ := LocalStationaryEnergy.exists_uniqueness_radius_of_physical_system
    (V := p.vStar) hL hmu hm hbeta halpha hb hell hLH hU hequil hsigequil hK
  refine ⟨epsilon, heps, ?_⟩
  intro chi hchi q hsmall hv hv0 hvL hsig
  apply huni chi hchi q ?_ hv hv0 hvL hsig ?_
  · intro x hx
    have h := abs_le.mp (hsmall x hx)
    constructor <;> linarith
  · intro x hx
    have h := hLip (q.u x - p.uStar) (hsmall x hx)
    convert h using 1
    congr 1
    rw [add_sub_cancel]
    ring


/-- The signal is also the physical constant once population uniqueness is
known; its actual shifted elliptic response has zero source. -/
theorem signal_eq_of_population_eq (p : PhysicalParams) {L beta chi : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L p.a p.b p.alpha chi p.m beta)
    (hL : 0 < L) (hmu : 0 < p.mu) (hu : 0 < p.uStar)
    (hsigequil : p.SignalEquilibrium)
    (hpop : ∀ x ∈ Icc 0 L, q.u x = p.uStar)
    (hv0 : q.dv 0 = 0) (hvL : q.dv L = 0)
    (hsig : ∀ x ∈ Ioo 0 L, q.ddv x - p.mu * q.v x + p.nu * q.u x ^ p.gamma = 0) :
    ∀ x ∈ Icc 0 L, q.v x = p.vStar := by
  let sig := LocalStationaryEnergy.shiftedSignalProfile q hsigequil hsig hv0 hvL
  have huc : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
  have hF : ContinuousOn (fun x => p.nu * (q.u x ^ p.gamma - p.uStar ^ p.gamma))
      (Icc 0 L) := continuousOn_const.mul
      ((huc.rpow_const fun x hx => Or.inl (by rw [hpop x hx]; exact hu.ne')).sub continuousOn_const)
  have hb := sig.value_bound hL hmu hF (B := 0) le_rfl (fun x hx => by rw [hpop x hx]; simp)
  intro x hx
  have hz := hb x hx
  change |q.v x - p.vStar| ≤ (0 : ℝ) / p.mu + 2 * L ^ 2 * 0 at hz
  simp only [zero_div, mul_zero, add_zero] at hz
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

/-- The local uniqueness input consumed by AmbientClosure follows from the
actual PDE energy argument and continuity/injectivity of the profile map.
No implicit-function or local-uniqueness theorem is assumed. -/
theorem eventually_trivial_of_physical_profiles
    {E : Type*} [TopologicalSpace E]
    (p : PhysicalParams) {L beta : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu)
    (hm : 1 ≤ p.m) (hbeta : 0 ≤ beta) (halpha : 0 < p.alpha) (hb : 0 < p.b)
    (hequil : p.LogisticEquilibrium) (hsigequil : p.SignalEquilibrium)
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {uStar : E} {Sol : Set (ℝ × E)}
    (hProf : Continuous prof) (hInj : Function.Injective prof)
    (hconst : ∀ x, prof uStar x = p.uStar)
    (data : ∀ z ∈ Sol,
      PhysicalStrongPositivity.StationaryProfile L p.a p.b p.alpha z.1 p.m beta)
    (hRep : ∀ z (hz : z ∈ Sol) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = prof z.2 ⟨x, hx⟩)
    (hV : ∀ z (hz : z ∈ Sol) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hV0 : ∀ z (hz : z ∈ Sol), (data z hz).dv 0 = 0)
    (hVL : ∀ z (hz : z ∈ Sol), (data z hz).dv L = 0)
    (hSignal : ∀ z (hz : z ∈ Sol) x, x ∈ Ioo 0 L →
      (data z hz).ddv x - p.mu * (data z hz).v x + p.nu * (data z hz).u x ^ p.gamma = 0) :
    ∀ᶠ z in nhds ((0 : ℝ), uStar), z ∈ Sol → z.2 = uStar := by
  obtain ⟨epsilon, heps, huni⟩ := exists_physical_uniqueness_radius p L beta
    hL hu hmu hm hbeta halpha hb hequil hsigequil
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
    (data z hz) hsmall (hV z hz) (hV0 z hz) (hVL z hz) (hSignal z hz)
  apply hInj
  ext x
  rw [hconst]
  have hx := hup x x.property
  rwa [hRep z hz x x.property] at hx

end
end ChemotaxisBifurcation.PhysicalLocalUniqueness
