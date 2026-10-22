module
public import ChemotaxisBifurcation.PhysicalLocalUniqueness
public import ChemotaxisBifurcation.StationaryMassIdentity

@[expose] public section

/-! Ambient admissibility with strong positivity, zero-sensitivity uniqueness
and local uniqueness derived for the actual logistic stationary equations.
Limit passage and the phase-space embedding remain explicit application data. -/
set_option autoImplicit false
namespace ChemotaxisBifurcation.PhysicalAmbientClosure
open Set Filter Topology
noncomputable section

/-- The literal classical population equation supplies mass balance, with
no independently supplied flux derivative or mass identity. -/
theorem mass_balance_of_physical_profile {L a b alpha chi m beta : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
    (hL : 0 ≤ L) (hm : 1 ≤ m) (halpha : 0 ≤ alpha)
    (hbase : ∀ x ∈ Icc 0 L, 0 < 1 + q.v x)
    (hv0 : q.dv 0 = 0) (hvL : q.dv L = 0) :
    a * (∫ x in (0 : ℝ)..L, q.u x) = b * (∫ x in (0 : ℝ)..L, q.u x ^ (1 + alpha)) := by
  have hu : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
  have hdu : ContinuousOn q.du (Icc 0 L) := fun x hx => (q.derivative_du x hx).continuousWithinAt
  have hv : ContinuousOn q.v (Icc 0 L) := fun x hx => (q.derivative_v x hx).continuousWithinAt
  have hdv : ContinuousOn q.dv (Icc 0 L) := fun x hx => (q.derivative_dv x hx).continuousWithinAt
  let J := MinimalFlux.flux chi m beta q.u q.v q.dv
  have hJ : ContinuousOn J (Icc 0 L) :=
    ((continuousOn_const.mul ((hu.rpow_const fun _ _ => Or.inr (by linarith : 0 ≤ m)).div
      ((continuousOn_const.add hv).rpow_const fun x hx => Or.inl (hbase x hx).ne')
      (fun x hx => (Real.rpow_pos_of_pos (hbase x hx) beta).ne'))).mul hdv)
  apply StationaryMassIdentity.logistic_mass_identity hL halpha hu (hdu.sub hJ)
  · intro x hx
    have hx' := Ioo_subset_Icc_self hx
    have hdJ : HasDerivAt J (deriv J x) x :=
      ((PhysicalStrongPositivity.flux_hasDerivWithinAt (chi := chi) (beta := beta) hm hbase hx'
        (q.derivative_u x hx') (q.derivative_v x hx') (q.derivative_dv x hx')).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)).differentiableAt.hasDerivAt
    have hd := ((q.derivative_du x hx').hasDerivAt (Icc_mem_nhds hx.1 hx.2)).sub hdJ
    convert hd using 1
    have hs := q.stationary x hx
    change q.ddu x - deriv J x + a * q.u x - b * q.u x ^ (1 + alpha) = 0 at hs
    linarith
  · simp [J, MinimalFlux.flux, q.neumann_left, hv0]
  · simp [J, MinimalFlux.flux, q.neumann_right, hvL]

theorem closure_subset_admissible
    {E : Type*} [TopologicalSpace E]
    (p : PhysicalParams) {L beta : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu)
    (hm : 1 ≤ p.m) (hbeta : 0 ≤ beta) (halpha : 0 < p.alpha) (hb : 0 < p.b)
    (hequil : p.LogisticEquilibrium) (hsigequil : p.SignalEquilibrium)
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {uStar : E} {S Sol : Set (ℝ × E)}
    (hProf : Continuous prof) (hInj : Function.Injective prof)
    (hconst : ∀ x, prof uStar x = p.uStar) (hAff : IsClosed Aff)
    (hS : S ⊆ AmbientClosure.admissibleSet prof Aff)
    (hSne : ∀ z ∈ S, z.2 ≠ uStar)
    (hSSol : S ⊆ Sol) (hLimit : closure S ⊆ Sol)
    (data : ∀ z ∈ Sol,
      PhysicalStrongPositivity.StationaryProfile L p.a p.b p.alpha z.1 p.m beta)
    (hRep : ∀ z (hz : z ∈ Sol) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = prof z.2 ⟨x, hx⟩)
    (hV : ∀ z (hz : z ∈ Sol) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hV0 : ∀ z (hz : z ∈ Sol), (data z hz).dv 0 = 0)
    (hVL : ∀ z (hz : z ∈ Sol), (data z hz).dv L = 0)
    (hSignal : ∀ z (hz : z ∈ Sol) x, x ∈ Ioo 0 L →
      (data z hz).ddv x - p.mu * (data z hz).v x + p.nu * (data z hz).u x ^ p.gamma = 0) :
    closure S ⊆ AmbientClosure.admissibleSet prof Aff := by
  have ha : 0 < p.a := by
    rw [hequil]
    exact mul_pos hb (Real.rpow_pos_of_pos hu _)
  have hUformula : (p.a / p.b) ^ (1 / p.alpha) = p.uStar := by
    have hab : p.a / p.b = p.uStar ^ p.alpha := by rw [hequil]; field_simp
    rw [hab, one_div, Real.rpow_rpow_inv hu.le halpha.ne']
  have hMax : ∀ z ∈ S, ∃ x, p.uStar ≤ prof z.2 x := by
    intro z hz
    let q := data z (hSSol hz)
    have hqpos : ∀ x ∈ Icc 0 L, 0 < q.u x := by
      intro x hx
      change 0 < (data z (hSSol hz)).u x
      rw [hRep z (hSSol hz) x hx]
      exact (hS hz).2.2 ⟨x, hx⟩
    have hmass := mass_balance_of_physical_profile q hL.le hm halpha.le
      (fun x hx => by linarith [hV z (hSSol hz) x hx]) (hV0 z (hSSol hz)) (hVL z (hSSol hz))
    have hc : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
    obtain ⟨x, hx, hge⟩ := AmbientClosure.logistic_exists_ge_uStar p.a p.b p.alpha L q.u
      ha hb halpha hL hc hqpos hmass
    rw [hUformula] at hge
    refine ⟨⟨x, hx⟩, ?_⟩
    change p.uStar ≤ (data z (hSSol hz)).u x at hge
    rwa [hRep z (hSSol hz) x hx] at hge
  have hIFT := PhysicalLocalUniqueness.eventually_trivial_of_physical_profiles p
    hL hu hmu hm hbeta halpha hb hequil hsigequil hProf hInj hconst data hRep hV hV0 hVL hSignal
  apply AmbientClosure.closure_subset_admissible hProf hAff hu hS hSne hMax hSSol hLimit
    ?_ ?_ hIFT
  · intro z hz _ _ hnonneg hpoint x
    have hnn : ∀ y ∈ Icc 0 L, 0 ≤ (data z hz).u y := by
      intro y hy
      rw [hRep z hz y hy]
      exact hnonneg ⟨y, hy⟩
    have hp : ∃ y ∈ Icc 0 L, 0 < (data z hz).u y := by
      obtain ⟨y, hy⟩ := hpoint
      exact ⟨y, y.property, by rw [hRep z hz y y.property]; exact hy⟩
    have hout := PhysicalStrongPositivity.StationaryProfile.positive_of_nonnegative
      (data z hz) hL hm halpha.le hnn (fun y hy => by linarith [hV z hz y hy]) hp x x.property
    rwa [hRep z hz x x.property] at hout
  · intro u hsol _ hpos
    let q := data ((0 : ℝ), u) hsol
    have hc : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
    have hdc : ContinuousOn q.du (Icc 0 L) := fun x hx => (q.derivative_du x hx).continuousWithinAt
    have hqp : ∀ x ∈ Icc 0 L, 0 < q.u x := by
      intro x hx
      change 0 < (data ((0 : ℝ), u) hsol).u x
      rw [hRep ((0 : ℝ), u) hsol x hx]
      exact hpos ⟨x, hx⟩
    have hflux : MinimalFlux.flux 0 p.m beta q.u q.v q.dv = fun _ : ℝ => 0 := by
      funext x; simp [MinimalFlux.flux]
    have hstat : ∀ x ∈ Ioo 0 L,
        q.ddu x + p.a * q.u x - p.b * q.u x ^ (1 + p.alpha) = 0 := by
      intro x hx
      have hs := q.stationary x hx
      change q.ddu x - deriv (MinimalFlux.flux 0 p.m beta q.u q.v q.dv) x +
        p.a * q.u x - p.b * q.u x ^ (1 + p.alpha) = 0 at hs
      rw [hflux] at hs
      simpa only [deriv_const, sub_zero] using hs
    have heq := AmbientClosure.logistic_zero_sensitivity_eq p.a p.b p.alpha L q.u q.du q.ddu
      ha hb halpha hL hc hqp
      (fun x hx => (q.derivative_u x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      hdc (fun x hx => (q.derivative_du x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      hstat q.neumann_left q.neumann_right
    rw [hUformula] at heq
    apply hInj
    ext x
    rw [hconst]
    have hx := heq x x.property
    change (data ((0 : ℝ), u) hsol).u x = p.uStar at hx
    rwa [hRep ((0 : ℝ), u) hsol x x.property] at hx

end
end ChemotaxisBifurcation.PhysicalAmbientClosure
