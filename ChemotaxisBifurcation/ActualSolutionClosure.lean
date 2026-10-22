module
public import ChemotaxisBifurcation.PhysicalClassicalAdapter
public import ChemotaxisBifurcation.PhysicalAmbientClosure
public import ChemotaxisBifurcation.MinimalLocalUniqueness
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ActualSolutionClosure
open Set Filter Topology MeasureTheory
noncomputable section

/-- Actual nonnegative classical solutions of both original stationary PDEs.
No closure or compactness property is part of this definition. -/
def solutionSet {E : Type*} {L : ℝ} (prof : E → C(Icc (0 : ℝ) L, ℝ))
    (a b alpha m beta mu nu gamma : ℝ) : Set (ℝ × E) :=
  {z | ∃ q : PhysicalStrongPositivity.StationaryProfile L a b alpha z.1 m beta,
    (∀ x : Icc (0 : ℝ) L, q.u x = prof z.2 x) ∧
    (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
    q.dv 0 = 0 ∧ q.dv L = 0 ∧
    ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma=0}

/-- Identification of an extracted actual solution uses uniqueness of the
ordinary scalar and pointwise limits of the given phase-space sequence. -/
theorem mem_solutionSet_of_limit {E : Type*} [TopologicalSpace E]
    {L a b alpha m beta mu nu gamma chiBar : ℝ}
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} (hProf : Continuous prof)
    {z : ℝ × E} {seq : ℕ → ℝ × E} (hz : Tendsto seq atTop (nhds z))
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chiBar m beta)
    {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (hchi : Tendsto (fun n => (seq (phi n)).1) atTop (nhds chiBar))
    (hu : ∀ x : Icc (0 : ℝ) L,
      Tendsto (fun n => prof (seq (phi n)).2 x) atTop (nhds (q.u x)))
    (hnn : ∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x)
    (hN0 : q.dv 0 = 0) (hNL : q.dv L = 0)
    (heq : ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma=0) :
    z ∈ solutionSet prof a b alpha m beta mu nu gamma := by
  have hseq := hz.comp hphi.tendsto_atTop
  have heqchi : chiBar = z.1 := tendsto_nhds_unique hchi (continuous_fst.tendsto z |>.comp hseq)
  subst chiBar
  refine ⟨q, ?_, hnn, hN0, hNL, heq⟩
  intro x
  have hc : Continuous (fun y : ℝ × E => prof y.2 x) := by
    exact (continuous_eval_const x).comp (hProf.comp continuous_snd)
  exact tendsto_nhds_unique (hu x) ((hc.tendsto z).comp hseq)

/-- Actual logistic stationary solutions are closed along nonconstant positive
branches, by the derived bounded-sensitivity compactness theorem. -/
theorem closure_subset_solutionSet {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]
    {L a b alpha m beta mu nu gamma : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha)
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} (hProf : Continuous prof)
    {S : Set (ℝ × E)} (hS : S ⊆ solutionSet prof a b alpha m beta mu nu gamma)
    (hpos : ∀ z ∈ S, ∀ x : Icc (0 : ℝ) L, 0 < prof z.2 x)
    (hnonconst : ∀ z ∈ S, ∃ x y : Icc (0 : ℝ) L, prof z.2 x ≠ prof z.2 y) :
    closure S ⊆ solutionSet prof a b alpha m beta mu nu gamma := by
  intro z hz
  obtain ⟨seq, hseqS, hseq⟩ := mem_closure_iff_seq_limit.mp hz
  choose q hrep hnn hN0 hNL heq using fun n => hS (hseqS n)
  let chi := fun n => (seq n).1
  have hchil : Tendsto chi atTop (nhds z.1) := (continuous_fst.tendsto z).comp hseq
  obtain ⟨X, hX⟩ := (Metric.isBounded_range_of_tendsto chi hchil).exists_norm_le
  have hchi : ∀ n, |chi n| ≤ X := fun n => by simpa only [Real.norm_eq_abs] using hX _ (mem_range_self n)
  let p := fun n => PhysicalClassicalAdapter.toClassicalProfile (q n) hm
    (fun x hx => (hnn n x hx).2) (hN0 n) (hNL n)
  let sig := fun n => PhysicalClassicalAdapter.toSignalData (q n) hm
    (fun x hx => (hnn n x hx).2) (hN0 n) (hNL n) (heq n)
  obtain ⟨chiBar, limit, phi, hphi, hcl, hul, _, _, _, hnnl, hN0l, hNLl, heql⟩ :=
    ClassicalStationaryLimit.exists_classical_stationary_limit chi p sig
      hL ha hb halpha hm hm1 hbeta hmu hnu hgamma hgamma1 hchi
      (fun n x hx => by change 0 < (q n).u x; rw [hrep n ⟨x,hx⟩]; exact hpos _ (hseqS n) ⟨x,hx⟩)
      (fun n => by
        obtain ⟨x,y,hxy⟩ := hnonconst _ (hseqS n)
        refine ⟨x,x.property,y,y.property,?_⟩
        change (q n).u x ≠ (q n).u y
        rw [hrep n x,hrep n y]
        exact hxy)
  apply mem_solutionSet_of_limit hProf hseq limit hphi hcl _ hnnl hN0l hNLl heql
  intro x
  have h := hul.tendsto_at x.property
  change Tendsto (fun n => (q (phi n)).u x) atTop (nhds (limit.u x)) at h
  simpa only [hrep, Function.comp_apply] using h

/-- Ambient admissibility for the actual logistic stationary solution set.
The former hLimit, hSMP, hIFT, hZero and hMax inputs are all discharged. -/
theorem closure_subset_admissible {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]
    (p : PhysicalParams) {L beta : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2) (hbeta : 0 ≤ beta)
    (halpha : 0 < p.alpha) (hb : 0 < p.b)
    (hnu : 0 ≤ p.nu) (hgamma : 0 < p.gamma) (hgamma1 : p.gamma ≤ 1+p.alpha)
    (hequil : p.LogisticEquilibrium) (hsigequil : p.SignalEquilibrium)
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {uStar : E} {S : Set (ℝ × E)}
    (hProf : Continuous prof) (hInj : Function.Injective prof)
    (hconst : ∀ x, prof uStar x = p.uStar) (hAff : IsClosed Aff)
    (hS : S ⊆ AmbientClosure.admissibleSet prof Aff)
    (hSne : ∀ z ∈ S, z.2 ≠ uStar)
    (hSSol : S ⊆ solutionSet prof p.a p.b p.alpha p.m beta p.mu p.nu p.gamma)
    (hnonconst : ∀ z ∈ S, ∃ x y : Icc (0 : ℝ) L, prof z.2 x ≠ prof z.2 y) :
    closure S ⊆ AmbientClosure.admissibleSet prof Aff := by
  have ha : 0 < p.a := by
    rw [hequil]
    exact mul_pos hb (Real.rpow_pos_of_pos hu _)
  let Sol := solutionSet prof p.a p.b p.alpha p.m beta p.mu p.nu p.gamma
  have hLimit : closure S ⊆ Sol := closure_subset_solutionSet hL ha hb halpha hm hm1 hbeta
    hmu hnu hgamma hgamma1 hProf hSSol (fun z hz x => (hS hz).2.2 x) hnonconst
  choose data hrep hnn hN0 hNL heq using fun z (hz : z ∈ Sol) => hz
  apply PhysicalAmbientClosure.closure_subset_admissible p hL hu hmu hm hbeta halpha hb
    hequil hsigequil hProf hInj hconst hAff hS hSne hSSol hLimit data
  · intro z hz x hx
    exact hrep z hz ⟨x,hx⟩
  · exact fun z hz x hx => (hnn z hz x hx).2
  · exact hN0
  · exact hNL
  · exact heq

/-- Actual minimal stationary solutions with their prescribed population
mass. The mass is ordinary model data, never a closure condition. -/
def minimalSolutionSet {E : Type*} {L : ℝ} (prof : E → C(Icc (0 : ℝ) L, ℝ))
    (alpha m beta mu nu gamma U : ℝ) : Set (ℝ × E) :=
  {z | ∃ q : PhysicalStrongPositivity.StationaryProfile L 0 0 alpha z.1 m beta,
    (∀ x : Icc (0 : ℝ) L, q.u x = prof z.2 x) ∧
    (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
    q.dv 0 = 0 ∧ q.dv L = 0 ∧
    (∫ x in (0 : ℝ)..L, q.u x) = L*U ∧
    ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma=0}

/-- Minimal prescribed-mass stationary solutions retain the original PDEs,
Neumann data and prescribed mass at every phase-space closure point. -/
theorem closure_subset_minimalSolutionSet {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]
    {L alpha m beta mu nu gamma U : ℝ}
    (hL : 0 < L) (halpha : 0 ≤ alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} (hProf : Continuous prof)
    {S : Set (ℝ × E)} (hS : S ⊆ minimalSolutionSet prof alpha m beta mu nu gamma U)
    (hpos : ∀ z ∈ S, ∀ x : Icc (0 : ℝ) L, 0 < prof z.2 x) :
    closure S ⊆ minimalSolutionSet prof alpha m beta mu nu gamma U := by
  intro z hz
  obtain ⟨seq, hseqS, hseq⟩ := mem_closure_iff_seq_limit.mp hz
  choose q hrep hnn hN0 hNL hmass heq using fun n => hS (hseqS n)
  let chi := fun n => (seq n).1
  have hchil : Tendsto chi atTop (nhds z.1) := (continuous_fst.tendsto z).comp hseq
  obtain ⟨X, hX⟩ := (Metric.isBounded_range_of_tendsto chi hchil).exists_norm_le
  have hchi : ∀ n, |chi n| ≤ X := fun n => by simpa only [Real.norm_eq_abs] using hX _ (mem_range_self n)
  let p := fun n => PhysicalClassicalAdapter.toClassicalProfile (q n) hm
    (fun x hx => (hnn n x hx).2) (hN0 n) (hNL n)
  let sig := fun n => PhysicalClassicalAdapter.toSignalData (q n) hm
    (fun x hx => (hnn n x hx).2) (hN0 n) (hNL n) (heq n)
  obtain ⟨chiBar, limit, phi, hphi, hcl, hul, _, _, _, _, _, _, _, hnnl, hN0l, hNLl, hmassl, heql⟩ :=
    ClassicalMinimalCompactness.exists_classical_componentH2_stationary_limit chi p sig
      hL halpha hm hm1 hbeta hmu hnu hgamma hgamma1
      (fun n => (q n).continuous_ddu) (fun n => (q n).continuous_ddv) hchi
      (fun n x hx => by change 0 < (q n).u x; rw [hrep n ⟨x,hx⟩]; exact hpos _ (hseqS n) ⟨x,hx⟩)
      hmass
  have hseqphi := hseq.comp hphi.tendsto_atTop
  have heqchi : chiBar = z.1 := tendsto_nhds_unique hcl ((continuous_fst.tendsto z).comp hseqphi)
  subst chiBar
  refine ⟨limit, ?_, hnnl, hN0l, hNLl, hmassl, heql⟩
  intro x
  have h := hul.tendsto_at x.property
  change Tendsto (fun n => (q (phi n)).u x) atTop (nhds (limit.u x)) at h
  have hc : Continuous (fun y : ℝ × E => prof y.2 x) :=
    (continuous_eval_const x).comp (hProf.comp continuous_snd)
  have hlim : Tendsto (fun n => prof (seq (phi n)).2 x) atTop (nhds (limit.u x)) := by
    simpa only [hrep] using h
  have hother : Tendsto (fun n => prof (seq (phi n)).2 x) atTop (nhds (prof z.2 x)) :=
    (hc.tendsto z).comp hseqphi
  exact tendsto_nhds_unique hlim hother

/-- Ambient admissibility for the actual prescribed-mass minimal stationary
solution set, with all analytic closure/positivity/uniqueness inputs derived. -/
theorem closure_subset_admissible_minimal {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]
    (p : PhysicalParams) {L beta : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta) (halpha : 0 ≤ p.alpha)
    (hnu : 0 ≤ p.nu) (hgamma : 0 ≤ p.gamma) (hgamma1 : p.gamma ≤ 1)
    (hsigequil : p.SignalEquilibrium)
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {uStar : E} {S : Set (ℝ × E)}
    (hProf : Continuous prof) (hInj : Function.Injective prof)
    (hconst : ∀ x, prof uStar x = p.uStar) (hAff : IsClosed Aff)
    (hS : S ⊆ AmbientClosure.admissibleSet prof Aff)
    (hSne : ∀ z ∈ S, z.2 ≠ uStar)
    (hSSol : S ⊆ minimalSolutionSet prof p.alpha p.m beta p.mu p.nu p.gamma p.uStar) :
    closure S ⊆ AmbientClosure.admissibleSet prof Aff := by
  let Sol := minimalSolutionSet prof p.alpha p.m beta p.mu p.nu p.gamma p.uStar
  have hLimit : closure S ⊆ Sol := closure_subset_minimalSolutionSet hL halpha hm hm1 hbeta
    hmu hnu hgamma hgamma1 hProf hSSol (fun z hz x => (hS hz).2.2 x)
  choose data hrep hnn hN0 hNL hmass heq using fun z (hz : z ∈ Sol) => hz
  have hRep : ∀ z (hz : z ∈ Sol) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = prof z.2 ⟨x,hx⟩ := fun z hz x hx => hrep z hz ⟨x,hx⟩
  have hV : ∀ z (hz : z ∈ Sol) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x :=
    fun z hz x hx => (hnn z hz x hx).2
  have hIFT := MinimalLocalUniqueness.eventually_trivial_of_physical_profiles p
    hL hu hmu hm hbeta hsigequil hProf hInj hconst data hRep hV hN0 hNL heq hmass
  have hMax : ∀ z ∈ S, ∃ x, p.uStar ≤ prof z.2 x := by
    intro z hz
    let q := data z (hSSol hz)
    have hc : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
    obtain ⟨x,hx,hge⟩ := AmbientClosure.exists_ge_mean L p.uStar q.u hL hc (hmass z (hSSol hz))
    refine ⟨⟨x,hx⟩,?_⟩
    change p.uStar ≤ (data z (hSSol hz)).u x at hge
    rwa [hRep z (hSSol hz) x hx] at hge
  apply AmbientClosure.closure_subset_admissible hProf hAff hu hS hSne hMax hSSol hLimit
    ?_ ?_ hIFT
  · intro z hz _ _ _ hpoint x
    obtain ⟨y,hy⟩ := hpoint
    have hp : ∃ y ∈ Icc 0 L, 0 < (data z hz).u y :=
      ⟨y,y.property,by rw [hRep z hz y y.property]; exact hy⟩
    have hout := PhysicalStrongPositivity.StationaryProfile.positive_of_nonnegative
      (data z hz) hL hm halpha (fun y hy => (hnn z hz y hy).1)
      (fun y hy => by linarith [hV z hz y hy]) hp x x.property
    rwa [hRep z hz x x.property] at hout
  · intro u hsol _ _
    let q := data ((0 : ℝ),u) hsol
    have hc : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
    have hf := MinimalLocalUniqueness.flux_identity q hm (hV _ hsol) (hN0 _ hsol)
    have hd : ∀ x ∈ Ioo 0 L, |q.du x| ≤ 0 := by
      intro x hx
      rw [hf x (Ioo_subset_Icc_self hx)]
      simp [MinimalFlux.flux]
    have hpop := MinimalLocalUniqueness.deviation_le_of_mass hL hc
      (fun x hx => (q.derivative_u x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      le_rfl hd (hmass _ hsol)
    apply hInj
    ext x
    rw [hconst]
    have hx := hpop x x.property
    have hequal : q.u x = p.uStar := sub_eq_zero.mp (abs_eq_zero.mp (by simpa using hx))
    change (data ((0 : ℝ),u) hsol).u x = p.uStar at hequal
    rwa [hRep _ hsol x x.property] at hequal

end
end ChemotaxisBifurcation.ActualSolutionClosure
