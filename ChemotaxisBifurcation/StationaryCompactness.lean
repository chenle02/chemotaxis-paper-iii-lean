module
public import ChemotaxisBifurcation.StationaryODEState

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.StationaryCompactness
open Real Set MeasureTheory Filter Topology StationaryODEState
noncomputable section

/-- Bounded-sensitivity positive classical logistic stationary profiles have
an actual simultaneous parameter/population/signal subsequence. Their limiting
first-order stationary system and endpoint derivatives are derived, not inputs. -/
theorem exists_augmented_limit {L a b alpha m beta mu nu gamma X : ℝ}
    (chi : ℕ → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha)
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hnonconst : ∀ n, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, (p n).u x ≠ (p n).u y) :
    ∃ g : ℝ → State, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ContinuousOn g (Icc 0 L) ∧
      TendstoUniformlyOn (fun n x => point (chi (phi n)) ((p (phi n)).u x)
        ((p (phi n)).du x) ((p (phi n)).v x) ((p (phi n)).dv x)) g atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n x => field a b alpha m beta mu nu gamma
        (point (chi (phi n)) ((p (phi n)).u x) ((p (phi n)).du x)
          ((p (phi n)).v x) ((p (phi n)).dv x)))
        (fun x => field a b alpha m beta mu nu gamma (g x)) atTop (Icc 0 L) ∧
      (∀ x ∈ Icc 0 L, HasDerivWithinAt g (field a b alpha m beta mu nu gamma (g x)) (Icc 0 L) x) ∧
      (∀ x ∈ Icc 0 L, (g x).1 = (g 0).1) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ (g x).2.1.1 ∧ 0 ≤ (g x).2.2.1) ∧
      (g 0).2.1.2 = 0 ∧ (g L).2.1.2 = 0 ∧ (g 0).2.2.2 = 0 ∧ (g L).2.2.2 = 0 := by
  let f := fun n x => point (chi n) ((p n).u x) ((p n).du x) ((p n).v x) ((p n).dv x)
  have hfc : ∀ n, ContinuousOn (f n) (Icc 0 L) := fun n =>
    continuousOn_const.prodMk ((((p n).continuous_u.prodMk (p n).continuous_du).prodMk
      ((s n).continuous_v.prodMk (s n).continuous_dv)))
  have hfd : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (f n) (field a b alpha m beta mu nu gamma (f n x)) x :=
    fun n x hx => classical_derivative (p n) (s n) hm halpha.le (fun y hy => (hpos n y hy).le) hx
  obtain ⟨B,hB,hbound⟩ := uniform_state_bound chi p s hL ha hb halpha hm hm1 hbeta
    hmu hnu hgamma hgamma1 hchi hpos hnonconst
  have hH := continuous_field a b alpha m beta mu nu gamma halpha.le hm hgamma.le
  obtain ⟨g,phi,hphi,hgc,huni,hsrc,_,hderiv⟩ :=
    ClassicalODECompactness.exists_stationary_subsequence (field a b alpha m beta mu nu gamma)
      hH hL.le f hfc hfd hbound
  have hwhole := ClassicalODECompactness.derivativeWithin_closed_interval hgc
    (hH.comp_continuousOn hgc) hderiv
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl,hL.le⟩
  have h1 : L ∈ Icc 0 L := ⟨hL.le,le_rfl⟩
  have hchic : Continuous (fun z : State => z.1) := by fun_prop
  have huc : Continuous (fun z : State => z.2.1.1) := by fun_prop
  have hvc : Continuous (fun z : State => z.2.2.1) := by fun_prop
  have hchilim : ∀ x ∈ Icc 0 L, Tendsto (fun n => chi (phi n)) atTop (nhds (g x).1) := by
    intro x hx
    exact (hchic.tendsto (g x)).comp (huni.tendsto_at hx)
  have hconst : ∀ x ∈ Icc 0 L, (g x).1 = (g 0).1 := fun x hx =>
    tendsto_nhds_unique (hchilim x hx) (hchilim 0 h0)
  have hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ (g x).2.1.1 ∧ 0 ≤ (g x).2.2.1 := by
    intro x hx
    constructor
    · exact isClosed_Ici.mem_of_tendsto ((huc.tendsto (g x)).comp (huni.tendsto_at hx))
        (Eventually.of_forall (fun n => (hpos (phi n) x hx).le))
    · exact isClosed_Ici.mem_of_tendsto ((hvc.tendsto (g x)).comp (huni.tendsto_at hx))
        (Eventually.of_forall (fun n => (s (phi n)).nonnegative_v x hx))
  have htrace (q : State → ℝ) (hq : Continuous q) (x : ℝ) (hx : x ∈ Icc 0 L)
      (hz : ∀ n, q (f n x) = 0) : q (g x) = 0 := by
    have h := (hq.tendsto (g x)).comp (huni.tendsto_at hx)
    change Tendsto (fun n => q (f (phi n) x)) atTop (nhds (q (g x))) at h
    simp only [hz] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine ⟨g,phi,hphi,hgc,huni,hsrc,hwhole,hconst,hnonneg,?_,?_,?_,?_⟩
  · exact htrace (fun z => z.2.1.2) (by fun_prop) 0 h0 (fun n => (p n).neumann_u_left)
  · exact htrace (fun z => z.2.1.2) (by fun_prop) L h1 (fun n => (p n).neumann_u_right)
  · exact htrace (fun z => z.2.2.2) (by fun_prop) 0 h0 (fun n => (p n).neumann_v_left)
  · exact htrace (fun z => z.2.2.2) (by fun_prop) L h1 (fun n => (p n).neumann_v_right)

end
end ChemotaxisBifurcation.StationaryCompactness
