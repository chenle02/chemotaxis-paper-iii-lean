module
public import ChemotaxisBifurcation.ClassicalStationaryLimit

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalStationaryC2Limit
open Real Set MeasureTheory Filter Topology StationaryODEState
noncomputable section

/-- The actual second derivatives equal the continuous physical ODE field,
including endpoints when their chosen representatives are continuous there. -/
theorem field_eq_actual_derivatives {L a b alpha chi m beta mu nu gamma : ℝ}
    (p : StationaryMassIdentity.ClassicalProfile L a b alpha chi m beta)
    (s : ClassicalLogisticEstimates.SignalData p mu nu gamma)
    (hL : 0 < L) (hm : 1 ≤ m) (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma)
    (hu : ∀ x ∈ Icc 0 L, 0 ≤ p.u x)
    (hDDU : ContinuousOn p.ddu (Icc 0 L))
    (hDDV : ContinuousOn s.ddv (Icc 0 L)) :
    ∀ x ∈ Icc 0 L,
      field a b alpha m beta mu nu gamma (point chi (p.u x) (p.du x) (p.v x) (p.dv x)) =
        point 0 (p.du x) (p.ddu x) (p.dv x) (s.ddv x) := by
  have hc : ContinuousOn (fun x => field a b alpha m beta mu nu gamma
      (point chi (p.u x) (p.du x) (p.v x) (p.dv x))) (Icc 0 L) := (continuous_field a b alpha m beta mu nu gamma halpha hm hgamma).comp_continuousOn
    (continuousOn_const.prodMk ((p.continuous_u.prodMk p.continuous_du).prodMk
      (s.continuous_v.prodMk s.continuous_dv)))
  have hc' : ContinuousOn (fun x => point 0 (p.du x) (p.ddu x) (p.dv x) (s.ddv x)) (Icc 0 L) :=
    continuousOn_const.prodMk ((p.continuous_du.prodMk hDDU).prodMk (s.continuous_dv.prodMk hDDV))
  have hclosed := isClosed_Icc.isClosed_eq hc hc'
  have hin : Ioo 0 L ⊆ {x ∈ Icc 0 L |
      field a b alpha m beta mu nu gamma (point chi (p.u x) (p.du x) (p.v x) (p.dv x)) =
        point 0 (p.du x) (p.ddu x) (p.dv x) (s.ddv x)} := by
    intro x hx
    refine ⟨Ioo_subset_Icc_self hx,?_⟩
    exact (classical_derivative p s hm halpha hu hx).unique
      ((hasDerivAt_const x chi).prodMk
        (((p.derivative_u x hx).prodMk (p.derivative_du x hx)).prodMk
          ((p.derivative_v x hx).prodMk (s.derivative_dv x hx))))
  intro x hx
  have hmem : x ∈ closure (Ioo 0 L) := by rwa [closure_Ioo hL.ne]
  exact (closure_minimal hin hclosed hmem).2

/-- Actual bounded-sensitivity classical logistic stationary solutions have
a C1-convergent population/signal subsequence whose limit solves both original
stationary equations, with continuous second derivatives and Neumann data.
No extraction, elliptic estimate, Schauder theorem or limiting PDE is assumed. -/
theorem exists_classical_C2_stationary_limit {L a b alpha m beta mu nu gamma X : ℝ}
    (chi : ℕ → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha)
    (hDDU : ∀ n, ContinuousOn (p n).ddu (Icc 0 L))
    (hDDV : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hnonconst : ∀ n, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, (p n).u x ≠ (p n).u y) :
    ∃ chiBar : ℝ,
    ∃ q : PhysicalStrongPositivity.StationaryProfile L a b alpha chiBar m beta,
    ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (fun n => chi (phi n)) atTop (nhds chiBar) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).u) q.u atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).du) q.du atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).v) q.v atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).dv) q.dv atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).ddu) q.ddu atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (s (phi n)).ddv) q.ddv atTop (Icc 0 L) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0 := by
  obtain ⟨g,phi,hphi,hgc,huni,hsrc,hderiv,hconst,hnn,hU0,hUL,hV0,hVL⟩ :=
    StationaryCompactness.exists_augmented_limit chi p s hL ha hb halpha hm hm1 hbeta
      hmu hnu hgamma hgamma1 hchi hpos hnonconst
  let q := StationaryLimitProfile.toPopulationProfile g hgc hderiv hconst hnn hm halpha.le hgamma.le hU0 hUL
  have hPair := uniformContinuous_snd.comp_tendstoUniformlyOn huni
  have hU := uniformContinuous_fst.comp_tendstoUniformlyOn hPair
  have hV := uniformContinuous_snd.comp_tendstoUniformlyOn hPair
  have hUc := uniformContinuous_fst.comp_tendstoUniformlyOn hU
  have hDUc := uniformContinuous_snd.comp_tendstoUniformlyOn hU
  have hVc := uniformContinuous_fst.comp_tendstoUniformlyOn hV
  have hDVc := uniformContinuous_snd.comp_tendstoUniformlyOn hV
  have hchic : Continuous (fun z : State => z.1) := by fun_prop
  have hchil := (hchic.tendsto (g 0)).comp (huni.tendsto_at ⟨le_rfl,hL.le⟩)
  have hfield := fun n x hx => field_eq_actual_derivatives (p n) (s n) hL hm halpha.le hgamma.le
    (fun y hy => (hpos n y hy).le) (hDDU n) (hDDV n) x hx
  have hsrcPair := uniformContinuous_snd.comp_tendstoUniformlyOn hsrc
  have hDDUc := uniformContinuous_snd.comp_tendstoUniformlyOn
    (uniformContinuous_fst.comp_tendstoUniformlyOn hsrcPair)
  have hDDVc := uniformContinuous_snd.comp_tendstoUniformlyOn
    (uniformContinuous_snd.comp_tendstoUniformlyOn hsrcPair)
  have hDU : TendstoUniformlyOn (fun n => (p (phi n)).ddu) q.ddu atTop (Icc 0 L) := by
    apply hDDUc.congr
    · exact Eventually.of_forall (fun n x hx => (congrArg (fun z : State => z.2.1.2) (hfield (phi n) x hx)))
  have hDV : TendstoUniformlyOn (fun n => (s (phi n)).ddv) q.ddv atTop (Icc 0 L) := by
    apply hDDVc.congr
    · exact Eventually.of_forall (fun n x hx => (congrArg (fun z : State => z.2.2.2) (hfield (phi n) x hx)))
  refine ⟨(g 0).1,q,phi,hphi,hchil,hUc,hDUc,hVc,hDVc,hDU,hDV,hnn,hV0,hVL,?_⟩
  intro x hx
  exact StationaryLimitProfile.signal_identity mu nu gamma g x

end
end ChemotaxisBifurcation.ClassicalStationaryC2Limit
