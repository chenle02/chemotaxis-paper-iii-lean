module
public import ChemotaxisBifurcation.StationaryLimitProfile

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalStationaryLimit
open Real Set MeasureTheory Filter Topology StationaryODEState
noncomputable section

/-- Actual bounded-sensitivity classical logistic stationary solutions have
a C1-convergent population/signal subsequence whose limit solves both original
stationary equations, with continuous second derivatives and Neumann data.
No extraction, elliptic estimate, Schauder theorem or limiting PDE is assumed. -/
theorem exists_classical_stationary_limit {L a b alpha m beta mu nu gamma X : ℝ}
    (chi : ℕ → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha)
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
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0 := by
  obtain ⟨g,phi,hphi,hgc,huni,_,hderiv,hconst,hnn,hU0,hUL,hV0,hVL⟩ :=
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
  refine ⟨(g 0).1,q,phi,hphi,hchil,hUc,hDUc,hVc,hDVc,hnn,hV0,hVL,?_⟩
  intro x hx
  exact StationaryLimitProfile.signal_identity mu nu gamma g x

end
end ChemotaxisBifurcation.ClassicalStationaryLimit
