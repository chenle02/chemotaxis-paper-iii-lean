module
public import ChemotaxisBifurcation.ClassicalSobolevDictionary
public import ChemotaxisBifurcation.ClassicalMinimalCompactness

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalBoundedCompactness
open Real Set MeasureTheory Filter Topology ClassicalSobolevDictionary UniformComponentH2
noncomputable section

/-- Actual bounded-sensitivity stationary solutions have a subsequence converging
in the literal standard C2 norm to an original stationary PDE solution, with
actual weak H2 membership and Neumann traces. No compactness or PDE limit is assumed. -/
theorem logistic_stationary_limit {L a b alpha m beta mu nu gamma X : ℝ}
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
      Tendsto (fun n => componentH2Distance L (p (phi n)).u (p (phi n)).du (p (phi n)).ddu
        q.u q.du q.ddu) atTop (nhds 0) ∧
      Tendsto (fun n => componentH2Distance L (p (phi n)).v (p (phi n)).dv (s (phi n)).ddv
        q.v q.dv q.ddv) atTop (nhds 0) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      (∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) ∧
    (WeakDerivative1D.H2 L q.u q.du q.ddu ∧ WeakDerivative1D.H2 L q.v q.dv q.ddv) ∧
      WeakDerivative1D.NeumannTrace L q.du ∧ WeakDerivative1D.NeumannTrace L q.dv ∧
      Tendsto (fun n => c2Distance L (p (phi n)).u (p (phi n)).du (p (phi n)).ddu q.u q.du q.ddu) atTop (𝓝 0) ∧
      Tendsto (fun n => c2Distance L (p (phi n)).v (p (phi n)).dv (s (phi n)).ddv q.v q.dv q.ddv) atTop (𝓝 0) := by
  obtain ⟨chiBar,q,phi,hphi,hcl,hu,hdu,hv,hdv,hddu,hddv,hH2u,hH2v,hnn,hN0,hNL,heq⟩ :=
    UniformComponentH2.exists_classical_componentH2_stationary_limit chi p s hL ha hb halpha hm hm1 hbeta hmu hnu hgamma hgamma1 hDDU hDDV hchi hpos hnonconst
  have hqu : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
  have hqdu : ContinuousOn q.du (Icc 0 L) := fun x hx => (q.derivative_du x hx).continuousWithinAt
  have hqv : ContinuousOn q.v (Icc 0 L) := fun x hx => (q.derivative_v x hx).continuousWithinAt
  have hqdv : ContinuousOn q.dv (Icc 0 L) := fun x hx => (q.derivative_dv x hx).continuousWithinAt
  refine ⟨chiBar,q,phi,hphi,hcl,hu,hdu,hv,hdv,hddu,hddv,hH2u,hH2v,hnn,hN0,hNL,heq,?_,?_,?_,?_,?_⟩
  · constructor
    · exact classical_H2 hL hqu hqdu q.continuous_ddu
        (fun x hx => (q.derivative_u x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
        (fun x hx => (q.derivative_du x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    · exact classical_H2 hL hqv hqdv q.continuous_ddv
        (fun x hx => (q.derivative_v x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
        (fun x hx => (q.derivative_dv x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
  · exact classical_neumann_trace hqdu q.neumann_left q.neumann_right
  · exact classical_neumann_trace hqdv hN0 hNL
  · exact c2Distance_tendsto hL.le _ _ _ _ _ _
      (fun n => (p (phi n)).continuous_u) (fun n => (p (phi n)).continuous_du)
      (fun n => hDDU (phi n)) hqu hqdu q.continuous_ddu hu hdu hddu
  · exact c2Distance_tendsto hL.le _ _ _ _ _ _
      (fun n => (s (phi n)).continuous_v) (fun n => (s (phi n)).continuous_dv)
      (fun n => hDDV (phi n)) hqv hqdv q.continuous_ddv hv hdv hddv

/-- Actual bounded-sensitivity stationary solutions have a subsequence converging
in the literal standard C2 norm to an original stationary PDE solution, with
actual weak H2 membership and Neumann traces. No compactness or PDE limit is assumed. -/
theorem minimal_stationary_limit {L alpha m beta mu nu gamma X uStar : ℝ}
    (chi : ℕ → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L 0 0 alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (halpha : 0 ≤ alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hDDU : ∀ n, ContinuousOn (p n).ddu (Icc 0 L))
    (hDDV : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, (p n).u x = L*uStar) :
    ∃ chiBar : ℝ,
    ∃ q : PhysicalStrongPositivity.StationaryProfile L 0 0 alpha chiBar m beta,
    ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (fun n => chi (phi n)) atTop (nhds chiBar) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).u) q.u atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).du) q.du atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).v) q.v atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).dv) q.dv atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).ddu) q.ddu atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (s (phi n)).ddv) q.ddv atTop (Icc 0 L) ∧
      Tendsto (fun n => UniformComponentH2.componentH2Distance L (p (phi n)).u (p (phi n)).du (p (phi n)).ddu
        q.u q.du q.ddu) atTop (nhds 0) ∧
      Tendsto (fun n => UniformComponentH2.componentH2Distance L (p (phi n)).v (p (phi n)).dv (s (phi n)).ddv
        q.v q.dv q.ddv) atTop (nhds 0) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      (∫ x in (0 : ℝ)..L, q.u x) = L*uStar ∧
      (∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) ∧
    (WeakDerivative1D.H2 L q.u q.du q.ddu ∧ WeakDerivative1D.H2 L q.v q.dv q.ddv) ∧
      WeakDerivative1D.NeumannTrace L q.du ∧ WeakDerivative1D.NeumannTrace L q.dv ∧
      Tendsto (fun n => c2Distance L (p (phi n)).u (p (phi n)).du (p (phi n)).ddu q.u q.du q.ddu) atTop (𝓝 0) ∧
      Tendsto (fun n => c2Distance L (p (phi n)).v (p (phi n)).dv (s (phi n)).ddv q.v q.dv q.ddv) atTop (𝓝 0) := by
  obtain ⟨chiBar,q,phi,hphi,hcl,hu,hdu,hv,hdv,hddu,hddv,hH2u,hH2v,hnn,hN0,hNL,hmasslim,heq⟩ :=
    ClassicalMinimalCompactness.exists_classical_componentH2_stationary_limit chi p s hL halpha hm hm1 hbeta hmu hnu hgamma hgamma1 hDDU hDDV hchi hpos hmass
  have hqu : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
  have hqdu : ContinuousOn q.du (Icc 0 L) := fun x hx => (q.derivative_du x hx).continuousWithinAt
  have hqv : ContinuousOn q.v (Icc 0 L) := fun x hx => (q.derivative_v x hx).continuousWithinAt
  have hqdv : ContinuousOn q.dv (Icc 0 L) := fun x hx => (q.derivative_dv x hx).continuousWithinAt
  refine ⟨chiBar,q,phi,hphi,hcl,hu,hdu,hv,hdv,hddu,hddv,hH2u,hH2v,hnn,hN0,hNL,hmasslim,heq,?_,?_,?_,?_,?_⟩
  · constructor
    · exact classical_H2 hL hqu hqdu q.continuous_ddu
        (fun x hx => (q.derivative_u x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
        (fun x hx => (q.derivative_du x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    · exact classical_H2 hL hqv hqdv q.continuous_ddv
        (fun x hx => (q.derivative_v x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
        (fun x hx => (q.derivative_dv x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
  · exact classical_neumann_trace hqdu q.neumann_left q.neumann_right
  · exact classical_neumann_trace hqdv hN0 hNL
  · exact c2Distance_tendsto hL.le _ _ _ _ _ _
      (fun n => (p (phi n)).continuous_u) (fun n => (p (phi n)).continuous_du)
      (fun n => hDDU (phi n)) hqu hqdu q.continuous_ddu hu hdu hddu
  · exact c2Distance_tendsto hL.le _ _ _ _ _ _
      (fun n => (s (phi n)).continuous_v) (fun n => (s (phi n)).continuous_dv)
      (fun n => hDDV (phi n)) hqv hqdv q.continuous_ddv hv hdv hddv

end
end ChemotaxisBifurcation.ClassicalBoundedCompactness
