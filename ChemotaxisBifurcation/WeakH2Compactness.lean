module
public import ChemotaxisBifurcation.WeakH2PhaseSpace
public import ChemotaxisBifurcation.ClassicalMinimalCompactness
public import ChemotaxisBifurcation.PhysicalClassicalAdapter

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.WeakH2Compactness
open Real Set MeasureTheory Filter Topology WeakDerivative1D WeakH2PhaseSpace
noncomputable section

/-- The exact raw L2 difference norm of actual continuous representatives. -/
theorem raw_L2_difference {L : ℝ} (hL : 0 < L) (u v : ℝ → ℝ)
    (hu : MemLp u 2 (intervalMeasure L)) (hv : MemLp v 2 (intervalMeasure L))
    (huc : ContinuousOn u (Icc 0 L)) (hvc : ContinuousOn v (Icc 0 L)) :
    ‖hu.toLp u-hv.toLp v‖ = sqrt (∫ x in Icc 0 L, (u x-v x)^2) := by
  rw [← MemLp.toLp_sub hu hv]
  have hh := WeakH2Embedding.norm_functionToLp_eq_raw hL (hu.sub hv) (huc.sub hvc)
    (Eventually.of_forall (fun _ _ => rfl))
  rw [← hh]
  change ‖SignalWeakSource.functionToLp (fun x => u x-v x) (huc.sub hvc) 2‖ = _
  rw [ClassicalSobolevDictionary.functionToLp_sub u v huc hvc,
    ClassicalSobolevDictionary.norm_L2_difference hL.le u v huc hvc]

/-- Actual uniform convergence implies norm convergence in the raw L2
space used by the genuine weak-H2 phase, not a surrogate norm variable. -/
theorem raw_L2_tendsto {L : ℝ} (hL : 0 < L) (u : ℕ → ℝ → ℝ) (v : ℝ → ℝ)
    (hu : ∀ n, MemLp (u n) 2 (intervalMeasure L)) (hv : MemLp v 2 (intervalMeasure L))
    (huc : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hvc : ContinuousOn v (Icc 0 L))
    (hconv : TendstoUniformlyOn u v atTop (Icc 0 L)) :
    Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he : (fun n => ‖(hu n).toLp (u n)-hv.toLp v‖) =
      (fun n => UniformComponentH2.l2Distance L (u n) v) := by
    funext n
    exact raw_L2_difference hL (u n) v (hu n) hv (huc n) hvc
  rw [he]
  exact UniformComponentH2.l2Distance_tendsto huc hvc hconv

/-- Three actual uniform component convergences produce genuine norm-topology
convergence of the full weak-H2 Neumann phase points. -/
theorem of_H2_tendsto {L : ℝ} (hL : 0 < L) (u du ddu : ℕ → ℝ → ℝ) (v dv ddv : ℝ → ℝ)
    (h : ∀ n, H2 L (u n) (du n) (ddu n)) (k : H2 L v dv ddv)
    (hN : ∀ n, NeumannTrace L (du n)) (kN : NeumannTrace L dv)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hdu : ∀ n, ContinuousOn (du n) (Icc 0 L))
    (hddu : ∀ n, ContinuousOn (ddu n) (Icc 0 L))
    (hv : ContinuousOn v (Icc 0 L)) (hdv : ContinuousOn dv (Icc 0 L))
    (hddv : ContinuousOn ddv (Icc 0 L))
    (h0 : TendstoUniformlyOn u v atTop (Icc 0 L))
    (h1 : TendstoUniformlyOn du dv atTop (Icc 0 L))
    (h2 : TendstoUniformlyOn ddu ddv atTop (Icc 0 L)) :
    Tendsto (fun n => of_H2 hL (h n) (hN n)) atTop (𝓝 (of_H2 hL k kN)) := by
  apply tendsto_subtype_rng.mpr
  exact (raw_L2_tendsto hL u v (fun n => (h n).memLp) k.memLp hu hv h0).prodMk_nhds
    ((raw_L2_tendsto hL du dv (fun n => (h n).memLp_deriv) k.memLp_deriv hdu hdv h1).prodMk_nhds
      (raw_L2_tendsto hL ddu ddv (fun n => (h n).memLp_deriv2) k.memLp_deriv2 hddu hddv h2))

/-- A phase point from ordinary actual classical population data. -/
def phaseOfClassical {L a b alpha chi m beta : ℝ} (hL : 0 < L)
    (p : StationaryMassIdentity.ClassicalProfile L a b alpha chi m beta)
    (hc : ContinuousOn p.ddu (Icc 0 L)) : Space L hL :=
  of_H2 hL (ClassicalSobolevDictionary.classical_H2 hL p.continuous_u p.continuous_du hc
    p.derivative_u p.derivative_du)
    (ClassicalSobolevDictionary.classical_neumann_trace p.continuous_du p.neumann_u_left p.neumann_u_right)

/-- The genuine weak-H2 phase point of an actual limiting classical profile. -/
def phaseOfPhysical {L a b alpha chi m beta : ℝ} (hL : 0 < L)
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta) : Space L hL :=
  of_H2 hL (ClassicalSobolevDictionary.classical_H2 hL
    (fun x hx => (q.derivative_u x hx).continuousWithinAt)
    (fun x hx => (q.derivative_du x hx).continuousWithinAt) q.continuous_ddu
    (fun x hx => (q.derivative_u x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => (q.derivative_du x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)))
    (ClassicalSobolevDictionary.classical_neumann_trace
      (fun x hx => (q.derivative_du x hx).continuousWithinAt) q.neumann_left q.neumann_right)

/-- Actual classical component convergence maps to the genuine weak-H2 norm topology. -/
theorem phaseOfClassical_tendsto {L a b alpha m beta chiBar : ℝ} {chi : ℕ → ℝ}
    (hL : 0 < L)
    (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (hc : ∀ n, ContinuousOn (p n).ddu (Icc 0 L))
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chiBar m beta)
    (h0 : TendstoUniformlyOn (fun n => (p n).u) q.u atTop (Icc 0 L))
    (h1 : TendstoUniformlyOn (fun n => (p n).du) q.du atTop (Icc 0 L))
    (h2 : TendstoUniformlyOn (fun n => (p n).ddu) q.ddu atTop (Icc 0 L)) :
    Tendsto (fun n => phaseOfClassical hL (p n) (hc n)) atTop (𝓝 (phaseOfPhysical hL q)) := by
  unfold phaseOfClassical phaseOfPhysical
  apply of_H2_tendsto hL
  · exact fun n => (p n).continuous_u
  · exact fun n => (p n).continuous_du
  · exact hc
  · exact fun x hx => (q.derivative_u x hx).continuousWithinAt
  · exact fun x hx => (q.derivative_du x hx).continuousWithinAt
  · exact q.continuous_ddu
  · exact h0
  · exact h1
  · exact h2

/-- Actual bounded-sensitivity stationary families have a genuine parameter
and weak-H2 norm convergent subsequence to an original stationary PDE profile.
No compactness, phase convergence or PDE limit is assumed. -/
theorem logistic_norm_subsequence {L a b alpha m beta mu nu gamma X : ℝ}
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
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun n => (chi (phi n),phaseOfClassical hL (p (phi n)) (hDDU (phi n))))
        atTop (𝓝 (chiBar,phaseOfPhysical hL q)) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0 := by
  obtain ⟨chiBar,q,phi,hphi,hcl,hU,hDU,_,_,hDDUlim,_,hnn,hN0,hNL,heq⟩ :=
    ClassicalStationaryC2Limit.exists_classical_C2_stationary_limit chi p s hL ha hb halpha
      hm hm1 hbeta hmu hnu hgamma hgamma1 hDDU hDDV hchi hpos hnonconst
  have hphase := phaseOfClassical_tendsto hL (fun n => p (phi n))
    (fun n => hDDU (phi n)) q hU hDU hDDUlim
  exact ⟨chiBar,q,phi,hphi,hcl.prodMk_nhds hphase,hnn,hN0,hNL,heq⟩

/-- Actual bounded-sensitivity stationary families have a genuine parameter
and weak-H2 norm convergent subsequence to an original stationary PDE profile.
No compactness, phase convergence or PDE limit is assumed. -/
theorem minimal_norm_subsequence {L alpha m beta mu nu gamma X uStar : ℝ}
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
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun n => (chi (phi n),phaseOfClassical hL (p (phi n)) (hDDU (phi n))))
        atTop (𝓝 (chiBar,phaseOfPhysical hL q)) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      (∫ x in (0 : ℝ)..L, q.u x) = L*uStar ∧
      ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0 := by
  obtain ⟨chiBar,q,phi,hphi,hcl,hU,hDU,_,_,hDDUlim,_,_,_,hnn,hN0,hNL,hmasslim,heq⟩ :=
    ClassicalMinimalCompactness.exists_classical_componentH2_stationary_limit chi p s hL halpha
      hm hm1 hbeta hmu hnu hgamma hgamma1 hDDU hDDV hchi hpos hmass
  have hphase := phaseOfClassical_tendsto hL (fun n => p (phi n))
    (fun n => hDDU (phi n)) q hU hDU hDDUlim
  exact ⟨chiBar,q,phi,hphi,hcl.prodMk_nhds hphase,hnn,hN0,hNL,hmasslim,heq⟩

/-- The physical adapter preserves the genuine phase point exactly. -/
theorem phaseOfAdapter {L a b alpha chi m beta : ℝ} (hL : 0 < L)
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
    (hm : 1 ≤ m) (hv : ∀ x ∈ Icc 0 L, 0 ≤ q.v x) (hN0 : q.dv 0 = 0) (hNL : q.dv L = 0) :
    phaseOfClassical hL (PhysicalClassicalAdapter.toClassicalProfile q hm hv hN0 hNL)
      q.continuous_ddu = phaseOfPhysical hL q := rfl

/-- Genuine parameter/weak-H2 norm compactness for literal physical classical
stationary families; adapter flux/derivative data are constructed internally. -/
theorem logistic_physical_norm_subsequence {L a b alpha m beta mu nu gamma X : ℝ}
    (chi : ℕ → ℝ)
    (Q : ∀ n, PhysicalStrongPositivity.StationaryProfile L a b alpha (chi n) m beta)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha)
    (hv : ∀ n x, x ∈ Icc 0 L → 0 ≤ (Q n).v x)
    (hN0 : ∀ n, (Q n).dv 0 = 0) (hNL : ∀ n, (Q n).dv L = 0)
    (heq : ∀ n x, x ∈ Ioo 0 L → (Q n).ddv x-mu*(Q n).v x+nu*(Q n).u x^gamma = 0)
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (Q n).u x)
    (hnonconst : ∀ n, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, (Q n).u x ≠ (Q n).u y) :
    ∃ chiBar : ℝ,
    ∃ q : PhysicalStrongPositivity.StationaryProfile L a b alpha chiBar m beta,
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun n => (chi (phi n),phaseOfPhysical hL (Q (phi n))))
        atTop (𝓝 (chiBar,phaseOfPhysical hL q)) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0 := by
  let p := fun n => PhysicalClassicalAdapter.toClassicalProfile (Q n) hm (hv n) (hN0 n) (hNL n)
  let s := fun n => PhysicalClassicalAdapter.toSignalData (Q n) hm (hv n) (hN0 n) (hNL n) (heq n)
  obtain ⟨chiBar,q,phi,hphi,hconv,hnn,hqN0,hqNL,hqeq⟩ :=
    logistic_norm_subsequence chi p s hL ha hb halpha hm hm1 hbeta hmu hnu hgamma hgamma1
      (fun n => (Q n).continuous_ddu) (fun n => (Q n).continuous_ddv) hchi hpos hnonconst
  have hconv' : Tendsto (fun n => (chi (phi n),phaseOfPhysical hL (Q (phi n))))
      atTop (𝓝 (chiBar,phaseOfPhysical hL q)) := by
    simpa only [p,phaseOfAdapter] using hconv
  exact ⟨chiBar,q,phi,hphi,hconv',hnn,hqN0,hqNL,hqeq⟩

/-- Genuine parameter/weak-H2 norm compactness for literal physical classical
stationary families; adapter flux/derivative data are constructed internally. -/
theorem minimal_physical_norm_subsequence {L alpha m beta mu nu gamma X uStar : ℝ}
    (chi : ℕ → ℝ)
    (Q : ∀ n, PhysicalStrongPositivity.StationaryProfile L 0 0 alpha (chi n) m beta)
    (hL : 0 < L) (halpha : 0 ≤ alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hv : ∀ n x, x ∈ Icc 0 L → 0 ≤ (Q n).v x)
    (hN0 : ∀ n, (Q n).dv 0 = 0) (hNL : ∀ n, (Q n).dv L = 0)
    (heq : ∀ n x, x ∈ Ioo 0 L → (Q n).ddv x-mu*(Q n).v x+nu*(Q n).u x^gamma = 0)
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (Q n).u x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, (Q n).u x = L*uStar) :
    ∃ chiBar : ℝ,
    ∃ q : PhysicalStrongPositivity.StationaryProfile L 0 0 alpha chiBar m beta,
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun n => (chi (phi n),phaseOfPhysical hL (Q (phi n))))
        atTop (𝓝 (chiBar,phaseOfPhysical hL q)) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      (∫ x in (0 : ℝ)..L, q.u x) = L*uStar ∧
      ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0 := by
  let p := fun n => PhysicalClassicalAdapter.toClassicalProfile (Q n) hm (hv n) (hN0 n) (hNL n)
  let s := fun n => PhysicalClassicalAdapter.toSignalData (Q n) hm (hv n) (hN0 n) (hNL n) (heq n)
  obtain ⟨chiBar,q,phi,hphi,hconv,hnn,hqN0,hqNL,hmasslim,hqeq⟩ :=
    minimal_norm_subsequence chi p s hL halpha hm hm1 hbeta hmu hnu hgamma hgamma1
      (fun n => (Q n).continuous_ddu) (fun n => (Q n).continuous_ddv) hchi hpos hmass
  have hconv' : Tendsto (fun n => (chi (phi n),phaseOfPhysical hL (Q (phi n))))
      atTop (𝓝 (chiBar,phaseOfPhysical hL q)) := by
    simpa only [p,phaseOfAdapter] using hconv
  exact ⟨chiBar,q,phi,hphi,hconv',hnn,hqN0,hqNL,hmasslim,hqeq⟩

/-- The actual population phase point realizes its original classical profile. -/
theorem profile_phaseOfClassical {L a b alpha chi m beta : ℝ} (hL : 0 < L)
    (p : StationaryMassIdentity.ClassicalProfile L a b alpha chi m beta)
    (hc : ContinuousOn p.ddu (Icc 0 L)) :
    ∀ x : Icc (0 : ℝ) L, profileCLM hL (phaseOfClassical hL p hc) x = p.u x := by
  unfold phaseOfClassical
  exact profile_of_H2 hL _ _ p.continuous_u

theorem profile_phaseOfPhysical {L a b alpha chi m beta : ℝ} (hL : 0 < L)
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta) :
    ∀ x : Icc (0 : ℝ) L, profileCLM hL (phaseOfPhysical hL q) x = q.u x := by
  unfold phaseOfPhysical
  exact profile_of_H2 hL _ _ (fun x hx => (q.derivative_u x hx).continuousWithinAt)

end
end ChemotaxisBifurcation.WeakH2Compactness
