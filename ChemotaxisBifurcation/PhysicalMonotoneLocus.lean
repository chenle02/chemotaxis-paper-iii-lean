module
public import ChemotaxisBifurcation.PhysicalSignalTopology
public import ChemotaxisBifurcation.PhysicalSineDecay

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.PhysicalMonotoneLocus
open Real Set MeasureTheory Filter Topology MonotoneLocus MonotoneLocusGeneral GlobalBranch
noncomputable section

/-- Literal physical minimal stationary profiles supply the general-mobility
first-order stationary ODE used by the monotone-locus proof. Every function is
preserved on the physical interval; no ODE/flux/sign conclusion is assumed. -/
theorem stationarySolution_of_physical {L chi m beta mu nu gamma : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L 0 0 0 chi m beta)
    (hL : 0 < L) (hm : 1 ≤ m) (hgamma : 0 ≤ gamma)
    {u v y : ℝ → ℝ}
    (hU : ∀ x ∈ Icc 0 L, q.u x = u x)
    (hV : ∀ x ∈ Icc 0 L, q.v x = v x)
    (hY : ∀ x ∈ Icc 0 L, q.dv x = y x)
    (hu : ∀ x ∈ Icc 0 L, 0 < q.u x) (hv : ∀ x ∈ Icc 0 L, 0 ≤ q.v x)
    (hN0 : q.dv 0 = 0) (hNL : q.dv L = 0)
    (heq : ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) :
    MonotoneLocusGeneral.StationarySolution chi mu nu gamma beta m L u v y := by
  have hs := PhysicalSineDecay.toStationarySolution q hL hm hgamma hu hv hN0 hNL heq
  refine {
    u_pos := ?_
    v_pos := ?_
    deriv_u := ?_
    deriv_v := ?_
    deriv_y := ?_
    bc_left := ?_
    bc_right := ?_ }
  · intro x hx; rw [← hU x hx]; exact hu x hx
  · intro x hx; rw [← hV x hx]; linarith [hv x hx]
  · intro x hx
    have h := (hs.deriv_u x hx).congr (fun t ht => (hU t ht).symm) (hU x hx).symm
    rwa [hU x hx,hV x hx,hY x hx] at h
  · intro x hx
    have h := (hs.deriv_v x hx).congr (fun t ht => (hV t ht).symm) (hV x hx).symm
    rwa [hY x hx] at h
  · intro x hx
    have h := (hs.deriv_y x hx).congr (fun t ht => (hY t ht).symm) (hY x hx).symm
    rwa [hU x hx,hV x hx] at h
  · rw [← hY 0 ⟨le_rfl,hL.le⟩]; exact hN0
  · rw [← hY L ⟨hL.le,le_rfl⟩]; exact hNL

section Locus
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [T1Space E]

/-- Physical decreasing-locus clopenness with the ODE and signal C2 topology
premises discharged; local branch/constant-limit representations remain explicit. -/
theorem isClopen_decreasingLocus_of_physical (prof : E →+ (ℝ → ℝ)) {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hm : 1 ≤ m) (hgamma : 0 ≤ γ) (hmu : 0 < μ)
    (profC : E → C(Icc (0 : ℝ) L, ℝ)) (hProf : Continuous profC)
    (hProfRep : ∀ e (x : Icc (0 : ℝ) L), profC e x = prof e x)
    (data : ∀ z ∈ C, PhysicalStrongPositivity.StationaryProfile L 0 0 0 z.1 m β)
    (hURep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).u x = prof z.2 x)
    (hVRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).v x = sig z x)
    (hYRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).dv x = sigx z x)
    (hpos : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 < (data z hz).u x)
    (hV : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hN0 : ∀ z (hz : z ∈ C), (data z hz).dv 0 = 0)
    (hNL : ∀ z (hz : z ∈ C), (data z hz).dv L = 0)
    (heq : ∀ z (hz : z ∈ C) x, x ∈ Ioo 0 L →
      (data z hz).ddv x-μ*(data z hz).v x+ν*(data z hz).u x^γ = 0)
    (hConst : ∀ p ∈ C, MonotoneLocusGeneral.IsConstOn (prof p.2) L →
      p ∈ closure (C ∩ {q | StrictAntiOn (prof q.2) (Icc 0 L)}) →
      ConstLimitRep prof L (C ∩ {q | StrictAntiOn (prof q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch prof L C pStar 1) :
    IsClopen (((↑) : C → ℝ × E) ⁻¹' DecreasingLocus prof L pStar) := by
  have hSol : ∀ z ∈ C, MonotoneLocusGeneral.StationarySolution z.1 μ ν γ β m L (prof z.2) (sig z) (sigx z) := by
    intro z hz
    exact stationarySolution_of_physical (data z hz) hL hm hgamma
      (hURep z hz) (hVRep z hz) (hYRep z hz) (hpos z hz) (hV z hz) (hN0 z hz) (hNL z hz) (heq z hz)
  have hPt : ∀ x ∈ Icc 0 L, ContinuousOn (fun z : ℝ × E => prof z.2 x) C := by
    intro x hx
    have hc : Continuous (fun z : ℝ × E => profC z.2 ⟨x,hx⟩) := (continuous_eval_const (⟨x,hx⟩ : Icc (0 : ℝ) L)).comp (hProf.comp continuous_snd)
    have he : (fun z : ℝ × E => profC z.2 ⟨x,hx⟩) = fun z => prof z.2 x := by
      funext z; exact hProfRep z.2 ⟨x,hx⟩
    rw [he] at hc
    exact hc.continuousOn
  have hC2 : ∀ p ∈ C, p ≠ pStar → SignalC2Close prof sig μ ν γ L C p := by
    intro p hp _
    apply PhysicalSignalTopology.signalC2Close_of_physical_profiles hL hmu prof profC hProf hProfRep sig hp
      data hURep hVRep hN0 hNL heq
    intro x hx
    rw [← hURep p hp x hx]
    exact hpos p hp x hx
  exact MonotoneLocusGeneral.isClopen_decreasingLocus prof hL sig sigx hχ hSol hPt hC2 hConst hStar

/-- Corresponding physical increasing-locus clopenness. -/
theorem isClopen_increasingLocus_of_physical (prof : E →+ (ℝ → ℝ)) {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hm : 1 ≤ m) (hgamma : 0 ≤ γ) (hmu : 0 < μ)
    (profC : E → C(Icc (0 : ℝ) L, ℝ)) (hProf : Continuous profC)
    (hProfRep : ∀ e (x : Icc (0 : ℝ) L), profC e x = prof e x)
    (data : ∀ z ∈ C, PhysicalStrongPositivity.StationaryProfile L 0 0 0 z.1 m β)
    (hURep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).u x = prof z.2 x)
    (hVRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).v x = sig z x)
    (hYRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).dv x = sigx z x)
    (hpos : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 < (data z hz).u x)
    (hV : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hN0 : ∀ z (hz : z ∈ C), (data z hz).dv 0 = 0)
    (hNL : ∀ z (hz : z ∈ C), (data z hz).dv L = 0)
    (heq : ∀ z (hz : z ∈ C) x, x ∈ Ioo 0 L →
      (data z hz).ddv x-μ*(data z hz).v x+ν*(data z hz).u x^γ = 0)
    (hConst : ∀ p ∈ C, MonotoneLocusGeneral.IsConstOn (prof p.2) L →
      p ∈ closure (C ∩ {q | StrictMonoOn (prof q.2) (Icc 0 L)}) →
      ConstLimitRep prof L (C ∩ {q | StrictMonoOn (prof q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch prof L C pStar (-1)) :
    IsClopen (((↑) : C → ℝ × E) ⁻¹' IncreasingLocus prof L pStar) := by
  have hSol : ∀ z ∈ C, MonotoneLocusGeneral.StationarySolution z.1 μ ν γ β m L (prof z.2) (sig z) (sigx z) := by
    intro z hz
    exact stationarySolution_of_physical (data z hz) hL hm hgamma
      (hURep z hz) (hVRep z hz) (hYRep z hz) (hpos z hz) (hV z hz) (hN0 z hz) (hNL z hz) (heq z hz)
  have hPt : ∀ x ∈ Icc 0 L, ContinuousOn (fun z : ℝ × E => prof z.2 x) C := by
    intro x hx
    have hc : Continuous (fun z : ℝ × E => profC z.2 ⟨x,hx⟩) := (continuous_eval_const (⟨x,hx⟩ : Icc (0 : ℝ) L)).comp (hProf.comp continuous_snd)
    have he : (fun z : ℝ × E => profC z.2 ⟨x,hx⟩) = fun z => prof z.2 x := by
      funext z; exact hProfRep z.2 ⟨x,hx⟩
    rw [he] at hc
    exact hc.continuousOn
  have hC2 : ∀ p ∈ C, p ≠ pStar → SignalC2Close prof sig μ ν γ L C p := by
    intro p hp _
    apply PhysicalSignalTopology.signalC2Close_of_physical_profiles hL hmu prof profC hProf hProfRep sig hp
      data hURep hVRep hN0 hNL heq
    intro x hx
    rw [← hURep p hp x hx]
    exact hpos p hp x hx
  exact MonotoneLocusGeneral.isClopen_increasingLocus prof hL sig sigx hχ hSol hPt hC2 hConst hStar

/-- Actual decreasing-branch propagation; only the structural phase dictionary
and local bifurcation/constant-limit representations remain supplied. -/
theorem part3_strictAnti_of_physical (prof : E →+ (ℝ → ℝ)) {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hConn : IsPreconnected C) (hStarC : pStar ∈ C)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hm : 1 ≤ m) (hgamma : 0 ≤ γ) (hmu : 0 < μ)
    (profC : E → C(Icc (0 : ℝ) L, ℝ)) (hProf : Continuous profC)
    (hProfRep : ∀ e (x : Icc (0 : ℝ) L), profC e x = prof e x)
    (data : ∀ z ∈ C, PhysicalStrongPositivity.StationaryProfile L 0 0 0 z.1 m β)
    (hURep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).u x = prof z.2 x)
    (hVRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).v x = sig z x)
    (hYRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).dv x = sigx z x)
    (hpos : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 < (data z hz).u x)
    (hV : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hN0 : ∀ z (hz : z ∈ C), (data z hz).dv 0 = 0)
    (hNL : ∀ z (hz : z ∈ C), (data z hz).dv L = 0)
    (heq : ∀ z (hz : z ∈ C) x, x ∈ Ioo 0 L →
      (data z hz).ddv x-μ*(data z hz).v x+ν*(data z hz).u x^γ = 0)
    (hConst : ∀ p ∈ C, MonotoneLocusGeneral.IsConstOn (prof p.2) L →
      p ∈ closure (C ∩ {q | StrictAntiOn (prof q.2) (Icc 0 L)}) →
      ConstLimitRep prof L (C ∩ {q | StrictAntiOn (prof q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch prof L C pStar 1) :
    ∀ p ∈ C, p ≠ pStar → StrictAntiOn (prof p.2) (Icc 0 L) := by
  exact GlobalBranch.part3_strictAnti prof L hConn hStarC
    (isClopen_decreasingLocus_of_physical prof hL sig sigx hχ hm hgamma hmu profC hProf hProfRep
      data hURep hVRep hYRep hpos hV hN0 hNL heq hConst hStar)

/-- Corresponding actual increasing-branch propagation. -/
theorem part3_strictMono_of_physical (prof : E →+ (ℝ → ℝ)) {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hConn : IsPreconnected C) (hStarC : pStar ∈ C)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hm : 1 ≤ m) (hgamma : 0 ≤ γ) (hmu : 0 < μ)
    (profC : E → C(Icc (0 : ℝ) L, ℝ)) (hProf : Continuous profC)
    (hProfRep : ∀ e (x : Icc (0 : ℝ) L), profC e x = prof e x)
    (data : ∀ z ∈ C, PhysicalStrongPositivity.StationaryProfile L 0 0 0 z.1 m β)
    (hURep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).u x = prof z.2 x)
    (hVRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).v x = sig z x)
    (hYRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).dv x = sigx z x)
    (hpos : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 < (data z hz).u x)
    (hV : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hN0 : ∀ z (hz : z ∈ C), (data z hz).dv 0 = 0)
    (hNL : ∀ z (hz : z ∈ C), (data z hz).dv L = 0)
    (heq : ∀ z (hz : z ∈ C) x, x ∈ Ioo 0 L →
      (data z hz).ddv x-μ*(data z hz).v x+ν*(data z hz).u x^γ = 0)
    (hConst : ∀ p ∈ C, MonotoneLocusGeneral.IsConstOn (prof p.2) L →
      p ∈ closure (C ∩ {q | StrictMonoOn (prof q.2) (Icc 0 L)}) →
      ConstLimitRep prof L (C ∩ {q | StrictMonoOn (prof q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch prof L C pStar (-1)) :
    ∀ p ∈ C, p ≠ pStar → StrictMonoOn (prof p.2) (Icc 0 L) := by
  exact GlobalBranch.part3_strictMono prof L hConn hStarC
    (isClopen_increasingLocus_of_physical prof hL sig sigx hχ hm hgamma hmu profC hProf hProfRep
      data hURep hVRep hYRep hpos hV hN0 hNL heq hConst hStar)

end Locus
end
end ChemotaxisBifurcation.PhysicalMonotoneLocus
