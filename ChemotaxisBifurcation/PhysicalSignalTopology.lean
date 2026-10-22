module
public import ChemotaxisBifurcation.SignalResponseContinuity
public import ChemotaxisBifurcation.MonotoneLocusGeneral

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.PhysicalSignalTopology
open Real Set MeasureTheory Filter Topology
noncomputable section

/-- The signal C2 topology premise of the monotone-locus consumer follows
from C0 continuity of the actual population representation and the actual
signal PDE. No signal-convergence or elliptic-response estimate is assumed.
The phase-space population embedding remains explicit structural data. -/
theorem signalC2Close_of_physical_profiles
    {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    {L a b alpha m beta mu nu gamma : ℝ}
    (hL : 0 < L) (hmu : 0 < mu)
    (prof : E →+ (ℝ → ℝ)) (profC : E → C(Icc (0 : ℝ) L, ℝ))
    (hProf : Continuous profC) (hProfRep : ∀ e (x : Icc (0 : ℝ) L), profC e x = prof e x)
    (sig : ℝ × E → ℝ → ℝ) {C : Set (ℝ × E)} {p : ℝ × E} (hp : p ∈ C)
    (data : ∀ z ∈ C, PhysicalStrongPositivity.StationaryProfile L a b alpha z.1 m beta)
    (hURep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).u x = prof z.2 x)
    (hVRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).v x = sig z x)
    (hN0 : ∀ z (hz : z ∈ C), (data z hz).dv 0 = 0)
    (hNL : ∀ z (hz : z ∈ C), (data z hz).dv L = 0)
    (heq : ∀ z (hz : z ∈ C) x, x ∈ Ioo 0 L →
      (data z hz).ddv x-mu*(data z hz).v x+nu*(data z hz).u x^gamma = 0)
    (hpos : ∀ x ∈ Icc 0 L, 0 < prof p.2 x) :
    MonotoneLocus.SignalC2Close prof sig mu nu gamma L C p := by
  let r := data p hp
  have hrc : ContinuousOn r.u (Icc 0 L) := fun x hx => (r.derivative_u x hx).continuousWithinAt
  have hrpos : ∀ x ∈ Icc 0 L, 0 < r.u x := by
    intro x hx; change 0 < (data p hp).u x; rw [hURep p hp x hx]; exact hpos x hx
  obtain ⟨xmin,hxmin,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hrc
  let A := r.u xmin/2
  have hA : 0 < A := half_pos (hrpos xmin hxmin)
  obtain ⟨B0,hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn hrc
  let B := max B0 0+1
  have hrange : ∀ x ∈ Icc 0 L, r.u x ∈ Icc A B := by
    intro x hx
    constructor
    · have hh : r.u xmin ≤ r.u x := hmin hx; dsimp [A]; linarith [hrpos xmin hxmin]
    · have hh : |r.u x| ≤ B0 := by simpa only [Real.norm_eq_abs] using hB0 x hx
      dsimp [B]; linarith [le_abs_self (r.u x),le_max_left B0 0]
  obtain ⟨K,hK,hpair⟩ := SignalResponseContinuity.exists_pair_bound L mu nu gamma A B hL hmu hA
  intro epsilon hepsilon
  let eta := min A (min 1 (epsilon/(K+1)))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hclose : ∀ᶠ z : ℝ × E in nhdsWithin p C, dist (profC z.2) (profC p.2) < eta := by
    exact (((hProf.comp continuous_snd).tendsto p).mono_left nhdsWithin_le_nhds).eventually
      (Metric.ball_mem_nhds _ heta)
  filter_upwards [hclose,self_mem_nhdsWithin] with z hzclose hz
  have hdist : ∀ x ∈ Icc 0 L, |(data z hz).u x-r.u x| ≤ eta := by
    intro x hx
    rw [hURep z hz x hx]
    change |prof z.2 x-(data p hp).u x| ≤ eta
    rw [hURep p hp x hx]
    have hh := ContinuousMap.dist_apply_le_dist (f := profC z.2) (g := profC p.2) ⟨x,hx⟩
    rw [hProfRep z.2 ⟨x,hx⟩,hProfRep p.2 ⟨x,hx⟩,Real.dist_eq] at hh
    exact (hh.trans_lt hzclose).le
  have hqrange : ∀ x ∈ Icc 0 L, (data z hz).u x ∈ Icc A B := by
    intro x hx
    have hh := abs_le.mp (hdist x hx)
    have hl : r.u xmin ≤ r.u x := hmin hx
    have hu : r.u x ≤ max B0 0 := by
      have hh' : |r.u x| ≤ B0 := by simpa only [Real.norm_eq_abs] using hB0 x hx
      exact (le_abs_self _).trans (hh'.trans (le_max_left _ _))
    have hEtaA : eta ≤ A := min_le_left _ _
    have hEta1 : eta ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    dsimp [A] at *
    constructor
    · linarith
    · dsimp [B]; linarith
  have hqpos : ∀ x ∈ Icc 0 L, 0 < (data z hz).u x := fun x hx => hA.trans_le (hqrange x hx).1
  have hbound := hpair (data z hz) r hqrange hrange (hN0 z hz) (hNL z hz) (hN0 p hp) (hNL p hp)
    (heq z hz) (heq p hp) eta heta.le hdist
  have hEta : eta ≤ epsilon/(K+1) := (min_le_right _ _).trans (min_le_right _ _)
  have hKe : K*eta ≤ epsilon := by
    have hh := (le_div_iff₀ (by linarith : 0 < K+1)).mp hEta
    nlinarith
  intro x hx
  have hh := (hbound x hx).2.trans hKe
  rw [SignalResponseContinuity.ddv_eq_rhs (data z hz) hL hqpos (heq z hz) x hx,
    SignalResponseContinuity.ddv_eq_rhs r hL hrpos (heq p hp) x hx] at hh
  change |(mu*(data z hz).v x-nu*(data z hz).u x^gamma)-
    (mu*(data p hp).v x-nu*(data p hp).u x^gamma)| ≤ epsilon at hh
  rwa [hURep z hz x hx,hURep p hp x hx,hVRep z hz x hx,hVRep p hp x hx] at hh

end
end ChemotaxisBifurcation.PhysicalSignalTopology
