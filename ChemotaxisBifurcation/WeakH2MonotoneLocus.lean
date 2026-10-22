module
public import ChemotaxisBifurcation.WeakH2PhaseSpace
public import ChemotaxisBifurcation.PhysicalMonotoneLocus

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.WeakH2MonotoneLocus
open Real Set MeasureTheory Filter Topology MonotoneLocus MonotoneLocusGeneral GlobalBranch
noncomputable section

/-- Additive realization of the actual weak-H2 canonical continuous profile,
extended by zero outside the physical interval. The extension is fixed and
additive; no arbitrary off-interval canonical choice is used. -/
def rawProfile {L : ℝ} (hL : 0 < L) : WeakH2PhaseSpace.Space L hL →+ (ℝ → ℝ) where
  toFun := fun J x => if hx : x ∈ Icc 0 L then WeakH2PhaseSpace.profileCLM hL J ⟨x,hx⟩ else 0
  map_zero' := by
    funext x
    split <;> simp
  map_add' := by
    intro J K
    funext x
    by_cases hx : 0 ≤ x ∧ x ≤ L
    · simp [Set.mem_Icc,hx,map_add]
    · simp [Set.mem_Icc,hx]

/-- On the actual closed interval this is exactly the proved canonical
weak-H2 profile continuous linear map. -/
theorem rawProfile_apply {L : ℝ} (hL : 0 < L) (J : WeakH2PhaseSpace.Space L hL)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    rawProfile hL J x = WeakH2PhaseSpace.profileCLM hL J ⟨x,hx⟩ := by
  simp only [rawProfile,AddMonoidHom.coe_mk,ZeroHom.coe_mk,dite_eq_left hx]

/-- Actual all-weak-H2 phase specialization. The structural profile embedding
is constructed internally; local branch and constant-limit representations
remain explicit and are not certified by this consumer. -/
theorem isClopen_decreasingLocus_of_weakH2 {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × WeakH2PhaseSpace.Space L hL)} {pStar : ℝ × WeakH2PhaseSpace.Space L hL} (sig sigx : ℝ × WeakH2PhaseSpace.Space L hL → ℝ → ℝ)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hm : 1 ≤ m) (hgamma : 0 ≤ γ) (hmu : 0 < μ)
    (data : ∀ z ∈ C, PhysicalStrongPositivity.StationaryProfile L 0 0 0 z.1 m β)
    (hURep : ∀ z (hz : z ∈ C) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = WeakH2PhaseSpace.profileCLM hL z.2 ⟨x,hx⟩)
    (hVRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).v x = sig z x)
    (hYRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).dv x = sigx z x)
    (hpos : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 < (data z hz).u x)
    (hV : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hN0 : ∀ z (hz : z ∈ C), (data z hz).dv 0 = 0)
    (hNL : ∀ z (hz : z ∈ C), (data z hz).dv L = 0)
    (heq : ∀ z (hz : z ∈ C) x, x ∈ Ioo 0 L →
      (data z hz).ddv x-μ*(data z hz).v x+ν*(data z hz).u x^γ = 0)
    (hConst : ∀ p ∈ C, MonotoneLocusGeneral.IsConstOn ((rawProfile hL) p.2) L →
      p ∈ closure (C ∩ {q | StrictAntiOn ((rawProfile hL) q.2) (Icc 0 L)}) →
      ConstLimitRep (rawProfile hL) L (C ∩ {q | StrictAntiOn ((rawProfile hL) q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch (rawProfile hL) L C pStar 1) :
    IsClopen (((↑) : C → ℝ × WeakH2PhaseSpace.Space L hL) ⁻¹' DecreasingLocus (rawProfile hL) L pStar) := by
  have hRep : ∀ z (hz : z ∈ C) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = rawProfile hL z.2 x := by
    intro z hz x hx
    exact (hURep z hz x hx).trans (rawProfile_apply hL z.2 hx).symm
  exact PhysicalMonotoneLocus.isClopen_decreasingLocus_of_physical (rawProfile hL) hL sig sigx hχ hm hgamma hmu
    (WeakH2PhaseSpace.profileCLM hL) (WeakH2PhaseSpace.profileCLM hL).continuous
    (fun J x => (rawProfile_apply hL J x.property).symm)
    data hRep hVRep hYRep hpos hV hN0 hNL heq hConst hStar


/-- Actual all-weak-H2 phase specialization. The structural profile embedding
is constructed internally; local branch and constant-limit representations
remain explicit and are not certified by this consumer. -/
theorem isClopen_increasingLocus_of_weakH2 {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × WeakH2PhaseSpace.Space L hL)} {pStar : ℝ × WeakH2PhaseSpace.Space L hL} (sig sigx : ℝ × WeakH2PhaseSpace.Space L hL → ℝ → ℝ)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hm : 1 ≤ m) (hgamma : 0 ≤ γ) (hmu : 0 < μ)
    (data : ∀ z ∈ C, PhysicalStrongPositivity.StationaryProfile L 0 0 0 z.1 m β)
    (hURep : ∀ z (hz : z ∈ C) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = WeakH2PhaseSpace.profileCLM hL z.2 ⟨x,hx⟩)
    (hVRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).v x = sig z x)
    (hYRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).dv x = sigx z x)
    (hpos : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 < (data z hz).u x)
    (hV : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hN0 : ∀ z (hz : z ∈ C), (data z hz).dv 0 = 0)
    (hNL : ∀ z (hz : z ∈ C), (data z hz).dv L = 0)
    (heq : ∀ z (hz : z ∈ C) x, x ∈ Ioo 0 L →
      (data z hz).ddv x-μ*(data z hz).v x+ν*(data z hz).u x^γ = 0)
    (hConst : ∀ p ∈ C, MonotoneLocusGeneral.IsConstOn ((rawProfile hL) p.2) L →
      p ∈ closure (C ∩ {q | StrictMonoOn ((rawProfile hL) q.2) (Icc 0 L)}) →
      ConstLimitRep (rawProfile hL) L (C ∩ {q | StrictMonoOn ((rawProfile hL) q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch (rawProfile hL) L C pStar (-1)) :
    IsClopen (((↑) : C → ℝ × WeakH2PhaseSpace.Space L hL) ⁻¹' IncreasingLocus (rawProfile hL) L pStar) := by
  have hRep : ∀ z (hz : z ∈ C) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = rawProfile hL z.2 x := by
    intro z hz x hx
    exact (hURep z hz x hx).trans (rawProfile_apply hL z.2 hx).symm
  exact PhysicalMonotoneLocus.isClopen_increasingLocus_of_physical (rawProfile hL) hL sig sigx hχ hm hgamma hmu
    (WeakH2PhaseSpace.profileCLM hL) (WeakH2PhaseSpace.profileCLM hL).continuous
    (fun J x => (rawProfile_apply hL J x.property).symm)
    data hRep hVRep hYRep hpos hV hN0 hNL heq hConst hStar


/-- Actual all-weak-H2 phase specialization. The structural profile embedding
is constructed internally; local branch and constant-limit representations
remain explicit and are not certified by this consumer. -/
theorem part3_strictAnti_of_weakH2 {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × WeakH2PhaseSpace.Space L hL)} {pStar : ℝ × WeakH2PhaseSpace.Space L hL} (sig sigx : ℝ × WeakH2PhaseSpace.Space L hL → ℝ → ℝ)
    (hConn : IsPreconnected C) (hStarC : pStar ∈ C)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hm : 1 ≤ m) (hgamma : 0 ≤ γ) (hmu : 0 < μ)
    (data : ∀ z ∈ C, PhysicalStrongPositivity.StationaryProfile L 0 0 0 z.1 m β)
    (hURep : ∀ z (hz : z ∈ C) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = WeakH2PhaseSpace.profileCLM hL z.2 ⟨x,hx⟩)
    (hVRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).v x = sig z x)
    (hYRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).dv x = sigx z x)
    (hpos : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 < (data z hz).u x)
    (hV : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hN0 : ∀ z (hz : z ∈ C), (data z hz).dv 0 = 0)
    (hNL : ∀ z (hz : z ∈ C), (data z hz).dv L = 0)
    (heq : ∀ z (hz : z ∈ C) x, x ∈ Ioo 0 L →
      (data z hz).ddv x-μ*(data z hz).v x+ν*(data z hz).u x^γ = 0)
    (hConst : ∀ p ∈ C, MonotoneLocusGeneral.IsConstOn ((rawProfile hL) p.2) L →
      p ∈ closure (C ∩ {q | StrictAntiOn ((rawProfile hL) q.2) (Icc 0 L)}) →
      ConstLimitRep (rawProfile hL) L (C ∩ {q | StrictAntiOn ((rawProfile hL) q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch (rawProfile hL) L C pStar 1) :
    ∀ p ∈ C, p ≠ pStar → StrictAntiOn ((rawProfile hL) p.2) (Icc 0 L) := by
  have hRep : ∀ z (hz : z ∈ C) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = rawProfile hL z.2 x := by
    intro z hz x hx
    exact (hURep z hz x hx).trans (rawProfile_apply hL z.2 hx).symm
  exact PhysicalMonotoneLocus.part3_strictAnti_of_physical (rawProfile hL) hL sig sigx hConn hStarC hχ hm hgamma hmu
    (WeakH2PhaseSpace.profileCLM hL) (WeakH2PhaseSpace.profileCLM hL).continuous
    (fun J x => (rawProfile_apply hL J x.property).symm)
    data hRep hVRep hYRep hpos hV hN0 hNL heq hConst hStar


/-- Actual all-weak-H2 phase specialization. The structural profile embedding
is constructed internally; local branch and constant-limit representations
remain explicit and are not certified by this consumer. -/
theorem part3_strictMono_of_weakH2 {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × WeakH2PhaseSpace.Space L hL)} {pStar : ℝ × WeakH2PhaseSpace.Space L hL} (sig sigx : ℝ × WeakH2PhaseSpace.Space L hL → ℝ → ℝ)
    (hConn : IsPreconnected C) (hStarC : pStar ∈ C)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hm : 1 ≤ m) (hgamma : 0 ≤ γ) (hmu : 0 < μ)
    (data : ∀ z ∈ C, PhysicalStrongPositivity.StationaryProfile L 0 0 0 z.1 m β)
    (hURep : ∀ z (hz : z ∈ C) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = WeakH2PhaseSpace.profileCLM hL z.2 ⟨x,hx⟩)
    (hVRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).v x = sig z x)
    (hYRep : ∀ z (hz : z ∈ C) x (_hx : x ∈ Icc 0 L), (data z hz).dv x = sigx z x)
    (hpos : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 < (data z hz).u x)
    (hV : ∀ z (hz : z ∈ C) x, x ∈ Icc 0 L → 0 ≤ (data z hz).v x)
    (hN0 : ∀ z (hz : z ∈ C), (data z hz).dv 0 = 0)
    (hNL : ∀ z (hz : z ∈ C), (data z hz).dv L = 0)
    (heq : ∀ z (hz : z ∈ C) x, x ∈ Ioo 0 L →
      (data z hz).ddv x-μ*(data z hz).v x+ν*(data z hz).u x^γ = 0)
    (hConst : ∀ p ∈ C, MonotoneLocusGeneral.IsConstOn ((rawProfile hL) p.2) L →
      p ∈ closure (C ∩ {q | StrictMonoOn ((rawProfile hL) q.2) (Icc 0 L)}) →
      ConstLimitRep (rawProfile hL) L (C ∩ {q | StrictMonoOn ((rawProfile hL) q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch (rawProfile hL) L C pStar (-1)) :
    ∀ p ∈ C, p ≠ pStar → StrictMonoOn ((rawProfile hL) p.2) (Icc 0 L) := by
  have hRep : ∀ z (hz : z ∈ C) x (hx : x ∈ Icc 0 L),
      (data z hz).u x = rawProfile hL z.2 x := by
    intro z hz x hx
    exact (hURep z hz x hx).trans (rawProfile_apply hL z.2 hx).symm
  exact PhysicalMonotoneLocus.part3_strictMono_of_physical (rawProfile hL) hL sig sigx hConn hStarC hχ hm hgamma hmu
    (WeakH2PhaseSpace.profileCLM hL) (WeakH2PhaseSpace.profileCLM hL).continuous
    (fun J x => (rawProfile_apply hL J x.property).symm)
    data hRep hVRep hYRep hpos hV hN0 hNL heq hConst hStar

end
end ChemotaxisBifurcation.WeakH2MonotoneLocus
