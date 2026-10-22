module
public import ChemotaxisBifurcation.WeakH2PhaseSpace
public import ChemotaxisBifurcation.ConstantProfileIdentification
public import ChemotaxisBifurcation.SignalWeakSource

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.WeakH2AmbientClosure
open Set Filter Topology MeasureTheory WeakH2PhaseSpace
noncomputable section

/-- Every actual classical Neumann population has a point in the full weak-H2
phase, with its exact original continuous profile. No representation premise. -/
theorem exists_phase_of_classical {L a b alpha chi m beta : ℝ} (hL : 0 < L)
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta) :
    ∃ J : Space L hL, ∀ x : Icc (0 : ℝ) L, profileCLM hL J x=q.u x := by
  have hu : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
  have hdu : ContinuousOn q.du (Icc 0 L) := fun x hx => (q.derivative_du x hx).continuousWithinAt
  have hH2 := ClassicalSobolevDictionary.classical_H2 hL hu hdu q.continuous_ddu
    (fun x hx => (q.derivative_u x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => (q.derivative_du x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
  have hN := ClassicalSobolevDictionary.classical_neumann_trace hdu q.neumann_left q.neumann_right
  exact ⟨of_H2 hL hH2 hN,profile_of_H2 hL hH2 hN hu⟩

/-- The actual population integral of a genuine weak-H2 Neumann phase point. -/
def populationMass {L : ℝ} (hL : 0 < L) (J : Space L hL) : ℝ :=
  ∫ x : Icc (0 : ℝ) L, profileCLM hL J x ∂SignalWeakSource.intervalVolume L

/-- Continuity of the mass functional follows from the proved C0 realization
and the actual continuous L1 integral, not an affine-closedness premise. -/
theorem continuous_populationMass {L : ℝ} (hL : 0 < L) : Continuous (populationMass hL) := by
  let mu := SignalWeakSource.intervalVolume L
  let T := ContinuousMap.toLp (1 : ENNReal) mu ℝ (E := ℝ)
  have hT : Continuous (fun J : Space L hL => T (profileCLM hL J)) :=
    T.continuous.comp (profileCLM hL).continuous
  have h := (MeasureTheory.continuous_integral (μ := mu)).comp hT
  change Continuous (fun J : Space L hL => ∫ x, T (profileCLM hL J) x ∂mu) at h
  have heq : (fun J : Space L hL => ∫ x, T (profileCLM hL J) x ∂mu)=populationMass hL := by
    funext J
    apply integral_congr_ae
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (1 : ENNReal)) mu (profileCLM hL J)
  rwa [heq] at h

/-- The actual prescribed-mean affine slice in the full weak-H2 Neumann space. -/
def fixedMeanSet {L : ℝ} (hL : 0 < L) (U : ℝ) : Set (Space L hL) :=
  {J | populationMass hL J=L*U}

theorem isClosed_fixedMeanSet {L : ℝ} (hL : 0 < L) (U : ℝ) :
    IsClosed (fixedMeanSet hL U) := isClosed_eq (continuous_populationMass hL) continuous_const

/-- The phase integral is the actual manuscript integral of any represented
classical population, including the physical endpoint convention. -/
theorem populationMass_eq_of_rep {L : ℝ} (hL : 0 < L) (J : Space L hL)
    (u : ℝ → ℝ) (hRep : ∀ x : Icc (0 : ℝ) L, u x=profileCLM hL J x) :
    populationMass hL J=∫ x in (0 : ℝ)..L, u x := by
  unfold populationMass
  calc (∫ x : Icc (0 : ℝ) L, profileCLM hL J x ∂SignalWeakSource.intervalVolume L)=
      ∫ x : Icc (0 : ℝ) L, u x ∂SignalWeakSource.intervalVolume L := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => (hRep x).symm)
    _ = _ := SignalWeakSource.integral_intervalVolume hL.le u

theorem const_mem_fixedMeanSet {L : ℝ} (hL : 0 < L) (U : ℝ) :
    const hL U ∈ fixedMeanSet hL U := by
  change populationMass hL (const hL U)=L*U
  rw [populationMass_eq_of_rep hL (const hL U) (fun _ => U) (fun x => by rw [profileCLM_const]; rfl)]
  simp

/-- The physical mass is linear on all weak-H2 phase points. -/
theorem populationMass_add {L : ℝ} (hL : 0 < L) (J K : Space L hL) :
    populationMass hL (J+K)=populationMass hL J+populationMass hL K := by
  unfold populationMass
  simp only [map_add, ContinuousMap.add_apply]
  apply integral_add
  · exact (profileCLM hL J).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (profileCLM hL K).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem populationMass_smul {L : ℝ} (hL : 0 < L) (c : ℝ) (J : Space L hL) :
    populationMass hL (c • J)=c*populationMass hL J := by
  unfold populationMass
  simp only [map_smul, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]

theorem populationMass_sub {L : ℝ} (hL : 0 < L) (J K : Space L hL) :
    populationMass hL (J-K)=populationMass hL J-populationMass hL K := by
  rw [sub_eq_add_neg, populationMass_add]
  have hn := populationMass_smul hL (-1) K
  have hn' : populationMass hL (-K) = -populationMass hL K := by
    have he : (-1 : ℝ) • K = -K := neg_one_smul ℝ K
    rw [he] at hn
    simpa only [neg_mul, one_mul] using hn
  rw [hn', sub_eq_add_neg]

/-- The manuscript's fixed-mass affine space is precisely the translate of
its mean-zero perturbation space, with the physical constant population. -/
theorem mem_fixedMean_iff_sub_const {L : ℝ} (hL : 0 < L) (U : ℝ) (J : Space L hL) :
    J ∈ fixedMeanSet hL U ↔ J-const hL U ∈ fixedMeanSet hL 0 := by
  have hc := const_mem_fixedMeanSet hL U
  change populationMass hL (const hL U)=L*U at hc
  simp only [fixedMeanSet, mem_ofPred_eq, populationMass_sub, hc, mul_zero]
  exact sub_eq_zero.symm

theorem fixedMeanSet_eq_translate {L : ℝ} (hL : 0 < L) (U : ℝ) :
    fixedMeanSet hL U={J | ∃ w ∈ fixedMeanSet hL 0, J=w+const hL U} := by
  ext J
  constructor
  · intro h
    exact ⟨J-const hL U,(mem_fixedMean_iff_sub_const hL U J).mp h,by abel⟩
  · rintro ⟨w,hw,rfl⟩
    apply (mem_fixedMean_iff_sub_const hL U _).mpr
    simpa using hw

/-- Translation gives the actual topology on the affine fixed-mean slice. -/
def meanZeroTranslation {L : ℝ} (hL : 0 < L) (U : ℝ) :
    {w : Space L hL // w ∈ fixedMeanSet hL 0} ≃ₜ
      {J : Space L hL // J ∈ fixedMeanSet hL U} where
  toFun w := ⟨w.1+const hL U, by
    apply (mem_fixedMean_iff_sub_const hL U _).mpr
    simpa only [add_sub_cancel_right] using w.2⟩
  invFun J := ⟨J.1-const hL U,(mem_fixedMean_iff_sub_const hL U J.1).mp J.2⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv J := by apply Subtype.ext; simp
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

/-- The strictly positive physical affine slice is exactly uStar plus the
mean-zero perturbations whose translated population is strictly positive. -/
def positiveMeanZeroTranslation {L : ℝ} (hL : 0 < L) (U : ℝ) :
    {w : Space L hL // w ∈ fixedMeanSet hL 0 ∧ ∀ x, 0 < U+profileCLM hL w x} ≃ₜ
      {J : Space L hL // J ∈ fixedMeanSet hL U ∧ ∀ x, 0 < profileCLM hL J x} where
  toFun w := ⟨w.1+const hL U, by
    refine ⟨?_,?_⟩
    · apply (mem_fixedMean_iff_sub_const hL U _).mpr
      simpa using w.2.1
    · intro x
      simpa [profileCLM_const, add_comm] using w.2.2 x⟩
  invFun J := ⟨J.1-const hL U, by
    refine ⟨(mem_fixedMean_iff_sub_const hL U J.1).mp J.2.1,?_⟩
    intro x
    simpa [profileCLM_const] using J.2.2 x⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv J := by apply Subtype.ext; simp
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

/-- Given actual positive nontrivial logistic stationary solutions, in the
actual all-weak-H2 Neumann phase space. No existence of a branch is encoded. -/
def logisticSolutionSet (p : PhysicalParams) {L : ℝ} (hL : 0 < L) (beta : ℝ) :
    Set (ℝ × Space L hL) :=
  {z | 0 < z.1 ∧ (∀ x, 0 < profileCLM hL z.2 x) ∧
    z.2 ≠ const hL p.uStar ∧
    z ∈ ActualSolutionClosure.solutionSet (profileCLM hL) p.a p.b p.alpha p.m beta p.mu p.nu p.gamma}

/-- Actual logistic ambient closure with the full weak-H2 phase realization.
No profile embedding, injectivity, affine closedness, nonconstancy, limit PDE,
strong positivity or local-uniqueness input remains. -/
theorem logistic_closure_subset_admissible (p : PhysicalParams) {L beta : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2) (hbeta : 0 ≤ beta)
    (halpha : 0 < p.alpha) (hb : 0 < p.b)
    (hnu : 0 ≤ p.nu) (hgamma : 0 < p.gamma) (hgamma1 : p.gamma ≤ 1+p.alpha)
    (hequil : p.LogisticEquilibrium) (hsigequil : p.SignalEquilibrium)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ logisticSolutionSet p hL beta) :
    closure S ⊆ AmbientClosure.admissibleSet (profileCLM hL) univ := by
  apply ConstantProfileIdentification.closure_subset_admissible_of_nontrivial (uStar := const hL p.uStar) p hL hu hmu hm hm1 hbeta
    halpha hb hnu hgamma hgamma1 hequil hsigequil (profileCLM hL).continuous
    (profileCLM_injective hL) ?_ isClosed_univ ?_ ?_ ?_
  · intro x
    rw [profileCLM_const]
    rfl
  · intro z hz
    exact ⟨(hS hz).1,mem_univ _,(hS hz).2.1⟩
  · exact fun z hz => (hS hz).2.2.1
  · exact fun z hz => (hS hz).2.2.2

/-- Actual prescribed-mass minimal stationary solutions with positive
sensitivity and population, excluding the given constant phase point. -/
def minimalSolutionSet (p : PhysicalParams) {L : ℝ} (hL : 0 < L) (beta : ℝ) :
    Set (ℝ × Space L hL) :=
  {z | 0 < z.1 ∧ (∀ x, 0 < profileCLM hL z.2 x) ∧
    z.2 ≠ const hL p.uStar ∧
    z ∈ ActualSolutionClosure.minimalSolutionSet (profileCLM hL) p.alpha p.m beta p.mu p.nu p.gamma p.uStar}

/-- Actual minimal ambient closure in the genuine fixed-mean affine slice of
all weak-H2 Neumann phase points. All phase realization and analytic inputs
are supplied by proofs, not assumptions about the chosen solution family. -/
theorem minimal_closure_subset_admissible (p : PhysicalParams) {L beta : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta) (halpha : 0 ≤ p.alpha)
    (hnu : 0 ≤ p.nu) (hgamma : 0 ≤ p.gamma) (hgamma1 : p.gamma ≤ 1)
    (hsigequil : p.SignalEquilibrium)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ minimalSolutionSet p hL beta) :
    closure S ⊆ AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar) := by
  apply ActualSolutionClosure.closure_subset_admissible_minimal (uStar := const hL p.uStar) p hL hu hmu hm hm1 hbeta halpha
    hnu hgamma hgamma1 hsigequil (profileCLM hL).continuous (profileCLM_injective hL)
    ?_ (isClosed_fixedMeanSet hL p.uStar) ?_ ?_ ?_
  · intro x
    rw [profileCLM_const]
    rfl
  · intro z hz
    obtain ⟨q,hrep,_,_,_,hmass,_⟩ := (hS hz).2.2.2
    have hmean : z.2 ∈ fixedMeanSet hL p.uStar := by
      change populationMass hL z.2=L*p.uStar
      rw [populationMass_eq_of_rep hL z.2 q.u hrep,hmass]
    exact ⟨(hS hz).1,hmean,(hS hz).2.1⟩
  · exact fun z hz => (hS hz).2.2.1
  · exact fun z hz => (hS hz).2.2.2

end
end ChemotaxisBifurcation.WeakH2AmbientClosure
