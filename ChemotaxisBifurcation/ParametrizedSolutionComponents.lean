module
public import ChemotaxisBifurcation.LocalBranchGeometry
public import ChemotaxisBifurcation.SelectedSolutionComponents

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ParametrizedSolutionComponents
open Set Topology WeakH2PhaseSpace WeakH2AmbientClosure GlobalBranch
noncomputable section

/-- Actual local curve data construct the selected-image geometry.
Local curve existence, stationary membership and local-chart exhaustion remain
explicit. No component membership, arc connectedness or relative openness is assumed. -/
theorem selectedImage_of_local_curve {E : Type*} [TopologicalSpace E]
    {S V : Set (ℝ × E)} (c : ℝ → V) (A : V → ℝ) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps)) (hAc : Continuous A)
    (hsol : ∀ t ∈ Ioo (-eps) eps, t ≠ 0 → (c t : ℝ × E) ∈ S)
    (hA : ∀ t ∈ Ioo (-eps) eps, A (c t) = t)
    (U : Set V) (hU : IsOpen U)
    (hnegative : ∀ t ∈ Ioo (-eps) 0, c t ∈ U)
    (hexhaust : ∀ x ∈ parentComponent (closure (((↑) : V → ℝ × E) ⁻¹' S)) (c 0),
      x ∈ U → ∃ t ∈ Ioo (-eps) eps, c t = x)
    (hAdmissible : closure S ⊆ V)
    (hCompact : ∀ X : ℝ, IsCompact (closure (S ∩ {z | z.1 ≤ X}))) :
    IsClosed (selectedImage S V (c '' Ioo (-eps) 0) (c 0) (c delta)) ∧
    IsConnected (selectedImage S V (c '' Ioo (-eps) 0) (c 0) (c delta)) ∧
    (c 0 : ℝ × E) ∈ selectedImage S V (c '' Ioo (-eps) 0) (c 0) (c delta) ∧
    (((↑) : V → ℝ × E) '' (c '' Ico 0 eps)) ⊆ selectedImage S V (c '' Ioo (-eps) 0) (c 0) (c delta) ∧
    selectedImage S V (c '' Ioo (-eps) 0) (c 0) (c delta) ⊆ V ∧
    selectedImage S V (c '' Ioo (-eps) 0) (c 0) (c delta) ⊆ closure S ∧
    ∀ X : ℝ, IsCompact (selectedImage S V (c '' Ioo (-eps) 0) (c 0) (c delta) ∩ {z | z.1 ≤ X}) := by
  have hpos : ∀ t ∈ Ioo 0 eps, c t ∈ (((↑) : V → ℝ × E) ⁻¹' S) := by
    intro t ht
    exact hsol t ⟨by linarith [ht.1],ht.2⟩ ht.1.ne'
  have hApos : ∀ t ∈ Ico 0 eps, A (c t) = t := by
    intro t ht
    exact hA t ⟨by linarith [ht.1],ht.2⟩
  have hrem : ∀ x ∈ c '' Ioo (-eps) 0, A x < 0 := by
    rintro x ⟨t,ht,rfl⟩
    rw [hA t ⟨ht.1,ht.2.trans heps⟩]
    exact ht.2
  obtain ⟨hBase,_,_,hSelector,hArc,hBaseSel⟩ :=
    LocalBranchGeometry.halfcurve_selected c A heps hdelta hc hpos hApos hrem
  have hOpen := LocalBranchGeometry.negative_arc_relatively_open c A heps hU hAc
    hnegative hexhaust hA
  obtain ⟨hClosed,hCV,hCS,hPre,hSlices⟩ :=
    SelectedSolutionComponents.selected_properties hBase hOpen hSelector hAdmissible hCompact
  have hBaseImage : (c 0 : ℝ × E) ∈ selectedImage S V (c '' Ioo (-eps) 0) (c 0) (c delta) :=
    ⟨c 0,hBaseSel,rfl⟩
  refine ⟨hClosed,⟨⟨_,hBaseImage⟩,hPre⟩,hBaseImage,?_,hCV,hCS,hSlices⟩
  rintro z ⟨x,⟨t,ht,rfl⟩,rfl⟩
  exact ⟨c t,hArc ⟨t,ht,rfl⟩,rfl⟩

/-- The ambient selected image does not depend on which positive point of
this same parameterized half-curve is used as selector. -/
theorem selectedImage_selector_independent {E : Type*} [TopologicalSpace E]
    {S V : Set (ℝ × E)} (c : ℝ → V) (A : V → ℝ) {eps delta eta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps) (heta : eta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps))
    (hsol : ∀ t ∈ Ioo (-eps) eps, t ≠ 0 → (c t : ℝ × E) ∈ S)
    (hA : ∀ t ∈ Ioo (-eps) eps, A (c t) = t) :
    selectedImage S V (c '' Ioo (-eps) 0) (c 0) (c delta) =
      selectedImage S V (c '' Ioo (-eps) 0) (c 0) (c eta) := by
  have hpos : ∀ t ∈ Ioo 0 eps, c t ∈ (((↑) : V → ℝ × E) ⁻¹' S) := by
    intro t ht
    exact hsol t ⟨by linarith [ht.1],ht.2⟩ ht.1.ne'
  have hApos : ∀ t ∈ Ico 0 eps, A (c t) = t := by
    intro t ht
    exact hA t ⟨by linarith [ht.1],ht.2⟩
  have hrem : ∀ x ∈ c '' Ioo (-eps) 0, A x < 0 := by
    rintro x ⟨t,ht,rfl⟩
    rw [hA t ⟨ht.1,ht.2.trans heps⟩]
    exact ht.2
  have heq := LocalBranchGeometry.halfcurve_selector_independent c A heps hdelta heta hc hpos hApos hrem
  exact congrArg (fun K : Set V => ((↑) : V → ℝ × E) '' K) heq

/-- Actual logistic selected half-branch consequences from a given local solution chart. -/
theorem logistic_of_local_curve (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (hp : p.LogisticAdmissible)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2) (hg1 : p.gamma ≤ 1+p.alpha) (hbeta : 0 ≤ beta)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ logisticSolutionSet p hL beta)
    (c : ℝ → (AmbientClosure.admissibleSet (profileCLM hL) univ)) (A : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps)) (hAc : Continuous A)
    (hsol : ∀ t ∈ Ioo (-eps) eps, t ≠ 0 → (c t : ℝ × Space L hL) ∈ S)
    (hA : ∀ t ∈ Ioo (-eps) eps, A (c t) = t)
    (U : Set (AmbientClosure.admissibleSet (profileCLM hL) univ)) (hU : IsOpen U)
    (hnegative : ∀ t ∈ Ioo (-eps) 0, c t ∈ U)
    (hexhaust : ∀ x ∈ parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × Space L hL) ⁻¹' S)) (c 0),
      x ∈ U → ∃ t ∈ Ioo (-eps) eps, c t = x) :
    IsClosed (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta)) ∧
    IsConnected (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta)) ∧
    (c 0 : ℝ × (Space L hL)) ∈ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta) ∧
    (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × (Space L hL)) '' (c '' Ico 0 eps)) ⊆ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta) ∧
    selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta) ⊆ (AmbientClosure.admissibleSet (profileCLM hL) univ) ∧
    selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta) ⊆ closure S ∧
    ∀ X : ℝ, IsCompact (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta) ∩ {z | z.1 ≤ X}) := by
  apply selectedImage_of_local_curve c A heps hdelta hc hAc hsol hA U hU hnegative hexhaust
  · obtain ⟨ha,hb,halpha,_,hgamma,hnu,hmu,hu,_,heq,hsigeq⟩ := hp
    exact logistic_closure_subset_admissible p hL hu hmu hm hm1 hbeta halpha hb
      hnu.le hgamma hg1 heq hsigeq hS
  · exact BoundedSolutionSlices.logistic_isCompact_closure_slice p hp hL hm hm1 hg1 hbeta hS

/-- The actual logistic local-chart selected image has unbounded sensitivity
when noncompact; noncompactness/global continuation remain explicit. -/
theorem logistic_unbounded_of_local_curve (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (hp : p.LogisticAdmissible)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2) (hg1 : p.gamma ≤ 1+p.alpha) (hbeta : 0 ≤ beta)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ logisticSolutionSet p hL beta)
    (c : ℝ → (AmbientClosure.admissibleSet (profileCLM hL) univ)) (A : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps)) (hAc : Continuous A)
    (hsol : ∀ t ∈ Ioo (-eps) eps, t ≠ 0 → (c t : ℝ × Space L hL) ∈ S)
    (hA : ∀ t ∈ Ioo (-eps) eps, A (c t) = t)
    (U : Set (AmbientClosure.admissibleSet (profileCLM hL) univ)) (hU : IsOpen U)
    (hnegative : ∀ t ∈ Ioo (-eps) 0, c t ∈ U)
    (hexhaust : ∀ x ∈ parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × Space L hL) ⁻¹' S)) (c 0),
      x ∈ U → ∃ t ∈ Ioo (-eps) eps, c t = x)
    (hNC : ¬ IsCompact (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta))) :
    (∀ M : ℝ, ∃ z ∈ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta), M < z.1) ∧
      sSup ((fun z : ℝ × Space L hL => (z.1 : EReal)) '' (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta))) = ⊤ := by
  obtain ⟨_,_,_,_,_,_,hSlices⟩ := logistic_of_local_curve p hL hp hm hm1 hg1 hbeta hS c A heps hdelta
    hc hAc hsol hA U hU hnegative hexhaust
  have hUnbounded := unbounded_of_not_isCompact hSlices hNC
  exact ⟨hUnbounded,sSup_eq_top_of_unbounded hUnbounded⟩

/-- Actual minimal selected half-branch consequences from a given local solution chart. -/
theorem minimal_of_local_curve (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (halpha : 0 ≤ p.alpha)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta)
    (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hnu : 0 ≤ p.nu)
    (hgamma : 0 ≤ p.gamma) (hg1 : p.gamma ≤ 1) (heq : p.SignalEquilibrium)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ minimalSolutionSet p hL beta)
    (c : ℝ → (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))) (A : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps)) (hAc : Continuous A)
    (hsol : ∀ t ∈ Ioo (-eps) eps, t ≠ 0 → (c t : ℝ × Space L hL) ∈ S)
    (hA : ∀ t ∈ Ioo (-eps) eps, A (c t) = t)
    (U : Set (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))) (hU : IsOpen U)
    (hnegative : ∀ t ∈ Ioo (-eps) 0, c t ∈ U)
    (hexhaust : ∀ x ∈ parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × Space L hL) ⁻¹' S)) (c 0),
      x ∈ U → ∃ t ∈ Ioo (-eps) eps, c t = x) :
    IsClosed (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta)) ∧
    IsConnected (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta)) ∧
    (c 0 : ℝ × (Space L hL)) ∈ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta) ∧
    (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × (Space L hL)) '' (c '' Ico 0 eps)) ⊆ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta) ∧
    selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta) ⊆ (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) ∧
    selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta) ⊆ closure S ∧
    ∀ X : ℝ, IsCompact (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta) ∩ {z | z.1 ≤ X}) := by
  apply selectedImage_of_local_curve c A heps hdelta hc hAc hsol hA U hU hnegative hexhaust
  · exact minimal_closure_subset_admissible p hL hu hmu hm hm1 hbeta halpha hnu hgamma hg1 heq hS
  · exact BoundedSolutionSlices.minimal_isCompact_closure_slice p hL halpha hm hm1 hbeta hmu hnu hgamma hg1 hS

/-- The actual minimal local-chart selected image has unbounded sensitivity
when noncompact; noncompactness/global continuation remain explicit. -/
theorem minimal_unbounded_of_local_curve (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (halpha : 0 ≤ p.alpha)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta)
    (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hnu : 0 ≤ p.nu)
    (hgamma : 0 ≤ p.gamma) (hg1 : p.gamma ≤ 1) (heq : p.SignalEquilibrium)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ minimalSolutionSet p hL beta)
    (c : ℝ → (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))) (A : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps)) (hAc : Continuous A)
    (hsol : ∀ t ∈ Ioo (-eps) eps, t ≠ 0 → (c t : ℝ × Space L hL) ∈ S)
    (hA : ∀ t ∈ Ioo (-eps) eps, A (c t) = t)
    (U : Set (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))) (hU : IsOpen U)
    (hnegative : ∀ t ∈ Ioo (-eps) 0, c t ∈ U)
    (hexhaust : ∀ x ∈ parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × Space L hL) ⁻¹' S)) (c 0),
      x ∈ U → ∃ t ∈ Ioo (-eps) eps, c t = x)
    (hNC : ¬ IsCompact (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta))) :
    (∀ M : ℝ, ∃ z ∈ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta), M < z.1) ∧
      sSup ((fun z : ℝ × Space L hL => (z.1 : EReal)) '' (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta))) = ⊤ := by
  obtain ⟨_,_,_,_,_,_,hSlices⟩ := minimal_of_local_curve p hL halpha hm hm1 hbeta hu hmu hnu hgamma hg1 heq hS c A heps hdelta
    hc hAc hsol hA U hU hnegative hexhaust
  have hUnbounded := unbounded_of_not_isCompact hSlices hNC
  exact ⟨hUnbounded,sSup_eq_top_of_unbounded hUnbounded⟩

end
end ChemotaxisBifurcation.ParametrizedSolutionComponents
