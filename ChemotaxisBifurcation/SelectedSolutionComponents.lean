module
public import ChemotaxisBifurcation.BoundedSolutionSlices

@[expose] public section

set_option autoImplicit false
namespace ChemotaxisBifurcation.SelectedSolutionComponents
open Set Filter Topology WeakH2PhaseSpace WeakH2AmbientClosure
noncomputable section

/-- Selected components inherit ambient closedness and compact slices from
ambient admissibility and relative compactness. Local arc geometry remains explicit. -/
theorem selected_properties {E : Type*} [TopologicalSpace E]
    {S V : Set (ℝ × E)} {removedArc : Set V} {base selector : V}
    (hBase : base ∈ closure (((↑) : V → ℝ × E) ⁻¹' S))
    (hOpen : IsOpen (((↑) : parentComponent (closure (((↑) : V → ℝ × E) ⁻¹' S)) base → V) ⁻¹' removedArc))
    (hSelector : selector ∈ unilateralRemainder (closure (((↑) : V → ℝ × E) ⁻¹' S)) removedArc base)
    (hAdmissible : closure S ⊆ V)
    (hCompact : ∀ X : ℝ, IsCompact (closure (S ∩ {z | z.1 ≤ X}))) :
    IsClosed (GlobalBranch.selectedImage S V removedArc base selector) ∧
    GlobalBranch.selectedImage S V removedArc base selector ⊆ V ∧
    GlobalBranch.selectedImage S V removedArc base selector ⊆ closure S ∧
    IsPreconnected (GlobalBranch.selectedImage S V removedArc base selector) ∧
    ∀ X : ℝ, IsCompact (GlobalBranch.selectedImage S V removedArc base selector ∩ {z | z.1 ≤ X}) := by
  obtain ⟨hRel,hCV,hCS,hConn⟩ := GlobalBranch.selectedImage_properties hBase hOpen hSelector
  have hClosed := GlobalBranch.isClosed_of_relClosed hRel hCV
    ((closure_mono hCS).trans (closure_closure (s := S)).le |>.trans hAdmissible)
  exact ⟨hClosed,hCV,hCS,hConn,GlobalBranch.isCompact_slice hClosed hCS hCompact⟩

/-- Actual logistic selected-component properties; local geometry is explicit. -/
theorem logistic_selected_properties (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (hp : p.LogisticAdmissible)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2) (hgamma1 : p.gamma ≤ 1+p.alpha)
    (hbeta : 0 ≤ beta)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ logisticSolutionSet p hL beta)
    {removedArc : Set (AmbientClosure.admissibleSet (profileCLM hL) univ)}
    {base selector : AmbientClosure.admissibleSet (profileCLM hL) univ}
    (hBase : base ∈ closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × Space L hL) ⁻¹' S))
    (hOpen : IsOpen (((↑) : parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × Space L hL) ⁻¹' S)) base → (AmbientClosure.admissibleSet (profileCLM hL) univ)) ⁻¹' removedArc))
    (hSelector : selector ∈ unilateralRemainder
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × Space L hL) ⁻¹' S)) removedArc base) :
    IsClosed (GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) removedArc base selector) ∧
    GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) removedArc base selector ⊆ (AmbientClosure.admissibleSet (profileCLM hL) univ) ∧
    GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) removedArc base selector ⊆ closure S ∧
    IsPreconnected (GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) removedArc base selector) ∧
    ∀ X : ℝ, IsCompact (GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) removedArc base selector ∩ {z | z.1 ≤ X}) := by
  apply selected_properties hBase hOpen hSelector ?_ (BoundedSolutionSlices.logistic_isCompact_closure_slice p hp hL hm hm1 hgamma1 hbeta hS)
  obtain ⟨ha,hb,halpha,hmpos,hgamma,hnu,hmu,hu,hv,hequil,hsigequil⟩ := hp
  exact logistic_closure_subset_admissible p hL hu hmu hm hm1 hbeta halpha hb
    hnu.le hgamma hgamma1 hequil hsigequil hS

/-- Noncompactness of the actual selected component implies unbounded sensitivity.
No branch existence or noncompactness theorem is asserted. -/
theorem logistic_selected_unbounded (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (hp : p.LogisticAdmissible)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2) (hgamma1 : p.gamma ≤ 1+p.alpha)
    (hbeta : 0 ≤ beta)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ logisticSolutionSet p hL beta)
    {removedArc : Set (AmbientClosure.admissibleSet (profileCLM hL) univ)}
    {base selector : AmbientClosure.admissibleSet (profileCLM hL) univ}
    (hBase : base ∈ closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × Space L hL) ⁻¹' S))
    (hOpen : IsOpen (((↑) : parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × Space L hL) ⁻¹' S)) base → (AmbientClosure.admissibleSet (profileCLM hL) univ)) ⁻¹' removedArc))
    (hSelector : selector ∈ unilateralRemainder
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × Space L hL) ⁻¹' S)) removedArc base)
    (hNC : ¬ IsCompact (GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) removedArc base selector)) :
    (∀ M : ℝ, ∃ z ∈ GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) removedArc base selector, M < z.1) ∧
    sSup ((fun z : ℝ × Space L hL => (z.1 : EReal)) '' (GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) removedArc base selector)) = ⊤ := by
  obtain ⟨_,_,_,_,hSlices⟩ := logistic_selected_properties p hL hp hm hm1 hgamma1 hbeta hS hBase hOpen hSelector
  have hUnbounded := GlobalBranch.unbounded_of_not_isCompact hSlices hNC
  exact ⟨hUnbounded,GlobalBranch.sSup_eq_top_of_unbounded hUnbounded⟩

/-- Actual minimal selected-component properties; local geometry is explicit. -/
theorem minimal_selected_properties (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (halpha : 0 ≤ p.alpha)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta)
    (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hnu : 0 ≤ p.nu)
    (hgamma : 0 ≤ p.gamma) (hgamma1 : p.gamma ≤ 1) (hsigequil : p.SignalEquilibrium)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ minimalSolutionSet p hL beta)
    {removedArc : Set (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))}
    {base selector : AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)}
    (hBase : base ∈ closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × Space L hL) ⁻¹' S))
    (hOpen : IsOpen (((↑) : parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × Space L hL) ⁻¹' S)) base → (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))) ⁻¹' removedArc))
    (hSelector : selector ∈ unilateralRemainder
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × Space L hL) ⁻¹' S)) removedArc base) :
    IsClosed (GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) removedArc base selector) ∧
    GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) removedArc base selector ⊆ (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) ∧
    GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) removedArc base selector ⊆ closure S ∧
    IsPreconnected (GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) removedArc base selector) ∧
    ∀ X : ℝ, IsCompact (GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) removedArc base selector ∩ {z | z.1 ≤ X}) := by
  apply selected_properties hBase hOpen hSelector ?_ (BoundedSolutionSlices.minimal_isCompact_closure_slice p hL halpha hm hm1 hbeta hmu hnu hgamma hgamma1 hS)
  exact minimal_closure_subset_admissible p hL hu hmu hm hm1 hbeta halpha
    hnu hgamma hgamma1 hsigequil hS

/-- Noncompactness of the actual selected component implies unbounded sensitivity.
No branch existence or noncompactness theorem is asserted. -/
theorem minimal_selected_unbounded (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (halpha : 0 ≤ p.alpha)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta)
    (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hnu : 0 ≤ p.nu)
    (hgamma : 0 ≤ p.gamma) (hgamma1 : p.gamma ≤ 1) (hsigequil : p.SignalEquilibrium)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ minimalSolutionSet p hL beta)
    {removedArc : Set (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))}
    {base selector : AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)}
    (hBase : base ∈ closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × Space L hL) ⁻¹' S))
    (hOpen : IsOpen (((↑) : parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × Space L hL) ⁻¹' S)) base → (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))) ⁻¹' removedArc))
    (hSelector : selector ∈ unilateralRemainder
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × Space L hL) ⁻¹' S)) removedArc base)
    (hNC : ¬ IsCompact (GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) removedArc base selector)) :
    (∀ M : ℝ, ∃ z ∈ GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) removedArc base selector, M < z.1) ∧
    sSup ((fun z : ℝ × Space L hL => (z.1 : EReal)) '' (GlobalBranch.selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) removedArc base selector)) = ⊤ := by
  obtain ⟨_,_,_,_,hSlices⟩ := minimal_selected_properties p hL halpha hm hm1 hbeta hu hmu hnu hgamma hgamma1 hsigequil hS hBase hOpen hSelector
  have hUnbounded := GlobalBranch.unbounded_of_not_isCompact hSlices hNC
  exact ⟨hUnbounded,GlobalBranch.sSup_eq_top_of_unbounded hUnbounded⟩

end
end ChemotaxisBifurcation.SelectedSolutionComponents
