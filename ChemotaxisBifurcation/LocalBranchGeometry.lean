module
public import ChemotaxisBifurcation.RelativeComponentClosure
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.LocalBranchGeometry
open Set

/-- The half-curve including its base is its positive half-arc with the base adjoined. -/
theorem insert_image_Ioo {X : Type*} (c : ℝ → X) {eps : ℝ} (heps : 0 < eps) :
    insert (c 0) (c '' Ioo 0 eps) = c '' Ico 0 eps := by
  ext x
  constructor
  · rintro (rfl | ⟨t,ht,rfl⟩)
    · exact ⟨0,⟨le_rfl,heps⟩,rfl⟩
    · exact ⟨t,⟨ht.1.le,ht.2⟩,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    by_cases h : t = 0
    · simp [h]
    · exact Or.inr ⟨t,⟨lt_of_le_of_ne ht.1 (Ne.symm h),ht.2⟩,rfl⟩

/-- A genuine continuous half-curve constructs closure membership, connectedness,
and the selected-component inclusion. Local existence, solution membership and
signed amplitude separation are explicit data; no local uniqueness is asserted. -/
theorem halfcurve_selected {X : Type*} [TopologicalSpace X]
    {F removed : Set X} (c : ℝ → X) (A : X → ℝ) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps))
    (hF : ∀ t ∈ Ioo 0 eps, c t ∈ F)
    (hA : ∀ t ∈ Ico 0 eps, A (c t) = t)
    (hremoved : ∀ x ∈ removed, A x < 0) :
    c 0 ∈ closure F ∧
    IsConnected (c '' Ico 0 eps) ∧
    Disjoint (c '' Ico 0 eps) removed ∧
    c delta ∈ unilateralRemainder (closure F) removed (c 0) ∧
    c '' Ico 0 eps ⊆ selectedComponent (closure F) removed (c 0) (c delta) ∧
    c 0 ∈ selectedComponent (closure F) removed (c 0) (c delta) := by
  have hzero : (0 : ℝ) ∈ closure (Ioo 0 eps) := by
    rw [closure_Ioo (ne_of_lt heps)]
    exact ⟨le_rfl,heps.le⟩
  have hbase : c 0 ∈ closure F :=
    ((hc 0 ⟨le_rfl,heps⟩).mono Ioo_subset_Ico_self).mem_closure hzero hF
  have hconn : IsConnected (c '' Ico 0 eps) :=
    (isConnected_Ico heps).image c hc
  have hin : c '' Ico 0 eps ⊆ closure F := by
    rintro _ ⟨t,ht,rfl⟩
    by_cases h : t = 0
    · simpa [h] using hbase
    · exact subset_closure (hF t ⟨lt_of_le_of_ne ht.1 (Ne.symm h),ht.2⟩)
  have hdis : Disjoint (c '' Ico 0 eps) removed := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨t,ht,rfl⟩ hr
    have hneg := hremoved (c t) hr
    rw [hA t ht] at hneg
    exact (not_lt_of_ge ht.1) hneg
  have heq := insert_image_Ioo c heps
  have hconn' : IsConnected (insert (c 0) (c '' Ioo 0 eps)) := heq ▸ hconn
  have hin' : insert (c 0) (c '' Ioo 0 eps) ⊆ closure F := heq ▸ hin
  have hdis' : Disjoint (insert (c 0) (c '' Ioo 0 eps)) removed := heq ▸ hdis
  have hsub := retainedWithBase_subset_selectedComponent
    (show c delta ∈ c '' Ioo 0 eps from ⟨delta,hdelta,rfl⟩) hconn' hin' hdis'
  have hrem := retainedWithBase_subset_unilateralRemainder hconn' hin' hdis'
  refine ⟨hbase,hconn,hdis,?_,?_,hsub (mem_insert _ _)⟩
  · exact hrem (Or.inr ⟨delta,hdelta,rfl⟩)
  · simpa only [heq] using hsub

/-- Every positive parameter on the same retained curve selects the same component. -/
theorem halfcurve_selector_independent {X : Type*} [TopologicalSpace X]
    {F removed : Set X} (c : ℝ → X) (A : X → ℝ) {eps delta eta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps) (heta : eta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps))
    (hF : ∀ t ∈ Ioo 0 eps, c t ∈ F)
    (hA : ∀ t ∈ Ico 0 eps, A (c t) = t)
    (hremoved : ∀ x ∈ removed, A x < 0) :
    selectedComponent (closure F) removed (c 0) (c delta) =
      selectedComponent (closure F) removed (c 0) (c eta) := by
  have hsub := (halfcurve_selected c A heps hdelta hc hF hA hremoved).2.2.2.2.1
  exact connectedComponentIn_eq (hsub ⟨eta,⟨heta.1.le,heta.2⟩,rfl⟩)

/-- A given local parametrization exhausts the parent in an open neighborhood;
the continuous amplitude then makes the negative punctured arc relatively open.
This theorem does not construct the local chart or prove its exhaustion. -/
theorem negative_arc_relatively_open {X : Type*} [TopologicalSpace X]
    {parent U : Set X} (c : ℝ → X) (A : X → ℝ) {eps : ℝ}
    (heps : 0 < eps) (hU : IsOpen U) (hAcont : Continuous A)
    (hnegative : ∀ t ∈ Ioo (-eps) 0, c t ∈ U)
    (hexhaust : ∀ x ∈ parent, x ∈ U → ∃ t ∈ Ioo (-eps) eps, c t = x)
    (hA : ∀ t ∈ Ioo (-eps) eps, A (c t) = t) :
    IsOpen (((↑) : parent → X) ⁻¹' (c '' Ioo (-eps) 0)) := by
  have heq : (((↑) : parent → X) ⁻¹' (c '' Ioo (-eps) 0)) =
      (((↑) : parent → X) ⁻¹' U) ∩
        (fun x : parent => A x) ⁻¹' Ioo (-eps) 0 := by
    ext x
    constructor
    · rintro ⟨t,ht,hcx⟩
      have hwide : t ∈ Ioo (-eps) eps := ⟨ht.1,ht.2.trans heps⟩
      refine ⟨?_,?_⟩
      · change (x : X) ∈ U
        rw [← hcx]
        exact hnegative t ht
      · change A (x : X) ∈ Ioo (-eps) 0
        rw [← hcx,hA t hwide]
        exact ht
    · rintro ⟨hxU,hAx⟩
      obtain ⟨t,ht,hcx⟩ := hexhaust x x.property hxU
      have hat : A (x : X) = t := by rw [← hcx]; exact hA t ht
      change A (x : X) ∈ Ioo (-eps) 0 at hAx
      exact ⟨t,by simpa only [hat] using hAx,hcx⟩
  rw [heq]
  exact (hU.preimage continuous_subtype_val).inter
    (isOpen_Ioo.preimage (hAcont.comp continuous_subtype_val))

end ChemotaxisBifurcation.LocalBranchGeometry
