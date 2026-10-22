module
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Constructions

@[expose] public section

/-!
# Relative closure of a unilateral connected component

This file isolates the topological deduction used in current Theorem 1.3(1).
The ambient type `X` is intended to be the admissible space `V` with its
subspace topology.  Local uniqueness and local bifurcation geometry enter only
through the explicit relative-openness, connectedness, containment, and
disjointness hypotheses below.

Nothing here proves that an ambient limit belongs to `V`; that is the separate
analytic content of current Lemma 4.3.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation

open Set

section

variable {X : Type*} [TopologicalSpace X]

/-- The component of the relatively closed nontrivial-solution set containing
the bifurcation point.  At the manuscript application, `X` is `V`. -/
noncomputable def parentComponent (solutionClosure : Set X) (base : X) : Set X :=
  connectedComponentIn solutionClosure base

/-- Remove the opposite punctured local half-arc from the parent component. -/
noncomputable def unilateralRemainder
    (solutionClosure removedArc : Set X) (base : X) : Set X :=
  parentComponent solutionClosure base \ removedArc

/-- The unilateral component selected by a point on the retained local
half-arc. -/
noncomputable def selectedComponent
    (solutionClosure removedArc : Set X) (base selector : X) : Set X :=
  connectedComponentIn (unilateralRemainder solutionClosure removedArc base) selector

/-- A connected component inside a closed subset is closed in the ambient
space.  This is obtained from the closed component in the subtype and the
closed subtype inclusion. -/
theorem isClosed_connectedComponentIn_of_isClosed
    {F : Set X} {x : X} (hF : IsClosed F) (hx : x ∈ F) :
    IsClosed (connectedComponentIn F x) := by
  rw [connectedComponentIn_eq_image hx]
  exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent

/-- Removing a set open in the relative topology of a closed parent leaves a
set closed in the ambient space. -/
theorem isClosed_sdiff_of_isOpen_preimage
    {parent removed : Set X} (hParent : IsClosed parent)
    (hRemoved : IsOpen (((↑) : parent → X) ⁻¹' removed)) :
    IsClosed (parent \ removed) := by
  have hImage :
      ((↑) : parent → X) '' ((((↑) : parent → X) ⁻¹' removed)ᶜ) =
        parent \ removed := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, by simpa using hz⟩
    · rintro ⟨hyParent, hyRemoved⟩
      exact ⟨⟨y, hyParent⟩, by simpa, rfl⟩
  rw [← hImage]
  exact hParent.isClosedMap_subtype_val _ hRemoved.isClosed_compl

/-- The manuscript's parent component is relatively closed in the admissible
space once the nontrivial-solution closure is closed there. -/
theorem parentComponent_isClosed
    {solutionClosure : Set X} {base : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure) :
    IsClosed (parentComponent solutionClosure base) := by
  exact isClosed_connectedComponentIn_of_isClosed hSolutionClosed hBase

/-- The opposite arc is an analytic/local-bifurcation input: if it is open in
the relative topology of the parent component, its removal is closed in the
admissible space. -/
theorem unilateralRemainder_isClosed
    {solutionClosure removedArc : Set X} {base : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure)
    (hRemovedRelOpen :
      IsOpen
        (((↑) : parentComponent solutionClosure base → X) ⁻¹' removedArc)) :
    IsClosed (unilateralRemainder solutionClosure removedArc base) := by
  exact isClosed_sdiff_of_isOpen_preimage
    (parentComponent_isClosed hSolutionClosed hBase) hRemovedRelOpen

/-- A connected retained half-arc together with the bifurcation point lies in
the parent component when it lies in the solution closure. -/
theorem retainedWithBase_subset_parentComponent
    {solutionClosure retainedArc : Set X} {base : X}
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure) :
    insert base retainedArc ⊆ parentComponent solutionClosure base := by
  exact hRetainedConnected.isPreconnected.subset_connectedComponentIn
    (mem_insert base retainedArc) hRetainedInSolution

/-- If the retained local half-arc and the base avoid the removed opposite
arc, they lie in the unilateral remainder. -/
theorem retainedWithBase_subset_unilateralRemainder
    {solutionClosure removedArc retainedArc : Set X} {base : X}
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    insert base retainedArc ⊆
      unilateralRemainder solutionClosure removedArc base := by
  intro x hx
  exact ⟨retainedWithBase_subset_parentComponent hRetainedConnected
    hRetainedInSolution hx, Set.disjoint_left.mp hAvoidRemoved hx⟩

/-- The connected retained local branch selects a single component of the
remainder.  Consequently both its punctured half-arc and its limiting base
point belong to that selected component. -/
theorem retainedWithBase_subset_selectedComponent
    {solutionClosure removedArc retainedArc : Set X} {base selector : X}
    (hSelector : selector ∈ retainedArc)
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    insert base retainedArc ⊆
      selectedComponent solutionClosure removedArc base selector := by
  have hSubset : insert base retainedArc ⊆
      unilateralRemainder solutionClosure removedArc base :=
    retainedWithBase_subset_unilateralRemainder hRetainedConnected
      hRetainedInSolution hAvoidRemoved
  exact hRetainedConnected.isPreconnected.subset_connectedComponentIn
    (mem_insert_of_mem base hSelector) hSubset

/-- In particular, the bifurcation point belongs to the unilateral component
selected by any point on the retained half-arc. -/
theorem base_mem_selectedComponent
    {solutionClosure removedArc retainedArc : Set X} {base selector : X}
    (hSelector : selector ∈ retainedArc)
    (hRetainedConnected : IsConnected (insert base retainedArc))
    (hRetainedInSolution : insert base retainedArc ⊆ solutionClosure)
    (hAvoidRemoved : Disjoint (insert base retainedArc) removedArc) :
    base ∈ selectedComponent solutionClosure removedArc base selector := by
  exact retainedWithBase_subset_selectedComponent hSelector hRetainedConnected
    hRetainedInSolution hAvoidRemoved (mem_insert base retainedArc)

/-- The selected unilateral component is relatively closed in the admissible
space.  Its only analytic input beyond closedness of the solution closure is
relative openness of the removed opposite arc in the parent component. -/
theorem selectedComponent_isClosed
    {solutionClosure removedArc : Set X} {base selector : X}
    (hSolutionClosed : IsClosed solutionClosure) (hBase : base ∈ solutionClosure)
    (hRemovedRelOpen :
      IsOpen
        (((↑) : parentComponent solutionClosure base → X) ⁻¹' removedArc))
    (hSelectorInRemainder :
      selector ∈ unilateralRemainder solutionClosure removedArc base) :
    IsClosed (selectedComponent solutionClosure removedArc base selector) := by
  exact isClosed_connectedComponentIn_of_isClosed
    (unilateralRemainder_isClosed hSolutionClosed hBase hRemovedRelOpen)
    hSelectorInRemainder

/-- The selected component stays inside the relatively closed solution set. -/
theorem selectedComponent_subset_solutionClosure
    {solutionClosure removedArc : Set X} {base selector : X} :
    selectedComponent solutionClosure removedArc base selector ⊆ solutionClosure := by
  exact (connectedComponentIn_subset _ _).trans
    (sdiff_subset.trans (connectedComponentIn_subset _ _))

end

end ChemotaxisBifurcation
