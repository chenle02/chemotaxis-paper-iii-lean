module
public import ChemotaxisBifurcation.AllPositiveLogisticCompactness
public import ChemotaxisBifurcation.WeakH2AmbientClosure
public import ChemotaxisBifurcation.GlobalBranch

public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
namespace ChemotaxisBifurcation.RelativeCompactness
open Filter Set
open scoped Topology

/-- Ambient subsequence extraction implies compactness of the closure.
No completeness or properness assumption on the ambient metric space is needed. -/
theorem isCompact_closure_of_subsequence {E : Type*} [MetricSpace E] {S : Set E}
    (hextract : ∀ u : ℕ → E, (∀ n, u n ∈ S) →
      ∃ x : E, ∃ phi : ℕ → ℕ, StrictMono phi ∧
        Tendsto (u ∘ phi) atTop (𝓝 x)) :
    IsCompact (closure S) := by
  apply IsSeqCompact.isCompact
  intro u hu
  have hnear : ∀ n : ℕ, ∃ v ∈ S, dist (u n) v < 1 / ((n : ℝ) + 1) := by
    intro n
    exact Metric.mem_closure_iff.mp (hu n) _ (by positivity)
  choose v hv hdist using hnear
  obtain ⟨x, phi, hphi, hconv⟩ := hextract v hv
  have hx : x ∈ closure S :=
    isClosed_closure.mem_of_tendsto hconv
      (Eventually.of_forall (fun n => subset_closure (hv (phi n))))
  have hd : Tendsto (fun n => dist (u n) (v n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨x, hx, phi, hphi, ?_⟩
  apply hconv.congr_dist
  simpa only [Function.comp_def, dist_comm] using hd.comp hphi.tendsto_atTop

end ChemotaxisBifurcation.RelativeCompactness


set_option autoImplicit false
namespace ChemotaxisBifurcation.BoundedSolutionSlices
open Set Filter Topology MeasureTheory WeakH2PhaseSpace WeakH2Compactness WeakH2AmbientClosure

/-- Bounded positive logistic solution sequences have an ambient phase limit.
The limit need not retain positive sensitivity or nonconstancy. -/
theorem logistic_slice_subsequence (p : PhysicalParams) (hp : p.LogisticAdmissible)
    {L beta X : ℝ} (hL : 0 < L) (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2)
    (hgamma1 : p.gamma ≤ 1+p.alpha) (hbeta : 0 ≤ beta)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ logisticSolutionSet p hL beta)
    (z : ℕ → ℝ × Space L hL) (hz : ∀ n, z n ∈ S ∩ {z | z.1 ≤ X}) :
    ∃ y : ℝ × Space L hL, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (z ∘ phi) atTop (𝓝 y) := by
  classical
  have hw := fun n => (hS (hz n).1).2.2.2
  choose Q hrep hnonneg hN0 hNL heq using hw
  have hphase : ∀ n, phaseOfPhysical hL (Q n) = (z n).2 := by
    intro n
    apply profileCLM_injective hL
    apply ContinuousMap.ext
    intro x
    rw [profile_phaseOfPhysical]
    exact hrep n x
  have hchi : ∀ n, |(z n).1| ≤ X := by
    intro n
    rw [abs_of_pos (hS (hz n).1).1]
    exact (hz n).2
  have hpos : ∀ n x, x ∈ Icc 0 L → 0 < (Q n).u x := by
    intro n x hx
    rw [hrep n ⟨x,hx⟩]
    exact (hS (hz n).1).2.1 ⟨x,hx⟩
  obtain ⟨chiBar,q,phi,hphi,hconv,_⟩ :=
    AllPositiveLogisticCompactness.logistic_all_positive_norm_subsequence p hp hL hm hm1
      hgamma1 hbeta (fun n => (z n).1) Q
      (fun n x hx => (hnonneg n x hx).2) hN0 hNL heq hchi hpos
  refine ⟨(chiBar,phaseOfPhysical hL q),phi,hphi,?_⟩
  simpa only [hphase,Prod.mk.eta,Function.comp_def] using hconv

/-- Fixed-mass minimal solution sequences have an ambient phase limit. -/
theorem minimal_slice_subsequence (p : PhysicalParams)
    {L beta X : ℝ} (hL : 0 < L) (halpha : 0 ≤ p.alpha)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < p.mu) (hnu : 0 ≤ p.nu) (hgamma : 0 ≤ p.gamma) (hgamma1 : p.gamma ≤ 1)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ minimalSolutionSet p hL beta)
    (z : ℕ → ℝ × Space L hL) (hz : ∀ n, z n ∈ S ∩ {z | z.1 ≤ X}) :
    ∃ y : ℝ × Space L hL, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (z ∘ phi) atTop (𝓝 y) := by
  classical
  have hw := fun n => (hS (hz n).1).2.2.2
  choose Q hrep hnonneg hN0 hNL hmass heq using hw
  have hphase : ∀ n, phaseOfPhysical hL (Q n) = (z n).2 := by
    intro n
    apply profileCLM_injective hL
    apply ContinuousMap.ext
    intro x
    rw [profile_phaseOfPhysical]
    exact hrep n x
  have hchi : ∀ n, |(z n).1| ≤ X := by
    intro n
    rw [abs_of_pos (hS (hz n).1).1]
    exact (hz n).2
  have hpos : ∀ n x, x ∈ Icc 0 L → 0 < (Q n).u x := by
    intro n x hx
    rw [hrep n ⟨x,hx⟩]
    exact (hS (hz n).1).2.1 ⟨x,hx⟩
  obtain ⟨chiBar,q,phi,hphi,hconv,_⟩ :=
    minimal_physical_norm_subsequence (fun n => (z n).1) Q hL halpha hm hm1 hbeta
      hmu hnu hgamma hgamma1 (fun n x hx => (hnonneg n x hx).2) hN0 hNL heq hchi hpos hmass
  refine ⟨(chiBar,phaseOfPhysical hL q),phi,hphi,?_⟩
  simpa only [hphase,Prod.mk.eta,Function.comp_def] using hconv

/-- Actual bounded-sensitivity logistic solution slices are relatively compact. -/
theorem logistic_isCompact_closure_slice (p : PhysicalParams) (hp : p.LogisticAdmissible)
    {L beta : ℝ} (hL : 0 < L) (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2)
    (hgamma1 : p.gamma ≤ 1+p.alpha) (hbeta : 0 ≤ beta)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ logisticSolutionSet p hL beta) (X : ℝ) :
    IsCompact (closure (S ∩ {z | z.1 ≤ X})) :=
  RelativeCompactness.isCompact_closure_of_subsequence
    (logistic_slice_subsequence p hp hL hm hm1 hgamma1 hbeta hS)

/-- Actual bounded-sensitivity fixed-mass minimal slices are relatively compact. -/
theorem minimal_isCompact_closure_slice (p : PhysicalParams)
    {L beta : ℝ} (hL : 0 < L) (halpha : 0 ≤ p.alpha)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < p.mu) (hnu : 0 ≤ p.nu) (hgamma : 0 ≤ p.gamma) (hgamma1 : p.gamma ≤ 1)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ minimalSolutionSet p hL beta) (X : ℝ) :
    IsCompact (closure (S ∩ {z | z.1 ≤ X})) :=
  RelativeCompactness.isCompact_closure_of_subsequence
    (minimal_slice_subsequence p hL halpha hm hm1 hbeta hmu hnu hgamma hgamma1 hS)

/-- A closed noncompact component in the logistic solution closure has
unbounded sensitivity. Component closedness, inclusion and noncompactness
remain explicit; bounded-slice compactness is now proved from the PDE. -/
theorem logistic_component_unbounded (p : PhysicalParams) (hp : p.LogisticAdmissible)
    {L beta : ℝ} (hL : 0 < L) (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2)
    (hgamma1 : p.gamma ≤ 1+p.alpha) (hbeta : 0 ≤ beta)
    {C S : Set (ℝ × Space L hL)} (hS : S ⊆ logisticSolutionSet p hL beta)
    (hClosed : IsClosed C) (hCS : C ⊆ closure S) (hNC : ¬ IsCompact C) :
    (∀ M : ℝ, ∃ z ∈ C, M < z.1) ∧
      sSup ((fun z : ℝ × Space L hL => (z.1 : EReal)) '' C) = ⊤ := by
  have hUnb := GlobalBranch.unbounded_of_not_isCompact
    (GlobalBranch.isCompact_slice hClosed hCS
      (logistic_isCompact_closure_slice p hp hL hm hm1 hgamma1 hbeta hS)) hNC
  exact ⟨hUnb,GlobalBranch.sSup_eq_top_of_unbounded hUnb⟩

/-- The fixed-mass minimal counterpart; no compactness hypothesis is supplied. -/
theorem minimal_component_unbounded (p : PhysicalParams)
    {L beta : ℝ} (hL : 0 < L) (halpha : 0 ≤ p.alpha)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < p.mu) (hnu : 0 ≤ p.nu) (hgamma : 0 ≤ p.gamma) (hgamma1 : p.gamma ≤ 1)
    {C S : Set (ℝ × Space L hL)} (hS : S ⊆ minimalSolutionSet p hL beta)
    (hClosed : IsClosed C) (hCS : C ⊆ closure S) (hNC : ¬ IsCompact C) :
    (∀ M : ℝ, ∃ z ∈ C, M < z.1) ∧
      sSup ((fun z : ℝ × Space L hL => (z.1 : EReal)) '' C) = ⊤ := by
  have hUnb := GlobalBranch.unbounded_of_not_isCompact
    (GlobalBranch.isCompact_slice hClosed hCS
      (minimal_isCompact_closure_slice p hL halpha hm hm1 hbeta hmu hnu hgamma hgamma1 hS)) hNC
  exact ⟨hUnb,GlobalBranch.sSup_eq_top_of_unbounded hUnb⟩

end ChemotaxisBifurcation.BoundedSolutionSlices

