module
public import ChemotaxisBifurcation.SignalTaylorRemainder
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation
open Set

/-- Actual positive-base signal source is locally Lipschitz with a derived
constant. The derivative bound is obtained by compact continuity, not assumed. -/
theorem signalSource_local_lipschitz (p : PhysicalParams) (hu : 0 < p.uStar) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℝ, |s| ≤ p.uStar/2 →
      |p.nu*(p.uStar+s)^p.gamma - p.nu*p.uStar^p.gamma| ≤ D*|s| := by
  let K := Icc (p.uStar/2) (3*p.uStar/2)
  have hpos : ∀ x ∈ K, 0 < x := by intro x hx; dsimp [K] at hx; linarith [hx.1]
  have hc : ContinuousOn (fun x : ℝ => p.nu*p.gamma*x^(p.gamma-1)) K :=
    continuousOn_const.mul (continuousOn_id.rpow_const
      (fun x hx => Or.inl (hpos x hx).ne'))
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro s hs
  have hx : p.uStar ∈ K := by constructor <;> linarith
  have hy : p.uStar+s ∈ K := by
    obtain ⟨hl,hr⟩ := abs_le.mp hs
    constructor <;> linarith
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := max B 0) (f := fun x : ℝ => p.nu*x^p.gamma)
    (f' := fun x : ℝ => p.nu*p.gamma*x^(p.gamma-1))
    (fun x hx => (signal_source_hasDerivAt p.nu p.gamma x (hpos x hx)).hasDerivWithinAt)
    (fun x hx => (hB x hx).trans (le_max_left B 0)) (convex_Icc _ _) hx hy
  simpa only [Real.norm_eq_abs,add_sub_cancel_left] using h

end ChemotaxisBifurcation
