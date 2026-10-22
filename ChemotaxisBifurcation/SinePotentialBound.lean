module
public import ChemotaxisBifurcation.MonotoneLocusGeneral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.SinePotentialBound
open Real Set
noncomputable section

/-- The sine test, expressed through its Wronskian. A positive classical
solution of -w''=c*w cannot have potential at least the first Dirichlet
frequency squared throughout an interior interval. No integral estimate or
spectral conclusion is assumed. -/
theorem not_potential_ge {a b : ℝ} (hab : a < b) {w dw c : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivWithinAt w (dw x) (Icc a b) x)
    (hdw : ∀ x ∈ Icc a b, HasDerivWithinAt dw (-c x*w x) (Icc a b) x)
    (hpos : ∀ x ∈ Icc a b, 0 < w x) :
    ¬ (∀ x ∈ Icc a b, (Real.pi/(b-a))^2 ≤ c x) := by
  intro hc
  let k := Real.pi/(b-a)
  have hk : 0 < k := div_pos Real.pi_pos (sub_pos.mpr hab)
  let psi := fun x : ℝ => Real.sin (k*(x-a))
  let dpsi := fun x : ℝ => k*Real.cos (k*(x-a))
  have hpsi : ∀ x, HasDerivAt psi (dpsi x) x := by
    intro x
    convert (((hasDerivAt_id x).sub_const a).const_mul k).sin using 1 <;>
      dsimp [psi,dpsi]; ring
  have hdpsi : ∀ x, HasDerivAt dpsi (-k^2*psi x) x := by
    intro x
    convert ((((hasDerivAt_id x).sub_const a).const_mul k).cos).const_mul k using 1 <;>
      dsimp [psi,dpsi]; ring
  have hsin : ∀ x ∈ Icc a b, 0 ≤ psi x := by
    intro x hx
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact mul_nonneg hk.le (sub_nonneg.mpr hx.1)
    · have heq : k*(b-a) = Real.pi := by dsimp [k]; field_simp
      rw [← heq]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hk.le
  let F := fun x => dw x*psi x-w x*dpsi x
  have hF : ContinuousOn F (Icc a b) := by
    intro x hx
    exact (((hdw x hx).continuousWithinAt.mul (hpsi x).continuousAt.continuousWithinAt).sub
      ((hw x hx).continuousWithinAt.mul (hdpsi x).continuousAt.continuousWithinAt))
  have hFd : ∀ x ∈ Icc a b,
      HasDerivWithinAt F ((k^2-c x)*w x*psi x) (Icc a b) x := by
    intro x hx
    convert ((hdw x hx).mul (hpsi x).hasDerivWithinAt).sub
      ((hw x hx).mul (hdpsi x).hasDerivWithinAt) using 1; ring
  have hanti : AntitoneOn F (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hF
      (fun x hx => (hFd x (interior_subset hx)).mono interior_subset)
      (fun x hx => mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hc x (interior_subset hx)))
          (hpos x (interior_subset hx)).le) (hsin x (interior_subset hx)))
  have hends := hanti ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ hab.le
  have heq : k*(b-a) = Real.pi := by dsimp [k]; field_simp
  have h0 : F a = -k*w a := by simp [F,psi,dpsi]; ring
  have h1 : F b = k*w b := by simp [F,psi,dpsi,heq]; ring
  rw [h0,h1] at hends
  have ha := mul_pos hk (hpos a ⟨le_rfl,hab.le⟩)
  have hb := mul_pos hk (hpos b ⟨hab.le,le_rfl⟩)
  linarith

end
end ChemotaxisBifurcation.SinePotentialBound
