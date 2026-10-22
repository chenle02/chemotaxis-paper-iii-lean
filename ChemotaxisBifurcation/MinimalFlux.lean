module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# The minimal-model flux identity (Lemma 4.2(1), (5))

In the minimal model (`a = b = 0`) a stationary solution of `E:main-PE`
satisfies the divergence-form equation
`0 = u_xx - χ₀ (u^m/(1+v)^β v_x)_x` on `(0,L)` with `u_x = v_x = 0` at
`x = 0`. Integrating from `0` to `x` gives the flux identity
`u_x = χ₀ u^m/(1+v)^β v_x` (TeX `E:minimal-spike-flux`). For `m = 1` and
`u > 0` the identity integrates once more to the exponential representation
`u(x) = u(x₀) exp(χ₀ ∫_{x₀}^x v_y/(1+v)^β dy)` used in Lemma 4.2(5).

Both are classical-calculus consumers. The derivatives of the solution
(`du = u_x`, `ddu = u_xx`, `dv = v_x`, and the derivative `dJ` of the flux),
the stationary equation and the left boundary values are hypotheses; the
existence and regularity of the solution are not proved here.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.MinimalFlux

open Set

/-- A function continuous on `[0,L]` with zero derivative on `(0,L)` equals
its value at `0` throughout `[0,L]`. -/
theorem eq_left_of_hasDerivAt_zero {L : ℝ} {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt F 0 x) :
    ∀ x ∈ Icc 0 L, F x = F 0 := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h0 | hpos
  · rw [← h0]
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F (fun _ => (0 : ℝ)) hpos
    (hF.mono (Icc_subset_Icc le_rfl hx.2))
    (fun y hy => hderiv y ⟨hy.1, hy.2.trans_le hx.2⟩)
  have hx0 : x - 0 ≠ 0 := by linarith
  rw [eq_comm, div_eq_zero_iff] at hslope
  rcases hslope with h | h
  · linarith
  · exact absurd h hx0

/-- The chemotactic flux `χ₀ u^m/(1+v)^β v_x`. -/
noncomputable def flux (chi0 m beta : ℝ) (u v dv : ℝ → ℝ) (x : ℝ) : ℝ :=
  chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x

/-- **Lemma 4.2(1)**, TeX `E:minimal-spike-flux`. If `u_x` is continuous on
`[0,L]` with derivative `u_xx` on `(0,L)`, the flux is continuous on `[0,L]`
with derivative `dJ` on `(0,L)`, the stationary minimal equation
`u_xx - dJ = 0` holds on `(0,L)`, and `u_x(0) = v_x(0) = 0`, then
`u_x = χ₀ u^m/(1+v)^β v_x` on `[0,L]`. -/
theorem minimal_flux_identity (L chi0 m beta : ℝ) (u v du ddu dv dJ : ℝ → ℝ)
    (hdu_cont : ContinuousOn du (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hJ_cont : ContinuousOn (flux chi0 m beta u v dv) (Icc 0 L))
    (hJ : ∀ x ∈ Ioo 0 L, HasDerivAt (flux chi0 m beta u v dv) (dJ x) x)
    (hstationary : ∀ x ∈ Ioo 0 L, ddu x - dJ x = 0)
    (hbc_u : du 0 = 0) (hbc_v : dv 0 = 0) :
    ∀ x ∈ Icc 0 L, du x = chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x := by
  have h := eq_left_of_hasDerivAt_zero (F := fun x => du x - flux chi0 m beta u v dv x)
    (hdu_cont.sub hJ_cont) (fun x hx => by
      have := (hddu x hx).sub (hJ x hx)
      rwa [hstationary x hx] at this)
  intro x hx
  have hx' := h x hx
  simp only [flux, hbc_u, hbc_v, mul_zero, sub_zero] at hx'
  linarith

/-- **Lemma 4.2(5), the exponential representation for `m = 1`.** If `u` is
positive and continuous on `[0,L]`, differentiable on `(0,L)` with derivative
`du`, and satisfies the flux identity `u_x = χ₀ u/(1+v)^β v_x` there, and the
signal factor `g = χ₀ v_x/(1+v)^β` is continuous on `[0,L]`, then
`u(x) = u(x₀) exp(∫_{x₀}^x g)` for all `x₀, x ∈ [0,L]`. -/
theorem minimal_exp_representation (L chi0 beta : ℝ) (u v du dv : ℝ → ℝ)
    (hu_cont : ContinuousOn u (Icc 0 L)) (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hflux : ∀ x ∈ Ioo 0 L, du x = chi0 * (u x / (1 + v x) ^ beta) * dv x)
    (hg_cont : ContinuousOn (fun y => chi0 * dv y / (1 + v y) ^ beta) (Icc 0 L)) :
    ∀ x₀ ∈ Icc 0 L, ∀ x ∈ Icc 0 L,
      u x = u x₀ * Real.exp (∫ y in x₀..x, chi0 * dv y / (1 + v y) ^ beta) := by
  set g : ℝ → ℝ := fun y => chi0 * dv y / (1 + v y) ^ beta with hg_def
  intro x₀ hx₀ x hx
  have hL0 : 0 ≤ L := hx.1.trans hx.2
  have hint : IntervalIntegrable g MeasureTheory.volume 0 L := hg_cont.intervalIntegrable_of_Icc hL0
  have hprim : ContinuousOn (fun y => ∫ t in x₀..y, g t) (Icc 0 L) := by
    have := intervalIntegral.continuousOn_primitive_interval' hint
      (by rw [uIcc_of_le hL0]; exact hx₀)
    rwa [uIcc_of_le hL0] at this
  -- `log u - ∫_{x₀} g` is constant on `[0,L]`
  set F : ℝ → ℝ := fun y => Real.log (u y) - ∫ t in x₀..y, g t with hF_def
  have hFc : ContinuousOn F (Icc 0 L) :=
    (hu_cont.log fun y hy => (hu_pos y hy).ne').sub hprim
  have hFd : ∀ y ∈ Ioo 0 L, HasDerivAt F 0 y := by
    intro y hy
    have hyI : y ∈ Icc 0 L := Ioo_subset_Icc_self hy
    have hlog := (hdu y hy).log (hu_pos y hyI).ne'
    have hgy : ContinuousAt g y := hg_cont.continuousAt (Icc_mem_nhds hy.1 hy.2)
    have hftc := intervalIntegral.integral_hasDerivAt_right
      ((hg_cont.mono (uIcc_subset_Icc hx₀ hyI)).intervalIntegrable)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hg_cont.mono Ioo_subset_Icc_self) y hy)
      hgy
    have h := hlog.sub hftc
    convert h using 1
    rw [hflux y hy, hg_def]
    field_simp [(hu_pos y hyI).ne']
    ring
  have hconst := eq_left_of_hasDerivAt_zero hFc hFd
  have hx_eq : F x = F x₀ := (hconst x hx).trans (hconst x₀ hx₀).symm
  simp only [hF_def, intervalIntegral.integral_same, sub_zero] at hx_eq
  have hlog : Real.log (u x) = Real.log (u x₀) + ∫ t in x₀..x, g t := by linarith
  calc u x = Real.exp (Real.log (u x)) := (Real.exp_log (hu_pos x hx)).symm
    _ = u x₀ * Real.exp (∫ t in x₀..x, g t) := by
        rw [hlog, Real.exp_add, Real.exp_log (hu_pos x₀ hx₀)]

end ChemotaxisBifurcation.MinimalFlux
