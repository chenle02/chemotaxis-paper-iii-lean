module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
public import ChemotaxisBifurcation.GlobalBranch
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Theorem 1.3(3): clopenness of the strictly monotone locus along `C₁^±`

TeX label `T:global-extension`(3) (statement, lines 934–952; proof, lines
3205–3319 of the October manuscript).

The minimal stationary system with `a = b = 0` and `m = 1` reads, after the
flux identity (Lemma 4.2(1), `MinimalFlux.minimal_flux_identity`),
`u_x = χ₀ u/(1+v)^β v_x`, `v_xx = μ v - ν u^γ`, `v_x(0) = v_x(L) = 0`
(TeX `E:y-eq`, lines 3240–3250).  This module formalizes the classical-ODE
content of the clopenness argument (TeX lines 3251–3297):

* **ODE uniqueness** (TeX lines 3251–3258).  With `y = v_x` and
  `z = μ v - ν u^γ = y_x`, the pair `(y, z)` solves the *linear* system
  `y' = z`, `z' = (μ - γ ν χ₀ u^{γ-1} u/(1+v)^β) y` with a coefficient that is
  continuous on `[0,L]`.  Mathlib's Gronwall uniqueness
  (`ODE_solution_unique_of_mem_Icc_right/left`) gives: `y(x₀) = z(x₀) = 0` at
  one point of `[0,L]` forces `y ≡ 0`, hence `u` is constant.
* **Closedness** (TeX lines 3289–3291).  A nonconstant solution whose profile
  is (non-strictly) decreasing has `v_x < 0` on `(0,L)`: an interior zero of
  `v_x ≤ 0` is a local maximum, so `v_xx` vanishes there too (Fermat) and
  uniqueness applies.  Hence it is strictly decreasing.  Pointwise limits of
  decreasing profiles are decreasing.
* **Simple endpoint zeros and openness** (TeX lines 3259–3264, 3291–3292).
  For a nonconstant solution `v_xx ≠ 0` at `x = 0, L`.  A quantitative margin
  `v_x(x) ≤ -c min(x, L-x)` follows, and it persists under `C⁰`-small
  perturbations of `v_xx` (the form in which the TeX uses `C²` convergence).
* **Near the bifurcation point** (TeX lines 3203–3230): a profile
  `u* + s cos(πx/L) + r` with `s > 0`, `r'(0) = r'(L) = 0` and
  `‖r''‖_∞ < 2πs/L²` is strictly decreasing.

The assembly `isClopen_decreasingLocus` delivers exactly the clopenness
hypothesis of `GlobalBranch.part3_strictAnti`; the analytic inputs (the
topology of the solution set: pointwise continuity of profiles, `C²`
convergence of nearby signals, the local bifurcation representation at
constant limits and at `(χ*, u*)`) stay explicit hypotheses.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.MonotoneLocus

open Set Filter Topology
open ChemotaxisBifurcation.Eigenmodes ChemotaxisBifurcation.GlobalBranch

section LinearUniqueness

/-- **Uniqueness for the linear second-order system** (TeX lines 3251–3258).
If `y' = z` and `z' = a y` on `[0,L]` (one-sided derivatives at the ends),
with `a` continuous on `[0,L]`, and `y(x₀) = z(x₀) = 0` for some
`x₀ ∈ [0,L]`, then `y ≡ z ≡ 0` on `[0,L]`.  Proved by Mathlib's Gronwall
uniqueness `ODE_solution_unique_of_mem_Icc_right/left` for the pair `(y,z)`,
whose vector field is Lipschitz with constant `max 1 ‖a‖_∞`. -/
theorem linear_eq_zero {L : ℝ} {y z a : ℝ → ℝ}
    (hy : ∀ x ∈ Icc 0 L, HasDerivWithinAt y (z x) (Icc 0 L) x)
    (hz : ∀ x ∈ Icc 0 L, HasDerivWithinAt z (a x * y x) (Icc 0 L) x)
    (ha : ContinuousOn a (Icc 0 L)) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc 0 L)
    (hy0 : y x₀ = 0) (hz0 : z x₀ = 0) :
    ∀ x ∈ Icc 0 L, y x = 0 ∧ z x = 0 := by
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  set K : NNReal := Real.toNNReal (max 1 A) with hK
  have hKval : (K : ℝ) = max 1 A := Real.coe_toNNReal _ (le_trans zero_le_one (le_max_left _ _))
  set V : ℝ → ℝ × ℝ → ℝ × ℝ := fun t p => (p.2, a t * p.1) with hV
  have hLip : ∀ t ∈ Icc 0 L, LipschitzOnWith K (V t) univ := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun p _ q _ => ?_
    simp only [hV, Prod.dist_eq, Real.dist_eq, hKval]
    have hat : |a t| ≤ A := by simpa using hA t ht
    have h1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
    have h2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
    have h0 : 0 ≤ max |p.1 - q.1| |p.2 - q.2| := le_trans (abs_nonneg _) h1
    refine max_le ?_ ?_
    · calc |p.2 - q.2| ≤ 1 * max |p.1 - q.1| |p.2 - q.2| := by linarith
        _ ≤ max 1 A * max |p.1 - q.1| |p.2 - q.2| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    · rw [← mul_sub, abs_mul]
      calc |a t| * |p.1 - q.1| ≤ A * max |p.1 - q.1| |p.2 - q.2| :=
            mul_le_mul hat h1 (abs_nonneg _) (le_trans (abs_nonneg _) hat)
        _ ≤ max 1 A * max |p.1 - q.1| |p.2 - q.2| :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) h0
  set f : ℝ → ℝ × ℝ := fun x => (y x, z x) with hf
  have hfd : ∀ x ∈ Icc 0 L, HasDerivWithinAt f (V x (f x)) (Icc 0 L) x :=
    fun x hx => (hy x hx).prodMk (hz x hx)
  have hfc : ContinuousOn f (Icc 0 L) := fun x hx => (hfd x hx).continuousWithinAt
  have hgd : ∀ x : ℝ, HasDerivWithinAt (fun _ : ℝ => (0 : ℝ × ℝ)) (V x 0) (Icc 0 L) x := by
    intro x
    have : V x 0 = 0 := by simp [hV]
    rw [this]; exact hasDerivWithinAt_const _ _ _
  have hgc : ContinuousOn (fun _ : ℝ => (0 : ℝ × ℝ)) (Icc 0 L) := continuousOn_const
  have hEq0 : f x₀ = 0 := by simp [hf, hy0, hz0]
  have hright : EqOn f (fun _ => (0 : ℝ × ℝ)) (Icc x₀ L) := by
    have hsub : Icc x₀ L ⊆ Icc 0 L := Icc_subset_Icc_left hx₀.1
    have hsub' : ∀ t ∈ Ico x₀ L, t ∈ Ico 0 L := fun t ht => ⟨hx₀.1.trans ht.1, ht.2⟩
    refine ODE_solution_unique_of_mem_Icc_right (v := V) (s := fun _ => univ) (K := K)
      (fun t ht => hLip t (Ico_subset_Icc_self (hsub' t ht)))
      (hfc.mono hsub) (fun t ht => ?_) (fun _ _ => mem_univ _)
      (hgc.mono hsub) (fun t ht => ?_) (fun _ _ => mem_univ _) hEq0
    · exact (hfd t (Ico_subset_Icc_self (hsub' t ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem (hsub' t ht))
    · exact (hgd t).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem (hsub' t ht))
  have hleft : EqOn f (fun _ => (0 : ℝ × ℝ)) (Icc 0 x₀) := by
    have hsub : Icc 0 x₀ ⊆ Icc 0 L := Icc_subset_Icc_right hx₀.2
    have hsub' : ∀ t ∈ Ioc 0 x₀, t ∈ Ioc 0 L := fun t ht => ⟨ht.1, ht.2.trans hx₀.2⟩
    refine ODE_solution_unique_of_mem_Icc_left (v := V) (s := fun _ => univ) (K := K)
      (fun t ht => hLip t (Ioc_subset_Icc_self (hsub' t ht)))
      (hfc.mono hsub) (fun t ht => ?_) (fun _ _ => mem_univ _)
      (hgc.mono hsub) (fun t ht => ?_) (fun _ _ => mem_univ _) hEq0
    · exact (hfd t (Ioc_subset_Icc_self (hsub' t ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem (hsub' t ht))
    · exact (hgd t).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem (hsub' t ht))
  intro x hx
  have hfx : f x = 0 := by
    rcases le_total x x₀ with h | h
    · exact hleft ⟨hx.1, h⟩
    · exact hright ⟨h, hx.2⟩
  simp only [hf, Prod.mk_eq_zero] at hfx
  exact hfx

end LinearUniqueness

section Stationary

/-- **The minimal stationary system with `m = 1`** (TeX `E:y-eq`, lines
3240–3250, after the flux identity `E:minimal-spike-flux`), as a classical
solution on `[0,L]` with one-sided derivatives at the endpoints:
`u_x = χ₀ (u/(1+v)^β) y`, `v_x = y`, `y_x = μ v - ν u^γ`, `y(0) = y(L) = 0`,
with `u > 0` and `1 + v > 0`.  Here `y = v_x`. -/
structure StationarySolution (χ μ ν γ β L : ℝ) (u v y : ℝ → ℝ) : Prop where
  u_pos : ∀ x ∈ Icc 0 L, 0 < u x
  v_pos : ∀ x ∈ Icc 0 L, 0 < 1 + v x
  deriv_u : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (χ * (u x / (1 + v x) ^ β) * y x) (Icc 0 L) x
  deriv_v : ∀ x ∈ Icc 0 L, HasDerivWithinAt v (y x) (Icc 0 L) x
  deriv_y : ∀ x ∈ Icc 0 L, HasDerivWithinAt y (μ * v x - ν * u x ^ γ) (Icc 0 L) x
  bc_left : y 0 = 0
  bc_right : y L = 0

/-- A profile is constant on `[0,L]`. -/
def IsConstOn (u : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ Icc 0 L, u x = u 0

/-- The coefficient `μ - ν χ₀ (u/(1+v)^β) γ u^{γ-1}` of the linear equation
`y_xx = coeff · y` (TeX `E:y-eq`, written as `y_xx + q y = 0` with `q = -coeff`). -/
noncomputable def coeff (χ μ ν γ β : ℝ) (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  μ - ν * (χ * (u x / (1 + v x) ^ β) * γ * u x ^ (γ - 1))

namespace StationarySolution

variable {χ μ ν γ β L : ℝ} {u v y : ℝ → ℝ}

theorem continuousOn_u (h : StationarySolution χ μ ν γ β L u v y) :
    ContinuousOn u (Icc 0 L) :=
  fun x hx => (h.deriv_u x hx).continuousWithinAt

theorem continuousOn_v (h : StationarySolution χ μ ν γ β L u v y) :
    ContinuousOn v (Icc 0 L) :=
  fun x hx => (h.deriv_v x hx).continuousWithinAt

/-- The second derivative of the signal: `(μ v - ν u^γ)_x = coeff · v_x`
(differentiating `E:y-eq`, TeX lines 3242–3249). -/
theorem deriv_z (h : StationarySolution χ μ ν γ β L u v y) :
    ∀ x ∈ Icc 0 L, HasDerivWithinAt (fun x => μ * v x - ν * u x ^ γ)
      (coeff χ μ ν γ β u v x * y x) (Icc 0 L) x := by
  intro x hx
  have h1 := ((h.deriv_v x hx).const_mul μ).sub
    (((h.deriv_u x hx).rpow_const (p := γ) (Or.inl (h.u_pos x hx).ne')).const_mul ν)
  convert h1 using 1
  simp only [coeff]; ring

theorem continuousOn_coeff (h : StationarySolution χ μ ν γ β L u v y) :
    ContinuousOn (coeff χ μ ν γ β u v) (Icc 0 L) := by
  have hu := h.continuousOn_u
  have hv := h.continuousOn_v
  have hpow : ContinuousOn (fun x => (1 + v x) ^ β) (Icc 0 L) :=
    (continuousOn_const.add hv).rpow_const (fun x hx => Or.inl (h.v_pos x hx).ne')
  have hupow : ContinuousOn (fun x => u x ^ (γ - 1)) (Icc 0 L) :=
    hu.rpow_const (fun x hx => Or.inl (h.u_pos x hx).ne')
  have hdiv : ContinuousOn (fun x => u x / (1 + v x) ^ β) (Icc 0 L) :=
    hu.div hpow (fun x hx => (Real.rpow_pos_of_pos (h.v_pos x hx) β).ne')
  exact continuousOn_const.sub (continuousOn_const.mul
    (((continuousOn_const.mul hdiv).mul continuousOn_const).mul hupow))

/-- **ODE uniqueness for the stationary system** (TeX lines 3251–3258):
`v_x(x₀) = v_xx(x₀) = 0` at one point `x₀ ∈ [0,L]` forces `v_x ≡ 0` and `u`
constant on `[0,L]`. -/
theorem eq_const_of_zero (h : StationarySolution χ μ ν γ β L u v y) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc 0 L) (hy0 : y x₀ = 0) (hz0 : μ * v x₀ - ν * u x₀ ^ γ = 0) :
    ∀ x ∈ Icc 0 L, y x = 0 ∧ u x = u 0 := by
  have hyz := linear_eq_zero (z := fun x => μ * v x - ν * u x ^ γ) h.deriv_y h.deriv_z
    h.continuousOn_coeff hx₀ hy0 hz0
  have hc := constant_of_has_deriv_right_zero h.continuousOn_u (fun x hx => by
    have := (h.deriv_u x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hx)
    rwa [(hyz x (Ico_subset_Icc_self hx)).1, mul_zero] at this)
  exact fun x hx => ⟨(hyz x hx).1, hc x hx⟩

/-- The chemotactic factor `χ₀ u/(1+v)^β` is positive when `χ₀ > 0`. -/
theorem factor_pos (h : StationarySolution χ μ ν γ β L u v y) (hχ : 0 < χ) :
    ∀ x ∈ Icc 0 L, 0 < χ * (u x / (1 + v x) ^ β) :=
  fun x hx => mul_pos hχ (div_pos (h.u_pos x hx) (Real.rpow_pos_of_pos (h.v_pos x hx) β))

/-- A nonconstant solution lives on a nondegenerate interval. -/
theorem pos_L_of_not_const (hnc : ¬ IsConstOn u L) : 0 < L := by
  by_contra hL
  apply hnc
  intro x hx
  have : x = 0 := by linarith [hx.1, hx.2, not_lt.mp hL]
  rw [this]

/-- **Endpoint nondegeneracy** (TeX lines 3259–3261, "every zero of `v_x` is
simple"): for a nonconstant solution, `v_xx(0) ≠ 0`. -/
theorem z_ne_zero_left (h : StationarySolution χ μ ν γ β L u v y) (hnc : ¬ IsConstOn u L) :
    μ * v 0 - ν * u 0 ^ γ ≠ 0 := fun hz =>
  hnc fun x hx => (h.eq_const_of_zero ⟨le_rfl, (pos_L_of_not_const hnc).le⟩ h.bc_left hz x hx).2

/-- **Endpoint nondegeneracy** at `x = L`: `v_xx(L) ≠ 0`. -/
theorem z_ne_zero_right (h : StationarySolution χ μ ν γ β L u v y) (hnc : ¬ IsConstOn u L) :
    μ * v L - ν * u L ^ γ ≠ 0 := fun hz =>
  hnc fun x hx => (h.eq_const_of_zero ⟨(pos_L_of_not_const hnc).le, le_rfl⟩ h.bc_right hz x hx).2

/-- **Interior sign for decreasing solutions** (TeX lines 3289–3291): a
nonconstant solution whose profile is (non-strictly) decreasing on `[0,L]`, with
`χ₀ > 0`, has `v_x < 0` on `(0,L)`.  An interior zero of `v_x ≤ 0` is a local
maximum, so `v_xx` vanishes there as well (Fermat), and ODE uniqueness makes
`u` constant. -/
theorem sig_neg_of_antitoneOn (h : StationarySolution χ μ ν γ β L u v y) (hχ : 0 < χ)
    (hanti : AntitoneOn u (Icc 0 L)) (hnc : ¬ IsConstOn u L) :
    ∀ x ∈ Ioo 0 L, y x < 0 := by
  have hL := pos_L_of_not_const hnc
  have hle : ∀ x ∈ Icc 0 L, y x ≤ 0 := by
    intro x hx
    have hd := (h.deriv_u x hx).derivWithin (uniqueDiffOn_Icc hL x hx)
    have h1 := hanti.derivWithin_nonpos (x := x)
    rw [hd] at h1
    by_contra hpos
    have := mul_pos (h.factor_pos hχ x hx) (lt_of_not_ge hpos)
    linarith
  intro x hx
  rcases (hle x (Ioo_subset_Icc_self hx)).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hmax : IsLocalMax y x := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with t ht
      rw [heq]; exact hle t ht
    have hz := hmax.hasDerivAt_eq_zero
      ((h.deriv_y x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    exact hnc fun t ht => (h.eq_const_of_zero (Ioo_subset_Icc_self hx) heq hz t ht).2

/-- **Interior sign for increasing solutions**: the mirror of
`sig_neg_of_antitoneOn`, with a local minimum of `v_x ≥ 0`. -/
theorem sig_pos_of_monotoneOn (h : StationarySolution χ μ ν γ β L u v y) (hχ : 0 < χ)
    (hmono : MonotoneOn u (Icc 0 L)) (hnc : ¬ IsConstOn u L) :
    ∀ x ∈ Ioo 0 L, 0 < y x := by
  have hL := pos_L_of_not_const hnc
  have hle : ∀ x ∈ Icc 0 L, 0 ≤ y x := by
    intro x hx
    have hd := (h.deriv_u x hx).derivWithin (uniqueDiffOn_Icc hL x hx)
    have h1 := hmono.derivWithin_nonneg (x := x)
    rw [hd] at h1
    by_contra hneg
    have := mul_neg_of_pos_of_neg (h.factor_pos hχ x hx) (lt_of_not_ge hneg)
    linarith
  intro x hx
  rcases (hle x (Ioo_subset_Icc_self hx)).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hmin : IsLocalMin y x := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with t ht
      rw [← heq]; exact hle t ht
    have hz := hmin.hasDerivAt_eq_zero
      ((h.deriv_y x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    exact hnc fun t ht => (h.eq_const_of_zero (Ioo_subset_Icc_self hx) heq.symm hz t ht).2

/-- A solution with `χ₀ > 0` and `v_x < 0` on `(0,L)` is strictly decreasing on
`[0,L]` (TeX lines 3226–3231: although `u_x(0) = u_x(L) = 0`, the integral of
`u_x` over any subinterval is negative). -/
theorem strictAntiOn_of_sig_neg (h : StationarySolution χ μ ν γ β L u v y) (hχ : 0 < χ)
    (hneg : ∀ x ∈ Ioo 0 L, y x < 0) : StrictAntiOn u (Icc 0 L) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 L) h.continuousOn_u
    (f' := fun x => χ * (u x / (1 + v x) ^ β) * y x) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx ⊢
    exact ((h.deriv_u x (Ioo_subset_Icc_self hx)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    exact mul_neg_of_pos_of_neg (h.factor_pos hχ x (Ioo_subset_Icc_self hx)) (hneg x hx)

/-- Mirror of `strictAntiOn_of_sig_neg`. -/
theorem strictMonoOn_of_sig_pos (h : StationarySolution χ μ ν γ β L u v y) (hχ : 0 < χ)
    (hpos : ∀ x ∈ Ioo 0 L, 0 < y x) : StrictMonoOn u (Icc 0 L) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 L) h.continuousOn_u
    (f' := fun x => χ * (u x / (1 + v x) ^ β) * y x) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx ⊢
    exact ((h.deriv_u x (Ioo_subset_Icc_self hx)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    exact mul_pos (h.factor_pos hχ x (Ioo_subset_Icc_self hx)) (hpos x hx)

/-- **Closedness, ODE part** (TeX lines 3289–3291): a nonconstant solution
with `χ₀ > 0` whose profile is (non-strictly) decreasing is strictly
decreasing. -/
theorem strictAntiOn_of_antitoneOn (h : StationarySolution χ μ ν γ β L u v y) (hχ : 0 < χ)
    (hanti : AntitoneOn u (Icc 0 L)) (hnc : ¬ IsConstOn u L) : StrictAntiOn u (Icc 0 L) :=
  h.strictAntiOn_of_sig_neg hχ (h.sig_neg_of_antitoneOn hχ hanti hnc)

/-- Mirror of `strictAntiOn_of_antitoneOn`. -/
theorem strictMonoOn_of_monotoneOn (h : StationarySolution χ μ ν γ β L u v y) (hχ : 0 < χ)
    (hmono : MonotoneOn u (Icc 0 L)) (hnc : ¬ IsConstOn u L) : StrictMonoOn u (Icc 0 L) :=
  h.strictMonoOn_of_sig_pos hχ (h.sig_pos_of_monotoneOn hχ hmono hnc)

end StationarySolution

end Stationary

section Margins

/-- Restriction of one-sided derivatives on `[0,L]` to two-sided derivatives on
the interior of a subinterval. -/
theorem hasDerivWithinAt_interior_sub {L a b : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 L, HasDerivWithinAt f (f' x) (Icc 0 L) x) (ha : 0 ≤ a) (hb : b ≤ L) :
    ∀ x ∈ interior (Icc a b), HasDerivWithinAt f (f' x) (interior (Icc a b)) x := by
  intro x hx
  rw [interior_Icc] at hx ⊢
  have hx' : x ∈ Ioo 0 L := ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
  exact ((hf x (Ioo_subset_Icc_self hx')).hasDerivAt (Icc_mem_nhds hx'.1 hx'.2)).hasDerivWithinAt

/-- **Mean-value bound with Neumann data** (TeX lines 3213–3217): if
`g(0) = g(L) = 0` and `|g'| ≤ δ` on `[0,L]`, then `|g(x)| ≤ δ min(x, L-x)`. -/
theorem abs_le_mul_min {L δ : ℝ} {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc 0 L, HasDerivWithinAt g (g' x) (Icc 0 L) x)
    (h0 : g 0 = 0) (hL0 : g L = 0) (hbound : ∀ x ∈ Icc 0 L, |g' x| ≤ δ) :
    ∀ x ∈ Icc 0 L, |g x| ≤ δ * min x (L - x) := by
  intro x hx
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hbound x hx)
  have hleft := norm_image_sub_le_of_norm_deriv_le_segment' hg
    (fun t ht => hbound t (Ico_subset_Icc_self ht)) x hx
  have hsub : Icc x L ⊆ Icc 0 L := Icc_subset_Icc_left hx.1
  have hright := norm_image_sub_le_of_norm_deriv_le_segment' (a := x) (b := L)
    (fun t ht => (hg t (hsub ht)).mono hsub)
    (fun t ht => hbound t (hsub (Ico_subset_Icc_self ht))) L ⟨hx.2, le_rfl⟩
  simp only [Real.norm_eq_abs, h0, hL0, sub_zero, zero_sub, abs_neg] at hleft hright
  rw [mul_min_of_nonneg _ _ hδ]
  exact le_min hleft hright

/-- `min(x, L-x) ≤ L/2`. -/
theorem min_le_half (x L : ℝ) : min x (L - x) ≤ L / 2 := by
  rcases le_total x (L - x) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- **Simple endpoint zeros give a linear margin** (TeX lines 3259–3264,
3291–3292).  If `f(0) = f(L) = 0`, `f < 0` on `(0,L)`, `f'` is continuous on
`[0,L]` and `f'(0) ≠ 0 ≠ f'(L)`, then `f(x) ≤ -c min(x, L-x)` for some
`c > 0`.  (The signs `f'(0) < 0 < f'(L)` are forced by `f < 0` inside.) -/
theorem exists_margin {L : ℝ} (hL : 0 < L) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 L, HasDerivWithinAt f (f' x) (Icc 0 L) x)
    (hf'c : ContinuousOn f' (Icc 0 L)) (h0 : f 0 = 0) (hL0 : f L = 0)
    (hneg : ∀ x ∈ Ioo 0 L, f x < 0) (hd0 : f' 0 ≠ 0) (hdL : f' L ≠ 0) :
    ∃ c > 0, ∀ x ∈ Icc 0 L, f x ≤ -c * min x (L - x) := by
  have m0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have mL : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
  have hfc : ContinuousOn f (Icc 0 L) := fun x hx => (hf x hx).continuousWithinAt
  -- continuity of `f'` at the endpoints, as a radius
  have radius : ∀ p ∈ Icc 0 L, ∀ (P : ℝ → Prop), (∀ᶠ t in 𝓝 (f' p), P t) →
      ∃ η > 0, ∀ x ∈ Icc 0 L, |x - p| < η → P (f' x) := by
    intro p hp P hP
    have hev : ∀ᶠ x in 𝓝[Icc 0 L] p, P (f' x) := (hf'c p hp).eventually hP
    obtain ⟨η, hη, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
    exact ⟨η, hη, fun x hx hd => hsub ⟨by rwa [Metric.mem_ball, Real.dist_eq], hx⟩⟩
  -- sign at `0`
  have hs0 : f' 0 < 0 := by
    rcases lt_or_gt_of_ne hd0 with h | hpos
    · exact h
    exfalso
    obtain ⟨η, hη, hP⟩ := radius 0 m0 (fun t => 0 < t) (lt_mem_nhds hpos)
    set t := min (η / 2) (L / 2) with ht
    have ht0 : 0 < t := lt_min (by linarith) (by linarith)
    have htL : t < L := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have htη : t < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hmono := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 t)
      (hfc.mono (Icc_subset_Icc_right htL.le))
      (hasDerivWithinAt_interior_sub hf le_rfl htL.le) (fun x hx => by
        rw [interior_Icc] at hx
        exact hP x ⟨hx.1.le, (hx.2.trans htL).le⟩
          (by rw [sub_zero, abs_of_pos hx.1]; linarith [hx.2]))
    have := hmono ⟨le_rfl, ht0.le⟩ ⟨ht0.le, le_rfl⟩ ht0
    have := hneg t ⟨ht0, htL⟩
    linarith
  -- sign at `L`
  have hsL : 0 < f' L := by
    rcases lt_or_gt_of_ne hdL with hn | h
    swap; · exact h
    exfalso
    obtain ⟨η, hη, hP⟩ := radius L mL (fun t => t < 0) (gt_mem_nhds hn)
    set t := max (L - η / 2) (L / 2) with ht
    have ht0 : 0 < t := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have htL : t < L := max_lt (by linarith) (by linarith)
    have htη : L - η < t := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hanti := strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc t L)
      (hfc.mono (Icc_subset_Icc_left ht0.le))
      (hasDerivWithinAt_interior_sub hf ht0.le le_rfl) (fun x hx => by
        rw [interior_Icc] at hx
        refine hP x ⟨(ht0.trans hx.1).le, hx.2.le⟩ ?_
        rw [abs_of_neg (by linarith [hx.2])]; linarith [hx.1])
    have := hanti ⟨le_rfl, htL.le⟩ ⟨htL.le, le_rfl⟩ htL
    have := hneg t ⟨ht0, htL⟩
    linarith
  -- margin near `0`
  set d0 := -f' 0 with hd0def
  have hd0pos : 0 < d0 := by linarith
  obtain ⟨η0, hη0, hP0⟩ := radius 0 m0 (fun t => t < -(d0 / 2))
    (gt_mem_nhds (by linarith))
  set a0 := min (η0 / 2) (L / 3) with ha0
  have ha0pos : 0 < a0 := lt_min (by linarith) (by linarith)
  have ha0L : a0 ≤ L / 3 := min_le_right _ _
  have hnear0 : ∀ x ∈ Icc 0 a0, f x ≤ -(d0 / 2) * x := by
    have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 a0)
      (f := fun x => f x + d0 / 2 * x) (f' := fun x => f' x + d0 / 2)
      ((hfc.mono (Icc_subset_Icc_right (by linarith))).add (by fun_prop))
      (fun x hx => (hasDerivWithinAt_interior_sub hf le_rfl (by linarith) x hx).add
        ((hasDerivWithinAt_id _ _).const_mul (d0 / 2) |>.congr_deriv (by ring)))
      (fun x hx => by
        rw [interior_Icc] at hx
        have := hP0 x ⟨hx.1.le, by linarith [hx.2]⟩
          (by rw [sub_zero, abs_of_pos hx.1]; linarith [hx.2, min_le_left (η0 / 2) (L / 3)])
        linarith)
    intro x hx
    have := hanti ⟨le_rfl, ha0pos.le⟩ hx hx.1
    simp only [h0, mul_zero, add_zero] at this
    linarith
  -- margin near `L`
  set d1 := f' L with hd1def
  obtain ⟨η1, hη1, hP1⟩ := radius L mL (fun t => d1 / 2 < t) (lt_mem_nhds (by linarith))
  set a1 := max (L - η1 / 2) (2 * L / 3) with ha1
  have ha1L : a1 < L := max_lt (by linarith) (by linarith)
  have ha1ge : 2 * L / 3 ≤ a1 := le_max_right _ _
  have hnearL : ∀ x ∈ Icc a1 L, f x ≤ -(d1 / 2) * (L - x) := by
    have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a1 L)
      (f := fun x => f x - d1 / 2 * x) (f' := fun x => f' x - d1 / 2)
      ((hfc.mono (Icc_subset_Icc_left (by linarith))).sub (by fun_prop))
      (fun x hx => (hasDerivWithinAt_interior_sub hf (by linarith) le_rfl x hx).sub
        ((hasDerivWithinAt_id _ _).const_mul (d1 / 2) |>.congr_deriv (by ring)))
      (fun x hx => by
        rw [interior_Icc] at hx
        have := hP1 x ⟨by linarith [hx.1], hx.2.le⟩
          (by rw [abs_of_neg (by linarith [hx.2])]
              linarith [hx.1, le_max_left (L - η1 / 2) (2 * L / 3)])
        linarith)
    intro x hx
    have := hmono hx ⟨ha1L.le, le_rfl⟩ hx.2
    simp only [hL0] at this
    linarith
  -- the middle
  have hmid_ne : (Icc a0 a1).Nonempty := ⟨a0, le_rfl, by linarith⟩
  obtain ⟨xm, hxm, hmax⟩ := isCompact_Icc.exists_isMaxOn hmid_ne
    (hfc.mono (Icc_subset_Icc ha0pos.le ha1L.le))
  set m := f xm with hm
  have hmneg : m < 0 := hneg xm ⟨lt_of_lt_of_le ha0pos hxm.1, lt_of_le_of_lt hxm.2 ha1L⟩
  refine ⟨min (d0 / 2) (min (d1 / 2) (-(2 * m / L))), ?_, ?_⟩
  · refine lt_min (by linarith) (lt_min (by linarith) ?_)
    have : 2 * m / L < 0 := div_neg_of_neg_of_pos (by linarith) hL
    linarith
  intro x hx
  set c := min (d0 / 2) (min (d1 / 2) (-(2 * m / L))) with hc
  have hc0 : c ≤ d0 / 2 := min_le_left _ _
  have hc1 : c ≤ d1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc2 : c ≤ -(2 * m / L) := (min_le_right _ _).trans (min_le_right _ _)
  have hmin0 : 0 ≤ min x (L - x) := le_min hx.1 (by linarith [hx.2])
  by_cases hxa0 : x ≤ a0
  · have h1 := hnear0 x ⟨hx.1, hxa0⟩
    have h2 : c * min x (L - x) ≤ d0 / 2 * x :=
      mul_le_mul hc0 (min_le_left _ _) hmin0 (by linarith)
    linarith
  by_cases hxa1 : a1 ≤ x
  · have h1 := hnearL x ⟨hxa1, hx.2⟩
    have h2 : c * min x (L - x) ≤ d1 / 2 * (L - x) :=
      mul_le_mul hc1 (min_le_right _ _) hmin0 (by linarith)
    linarith
  · rw [not_le] at hxa0 hxa1
    have h1 : f x ≤ m := hmax ⟨hxa0.le, hxa1.le⟩
    have h2 : c * min x (L - x) ≤ -(2 * m / L) * (L / 2) :=
      mul_le_mul hc2 (min_le_half x L) hmin0 (by
        have : 2 * m / L < 0 := div_neg_of_neg_of_pos (by linarith) hL
        linarith)
    have h3 : -(2 * m / L) * (L / 2) = -m := by field_simp
    linarith

/-- **Persistence of the margin under `C⁰`-small perturbation of the
derivative** (TeX lines 3218–3225, 3291–3292).  If `f₀(x) ≤ -c min(x, L-x)`,
`f(0) = f(L) = f₀(0) = f₀(L) = 0` and `|f' - f₀'| ≤ δ` on `[0,L]`, then
`f(x) ≤ -(c - δ) min(x, L-x)`. -/
theorem le_of_perturb {L c δ : ℝ} {f₀ f₀' f f' : ℝ → ℝ}
    (hf₀ : ∀ x ∈ Icc 0 L, HasDerivWithinAt f₀ (f₀' x) (Icc 0 L) x)
    (hf : ∀ x ∈ Icc 0 L, HasDerivWithinAt f (f' x) (Icc 0 L) x)
    (h00 : f₀ 0 = 0) (h0L : f₀ L = 0) (h0 : f 0 = 0) (hL0 : f L = 0)
    (hmargin : ∀ x ∈ Icc 0 L, f₀ x ≤ -c * min x (L - x))
    (hclose : ∀ x ∈ Icc 0 L, |f' x - f₀' x| ≤ δ) :
    ∀ x ∈ Icc 0 L, f x ≤ -(c - δ) * min x (L - x) := by
  intro x hx
  have hr := abs_le_mul_min (g := fun x => f x - f₀ x) (fun t ht => (hf t ht).sub (hf₀ t ht))
    (by simp [h0, h00]) (by simp [hL0, h0L]) hclose x hx
  have := (abs_le.mp hr).2
  have := hmargin x hx
  linarith

/-- **Openness, quantitative form**: under the hypotheses of `le_of_perturb`
with `δ < c`, the perturbed `f` is negative on `(0,L)`. -/
theorem neg_of_perturb {L c δ : ℝ} {f₀ f₀' f f' : ℝ → ℝ}
    (hf₀ : ∀ x ∈ Icc 0 L, HasDerivWithinAt f₀ (f₀' x) (Icc 0 L) x)
    (hf : ∀ x ∈ Icc 0 L, HasDerivWithinAt f (f' x) (Icc 0 L) x)
    (h00 : f₀ 0 = 0) (h0L : f₀ L = 0) (h0 : f 0 = 0) (hL0 : f L = 0)
    (hmargin : ∀ x ∈ Icc 0 L, f₀ x ≤ -c * min x (L - x))
    (hclose : ∀ x ∈ Icc 0 L, |f' x - f₀' x| ≤ δ) (hδc : δ < c) :
    ∀ x ∈ Ioo 0 L, f x < 0 := by
  intro x hx
  have := le_of_perturb hf₀ hf h00 h0L h0 hL0 hmargin hclose x (Ioo_subset_Icc_self hx)
  have hm : 0 < min x (L - x) := lt_min hx.1 (by linarith [hx.2])
  have : 0 < (c - δ) * min x (L - x) := mul_pos (by linarith) hm
  linarith

/-- **Jordan's inequality on `[0,L]`**: `sin(πx/L) ≥ (2/L) min(x, L-x)`
(TeX line 3218). -/
theorem two_div_mul_min_le_sin {L x : ℝ} (hL : 0 < L) (hx : x ∈ Icc 0 L) :
    2 / L * min x (L - x) ≤ Real.sin (Real.pi / L * x) := by
  have key : ∀ t ∈ Icc (0 : ℝ) (L / 2), 2 / L * t ≤ Real.sin (Real.pi / L * t) := by
    intro t ht
    have hθ0 : 0 ≤ Real.pi / L * t := mul_nonneg (div_pos Real.pi_pos hL).le ht.1
    have hθ1 : Real.pi / L * t ≤ Real.pi / 2 := by
      calc Real.pi / L * t ≤ Real.pi / L * (L / 2) :=
            mul_le_mul_of_nonneg_left ht.2 (div_pos Real.pi_pos hL).le
        _ = Real.pi / 2 := by field_simp
    have := Real.mul_le_sin hθ0 hθ1
    have e : 2 / Real.pi * (Real.pi / L * t) = 2 / L * t := by field_simp
    linarith
  rcases le_total x (L - x) with h | h
  · rw [min_eq_left h]; exact key x ⟨hx.1, by linarith⟩
  · rw [min_eq_right h]
    have e : Real.pi / L * x = Real.pi - Real.pi / L * (L - x) := by field_simp; ring
    rw [e, Real.sin_pi_sub]
    exact key (L - x) ⟨by linarith [hx.2], by linarith⟩

/-- **Monotonicity on the local half-branch** (TeX lines 3203–3231).  A profile
`c + s cos(πx/L) + r` with `s > 0`, `r'(0) = r'(L) = 0` and
`‖r''‖_∞ ≤ ε < 2πs/L²` is strictly decreasing on `[0,L]`. -/
theorem strictAntiOn_of_local_branch {L c s ε : ℝ} (hL : 0 < L) {r r' r'' : ℝ → ℝ}
    (hr : ∀ x ∈ Icc 0 L, HasDerivWithinAt r (r' x) (Icc 0 L) x)
    (hr' : ∀ x ∈ Icc 0 L, HasDerivWithinAt r' (r'' x) (Icc 0 L) x)
    (h0 : r' 0 = 0) (hL0 : r' L = 0) (hsmall : ∀ x ∈ Icc 0 L, |r'' x| ≤ ε)
    (hε : ε < 2 * Real.pi * s / L ^ 2) :
    StrictAntiOn (fun x => c + s * mode L 1 x + r x) (Icc 0 L) := by
  have hbound := abs_le_mul_min hr' h0 hL0 hsmall
  have hderiv : ∀ x, HasDerivAt (fun x => c + s * mode L 1 x)
      (s * (-Real.sin (Real.pi / L * x) * (Real.pi / L))) x := by
    intro x
    simp only [mode_one_eq]
    have := (((hasDerivAt_id x).const_mul (Real.pi / L)).cos).const_mul s |>.const_add c
    convert this using 1 <;> simp
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 L)
    (f' := fun x => s * (-Real.sin (Real.pi / L * x) * (Real.pi / L)) + r' x)
    (fun x hx => ((hderiv x).continuousAt.continuousWithinAt).add
      (hr x hx).continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
  · exact (hderiv x).hasDerivWithinAt.add (hasDerivWithinAt_interior_sub hr le_rfl le_rfl x hx)
  · rw [interior_Icc] at hx
    have hxI : x ∈ Icc 0 L := Ioo_subset_Icc_self hx
    have hm : 0 < min x (L - x) := lt_min hx.1 (by linarith [hx.2])
    have hsin := two_div_mul_min_le_sin hL hxI
    have hr'x := (abs_le.mp (hbound x hxI)).2
    have hs : 0 < s := by
      have : 0 ≤ ε := (abs_nonneg _).trans (hsmall x hxI)
      by_contra hs
      have : 2 * Real.pi * s / L ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos]) (by positivity)
      linarith
    have hk : 0 < s * (Real.pi / L) := mul_pos hs (div_pos Real.pi_pos hL)
    have h1 : s * (Real.pi / L) * (2 / L * min x (L - x)) ≤
        s * (Real.pi / L) * Real.sin (Real.pi / L * x) :=
      mul_le_mul_of_nonneg_left hsin hk.le
    have h2 : s * (Real.pi / L) * (2 / L * min x (L - x)) =
        2 * Real.pi * s / L ^ 2 * min x (L - x) := by field_simp
    have h3 : ε * min x (L - x) < 2 * Real.pi * s / L ^ 2 * min x (L - x) :=
      mul_lt_mul_of_pos_right hε hm
    nlinarith

end Margins

section Mirror

/-- Mirror of `strictAntiOn_of_local_branch` for the half-branch `s < 0`
(the component `C₁^-`, TeX line 3232). -/
theorem strictMonoOn_of_local_branch {L c s ε : ℝ} (hL : 0 < L) {r r' r'' : ℝ → ℝ}
    (hr : ∀ x ∈ Icc 0 L, HasDerivWithinAt r (r' x) (Icc 0 L) x)
    (hr' : ∀ x ∈ Icc 0 L, HasDerivWithinAt r' (r'' x) (Icc 0 L) x)
    (h0 : r' 0 = 0) (hL0 : r' L = 0) (hsmall : ∀ x ∈ Icc 0 L, |r'' x| ≤ ε)
    (hε : ε < 2 * Real.pi * (-s) / L ^ 2) :
    StrictMonoOn (fun x => c + s * mode L 1 x + r x) (Icc 0 L) := by
  have h := strictAntiOn_of_local_branch (c := -c) (r := fun x => -r x) (r' := fun x => -r' x)
    (r'' := fun x => -r'' x) hL (fun x hx => (hr x hx).neg) (fun x hx => (hr' x hx).neg)
    (by simp [h0]) (by simp [hL0]) (fun x hx => by simpa using hsmall x hx) hε
  intro x hx y hy hxy
  have := h hx hy hxy
  simp only at this ⊢
  linarith

/-- Mirror of `exists_margin` for a positive function. -/
theorem exists_margin_pos {L : ℝ} (hL : 0 < L) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 L, HasDerivWithinAt f (f' x) (Icc 0 L) x)
    (hf'c : ContinuousOn f' (Icc 0 L)) (h0 : f 0 = 0) (hL0 : f L = 0)
    (hpos : ∀ x ∈ Ioo 0 L, 0 < f x) (hd0 : f' 0 ≠ 0) (hdL : f' L ≠ 0) :
    ∃ c > 0, ∀ x ∈ Icc 0 L, -f x ≤ -c * min x (L - x) :=
  exists_margin (f := fun x => -f x) (f' := fun x => -f' x) hL (fun x hx => (hf x hx).neg)
    hf'c.neg (by simp [h0]) (by simp [hL0]) (fun x hx => by simpa using hpos x hx)
    (neg_ne_zero.mpr hd0) (neg_ne_zero.mpr hdL)

end Mirror

section Clopen

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E]

/-- **Local bifurcation representation at a constant limit** (TeX lines
3265–3279): the constant point `p` is approached by a sequence of points of `D`
whose profiles are `c + s_j φ_n + r_j` with `s_j ≠ 0` and
`sup |r_j| ≤ ε_j |s_j|`, `ε_j → 0`, at some mode `n ≥ 1`, and the mode-one
bifurcation point is `p*`.  This packages the implicit function theorem
(excluding nondegenerate `χ̂`) and the Shi–Wang local simple-eigenvalue
theorem; it does not assert `n = 1`, which is derived from monotonicity by
`GlobalBranch.mode_eq_one_of_monotone_limit`. -/
def ConstLimitRep (prof : E →+ (ℝ → ℝ)) (L : ℝ) (D : Set (ℝ × E)) (p pStar : ℝ × E) :
    Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ (n = 1 → p = pStar) ∧
    ∃ (q : ℕ → ℝ × E) (r : ℕ → ℝ → ℝ) (s ε : ℕ → ℝ) (c : ℝ),
      (∀ j, q j ∈ D) ∧ (∀ j x, prof (q j).2 x = c + s j * mode L n x + r j x) ∧
      (∀ j, s j ≠ 0) ∧ (∀ j, ∀ x ∈ Icc 0 L, |r j x| ≤ ε j * |s j|) ∧
      Tendsto ε atTop (𝓝 0)

/-- **The local half-branch at `p* = (χ*, u*)`** (TeX lines 3203–3212 and
3292–3293): near `p*`, every other point of `C` has profile
`c + s cos(πx/L) + r_s` on the selected half-arc (`sgn · s > 0`), with Neumann
data `r_s'(0) = r_s'(L) = 0` and `‖r_s''‖_∞ = o(|s|)`.  This is the output of
the local bifurcation theorem plus local uniqueness and removal of the opposite
half-arc. -/
def LocalHalfBranch (prof : E →+ (ℝ → ℝ)) (L : ℝ) (C : Set (ℝ × E)) (pStar : ℝ × E)
    (sgn : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ q in 𝓝[C] pStar, q = pStar ∨
    ∃ (c s : ℝ) (r r' r'' : ℝ → ℝ), 0 < sgn * s ∧
      (∀ x, prof q.2 x = c + s * mode L 1 x + r x) ∧
      (∀ x ∈ Icc 0 L, HasDerivWithinAt r (r' x) (Icc 0 L) x) ∧
      (∀ x ∈ Icc 0 L, HasDerivWithinAt r' (r'' x) (Icc 0 L) x) ∧
      r' 0 = 0 ∧ r' L = 0 ∧ ∀ x ∈ Icc 0 L, |r'' x| ≤ ε * |s|

/-- **`C²` convergence of nearby signals** (TeX lines 3289–3292: convergence in
the admissible `H²` topology bootstraps to `C²` convergence for stationary
solutions near a positive limit), in the form used: `v_xx = μ v - ν u^γ`
converges uniformly on `[0,L]` as `q → p` within `C`. -/
def SignalC2Close (prof : E →+ (ℝ → ℝ)) (sig : ℝ × E → ℝ → ℝ) (μ ν γ L : ℝ)
    (C : Set (ℝ × E)) (p : ℝ × E) : Prop :=
  ∀ δ > 0, ∀ᶠ q in 𝓝[C] p, ∀ x ∈ Icc 0 L,
    |(μ * sig q x - ν * prof q.2 x ^ γ) - (μ * sig p x - ν * prof p.2 x ^ γ)| ≤ δ

omit [AddCommGroup E] in
/-- Topological bookkeeping: a point of `C` in the closure of `C ∩ M`, other
than `p*`, lies in the closure of `C ∩ {strict}`, where `M = {p*} ∪ {strict}`. -/
theorem mem_closure_strict_of_locus [T1Space E] {C A : Set (ℝ × E)} {pStar p : ℝ × E}
    (hp : p ∈ closure (C ∩ {q | q = pStar ∨ q ∈ A})) (hne : p ≠ pStar) :
    p ∈ closure (C ∩ A) := by
  have hsub : C ∩ {q | q = pStar ∨ q ∈ A} ⊆ {pStar} ∪ (C ∩ A) := by
    rintro q ⟨hqC, rfl | hqA⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hqC, hqA⟩
  have := closure_mono hsub hp
  rw [closure_union, closure_singleton] at this
  rcases this with h | h
  · exact absurd h hne
  · exact h

omit [AddCommGroup E] in
/-- Pointwise limits (within `C`) of monotone-type inequalities persist. -/
theorem le_of_mem_closure {C D : Set (ℝ × E)} (hDC : D ⊆ C) {p : ℝ × E} (hpC : p ∈ C)
    (hp : p ∈ closure D) {F G : ℝ × E → ℝ} (hF : ContinuousOn F C) (hG : ContinuousOn G C)
    (hle : ∀ q ∈ D, F q ≤ G q) : F p ≤ G p :=
  ContinuousWithinAt.closure_le hp ((hF p hpC).mono hDC) ((hG p hpC).mono hDC) hle

/-- **Clopenness of the decreasing locus** (TeX lines 3281–3297): under the
analytic inputs below, `{p*} ∪ {strictly decreasing}` is relatively open and
closed in `C`.  This is exactly the hypothesis `hClopen` of
`GlobalBranch.part3_strictAnti`.

Inputs: `L > 0`; every point of `C` is a classical solution of the minimal
stationary system (`hSol`, signal `sig`, signal derivative `sigx`) with
`χ₀ > 0` (`hχ`); profile evaluation is continuous on `C` (`hPt`, from
`H² ↪ C⁰`); nearby signals converge in `C²` (`hC2`); constant limits carry
the local bifurcation representation (`hConst`); near `p*` the component is the
positive half-branch (`hStar`).  ODE content proved here: closedness via
`StationarySolution.strictAntiOn_of_antitoneOn`, openness via `exists_margin`
and `neg_of_perturb`, the base point via `strictAntiOn_of_local_branch`, and the
mode selection via `mode_eq_one_of_monotone_limit`. -/
theorem isClopen_decreasingLocus [T1Space E] (prof : E →+ (ℝ → ℝ)) {L μ ν γ β : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hSol : ∀ q ∈ C, StationarySolution q.1 μ ν γ β L (prof q.2) (sig q) (sigx q))
    (hPt : ∀ x ∈ Icc 0 L, ContinuousOn (fun q : ℝ × E => prof q.2 x) C)
    (hC2 : ∀ p ∈ C, p ≠ pStar → SignalC2Close prof sig μ ν γ L C p)
    (hConst : ∀ p ∈ C, IsConstOn (prof p.2) L →
      p ∈ closure (C ∩ {q | StrictAntiOn (prof q.2) (Icc 0 L)}) →
      ConstLimitRep prof L (C ∩ {q | StrictAntiOn (prof q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch prof L C pStar 1) :
    IsClopen (((↑) : C → ℝ × E) ⁻¹' DecreasingLocus prof L pStar) := by
  set SD : Set (ℝ × E) := {q | StrictAntiOn (prof q.2) (Icc 0 L)} with hSD
  constructor
  · -- closedness
    refine closure_subset_iff_isClosed.mp fun z hz => ?_
    rw [closure_subtype, Subtype.image_preimage_coe] at hz
    set p : ℝ × E := (z : ℝ × E)
    have hpC : p ∈ C := z.property
    show p = pStar ∨ StrictAntiOn (prof p.2) (Icc 0 L)
    by_cases hne : p = pStar
    · exact Or.inl hne
    right
    have hcl : p ∈ closure (C ∩ SD) := mem_closure_strict_of_locus hz hne
    have hanti : AntitoneOn (prof p.2) (Icc 0 L) := by
      intro a ha b hb hab
      exact le_of_mem_closure inter_subset_left hpC hcl (hPt b hb) (hPt a ha)
        (fun q hq => hq.2.antitoneOn ha hb hab)
    by_cases hc : IsConstOn (prof p.2) L
    · exfalso
      obtain ⟨n, hn, hn1, q, r, s, ε, c, hqD, hrep, hs, hr, hε⟩ := hConst p hpC hc hcl
      have := mode_eq_one_of_monotone_limit hL hn (fun j => prof (q j).2) r s ε hrep hs hr hε
        (fun j => Or.inr (hqD j).2.antitoneOn)
      exact hne (hn1 this)
    · exact (hSol p hpC).strictAntiOn_of_antitoneOn (hχ p hpC) hanti hc
  · -- openness
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hev : ∀ᶠ q in 𝓝[C] (z : ℝ × E), q ∈ DecreasingLocus prof L pStar := by
      set p : ℝ × E := (z : ℝ × E)
      have hpC : p ∈ C := z.property
      by_cases hp : p = pStar
      · -- the bifurcation point
        have hεpos : (0 : ℝ) < Real.pi / L ^ 2 := by positivity
        rw [hp]
        filter_upwards [hStar _ hεpos] with q hq
        rcases hq with rfl | ⟨c, s, r, r', r'', hs, hprof, hr, hr', h0, hL0, hsmall⟩
        · exact Or.inl rfl
        right
        rw [one_mul] at hs
        have hfun : prof q.2 = fun x => c + s * mode L 1 x + r x := funext hprof
        rw [hfun]
        refine strictAntiOn_of_local_branch hL hr hr' h0 hL0 hsmall ?_
        rw [abs_of_pos hs]
        rw [div_mul_eq_mul_div, div_lt_div_iff_of_pos_right (by positivity)]
        nlinarith [Real.pi_pos]
      · -- a strictly decreasing point
        have hstrict : StrictAntiOn (prof p.2) (Icc 0 L) := hz.resolve_left hp
        have hnc : ¬ IsConstOn (prof p.2) L := fun hc => by
          have h1 := hstrict ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL
          rw [hc L ⟨hL.le, le_rfl⟩] at h1
          exact lt_irrefl _ h1
        have hS := hSol p hpC
        have hzc : ContinuousOn (fun x => μ * sig p x - ν * prof p.2 x ^ γ) (Icc 0 L) :=
          fun x hx => (hS.deriv_z x hx).continuousWithinAt
        obtain ⟨c, hc, hmargin⟩ := exists_margin (f := sigx p)
          (f' := fun x => μ * sig p x - ν * prof p.2 x ^ γ) hL hS.deriv_y hzc hS.bc_left
          hS.bc_right (hS.sig_neg_of_antitoneOn (hχ p hpC) hstrict.antitoneOn hnc)
          (hS.z_ne_zero_left hnc) (hS.z_ne_zero_right hnc)
        filter_upwards [hC2 p hpC hp (c / 2) (by linarith), self_mem_nhdsWithin] with q hq hqC
        right
        have hSq := hSol q hqC
        exact hSq.strictAntiOn_of_sig_neg (hχ q hqC)
          (neg_of_perturb (f₀ := sigx p) (f₀' := fun x => μ * sig p x - ν * prof p.2 x ^ γ)
            (f := sigx q) (f' := fun x => μ * sig q x - ν * prof q.2 x ^ γ)
            hS.deriv_y hSq.deriv_y hS.bc_left hS.bc_right hSq.bc_left hSq.bc_right hmargin hq
            (by linarith))
    exact (eventually_nhds_subtype_iff C z _).mpr hev

/-- **Clopenness of the increasing locus** along `C₁^-` (TeX lines 3281–3297,
"the analogous argument for `C₁^-`"): the mirror of
`isClopen_decreasingLocus`, with the negative half-branch (`sgn = -1`) at
`p*`.  This is exactly the hypothesis `hClopen` of
`GlobalBranch.part3_strictMono`. -/
theorem isClopen_increasingLocus [T1Space E] (prof : E →+ (ℝ → ℝ)) {L μ ν γ β : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hSol : ∀ q ∈ C, StationarySolution q.1 μ ν γ β L (prof q.2) (sig q) (sigx q))
    (hPt : ∀ x ∈ Icc 0 L, ContinuousOn (fun q : ℝ × E => prof q.2 x) C)
    (hC2 : ∀ p ∈ C, p ≠ pStar → SignalC2Close prof sig μ ν γ L C p)
    (hConst : ∀ p ∈ C, IsConstOn (prof p.2) L →
      p ∈ closure (C ∩ {q | StrictMonoOn (prof q.2) (Icc 0 L)}) →
      ConstLimitRep prof L (C ∩ {q | StrictMonoOn (prof q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch prof L C pStar (-1)) :
    IsClopen (((↑) : C → ℝ × E) ⁻¹' IncreasingLocus prof L pStar) := by
  set SI : Set (ℝ × E) := {q | StrictMonoOn (prof q.2) (Icc 0 L)} with hSI
  constructor
  · refine closure_subset_iff_isClosed.mp fun z hz => ?_
    rw [closure_subtype, Subtype.image_preimage_coe] at hz
    set p : ℝ × E := (z : ℝ × E)
    have hpC : p ∈ C := z.property
    show p = pStar ∨ StrictMonoOn (prof p.2) (Icc 0 L)
    by_cases hne : p = pStar
    · exact Or.inl hne
    right
    have hcl : p ∈ closure (C ∩ SI) := mem_closure_strict_of_locus hz hne
    have hmono : MonotoneOn (prof p.2) (Icc 0 L) := by
      intro a ha b hb hab
      exact le_of_mem_closure inter_subset_left hpC hcl (hPt a ha) (hPt b hb)
        (fun q hq => hq.2.monotoneOn ha hb hab)
    by_cases hc : IsConstOn (prof p.2) L
    · exfalso
      obtain ⟨n, hn, hn1, q, r, s, ε, c, hqD, hrep, hs, hr, hε⟩ := hConst p hpC hc hcl
      have := mode_eq_one_of_monotone_limit hL hn (fun j => prof (q j).2) r s ε hrep hs hr hε
        (fun j => Or.inl (hqD j).2.monotoneOn)
      exact hne (hn1 this)
    · exact (hSol p hpC).strictMonoOn_of_monotoneOn (hχ p hpC) hmono hc
  · refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hev : ∀ᶠ q in 𝓝[C] (z : ℝ × E), q ∈ IncreasingLocus prof L pStar := by
      set p : ℝ × E := (z : ℝ × E)
      have hpC : p ∈ C := z.property
      by_cases hp : p = pStar
      · have hεpos : (0 : ℝ) < Real.pi / L ^ 2 := by positivity
        rw [hp]
        filter_upwards [hStar _ hεpos] with q hq
        rcases hq with rfl | ⟨c, s, r, r', r'', hs, hprof, hr, hr', h0, hL0, hsmall⟩
        · exact Or.inl rfl
        right
        have hs' : s < 0 := by linarith
        have hfun : prof q.2 = fun x => c + s * mode L 1 x + r x := funext hprof
        rw [hfun]
        refine strictMonoOn_of_local_branch hL hr hr' h0 hL0 hsmall ?_
        rw [abs_of_neg hs']
        rw [div_mul_eq_mul_div, div_lt_div_iff_of_pos_right (by positivity)]
        nlinarith [Real.pi_pos]
      · have hstrict : StrictMonoOn (prof p.2) (Icc 0 L) := hz.resolve_left hp
        have hnc : ¬ IsConstOn (prof p.2) L := fun hc => by
          have h1 := hstrict ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL
          rw [hc L ⟨hL.le, le_rfl⟩] at h1
          exact lt_irrefl _ h1
        have hS := hSol p hpC
        have hzc : ContinuousOn (fun x => μ * sig p x - ν * prof p.2 x ^ γ) (Icc 0 L) :=
          fun x hx => (hS.deriv_z x hx).continuousWithinAt
        obtain ⟨c, hc, hmargin⟩ := exists_margin_pos (f := sigx p)
          (f' := fun x => μ * sig p x - ν * prof p.2 x ^ γ) hL hS.deriv_y hzc hS.bc_left
          hS.bc_right (hS.sig_pos_of_monotoneOn (hχ p hpC) hstrict.monotoneOn hnc)
          (hS.z_ne_zero_left hnc) (hS.z_ne_zero_right hnc)
        filter_upwards [hC2 p hpC hp (c / 2) (by linarith), self_mem_nhdsWithin] with q hq hqC
        right
        have hSq := hSol q hqC
        refine hSq.strictMonoOn_of_sig_pos (hχ q hqC) fun x hx => ?_
        have := neg_of_perturb (f₀ := fun x => -sigx p x)
          (f₀' := fun x => -(μ * sig p x - ν * prof p.2 x ^ γ))
          (f := fun x => -sigx q x) (f' := fun x => -(μ * sig q x - ν * prof q.2 x ^ γ))
          (fun x hx => (hS.deriv_y x hx).neg) (fun x hx => (hSq.deriv_y x hx).neg)
          (by simp [hS.bc_left]) (by simp [hS.bc_right]) (by simp [hSq.bc_left])
          (by simp [hSq.bc_right]) hmargin
          (fun x hx => by rw [neg_sub_neg, abs_sub_comm]; exact hq x hx) (by linarith) x hx
        linarith
    exact (eventually_nhds_subtype_iff C z _).mpr hev

/-- **Theorem 1.3(3), monotonicity on `C₁^+`, from the ODE inputs** (TeX lines
939–942, 3240–3297): `GlobalBranch.part3_strictAnti` with its clopenness
hypothesis discharged by `isClopen_decreasingLocus`. -/
theorem part3_strictAnti_of_ode [T1Space E] (prof : E →+ (ℝ → ℝ)) {L μ ν γ β : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hConn : IsPreconnected C) (hStarC : pStar ∈ C)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hSol : ∀ q ∈ C, StationarySolution q.1 μ ν γ β L (prof q.2) (sig q) (sigx q))
    (hPt : ∀ x ∈ Icc 0 L, ContinuousOn (fun q : ℝ × E => prof q.2 x) C)
    (hC2 : ∀ p ∈ C, p ≠ pStar → SignalC2Close prof sig μ ν γ L C p)
    (hConst : ∀ p ∈ C, IsConstOn (prof p.2) L →
      p ∈ closure (C ∩ {q | StrictAntiOn (prof q.2) (Icc 0 L)}) →
      ConstLimitRep prof L (C ∩ {q | StrictAntiOn (prof q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch prof L C pStar 1) :
    ∀ p ∈ C, p ≠ pStar → StrictAntiOn (prof p.2) (Icc 0 L) :=
  part3_strictAnti prof L hConn hStarC
    (isClopen_decreasingLocus prof hL sig sigx hχ hSol hPt hC2 hConst hStar)

/-- **Theorem 1.3(3), monotonicity on `C₁^-`, from the ODE inputs**:
`GlobalBranch.part3_strictMono` with its clopenness hypothesis discharged by
`isClopen_increasingLocus`. -/
theorem part3_strictMono_of_ode [T1Space E] (prof : E →+ (ℝ → ℝ)) {L μ ν γ β : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hConn : IsPreconnected C) (hStarC : pStar ∈ C)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hSol : ∀ q ∈ C, StationarySolution q.1 μ ν γ β L (prof q.2) (sig q) (sigx q))
    (hPt : ∀ x ∈ Icc 0 L, ContinuousOn (fun q : ℝ × E => prof q.2 x) C)
    (hC2 : ∀ p ∈ C, p ≠ pStar → SignalC2Close prof sig μ ν γ L C p)
    (hConst : ∀ p ∈ C, IsConstOn (prof p.2) L →
      p ∈ closure (C ∩ {q | StrictMonoOn (prof q.2) (Icc 0 L)}) →
      ConstLimitRep prof L (C ∩ {q | StrictMonoOn (prof q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch prof L C pStar (-1)) :
    ∀ p ∈ C, p ≠ pStar → StrictMonoOn (prof p.2) (Icc 0 L) :=
  part3_strictMono prof L hConn hStarC
    (isClopen_increasingLocus prof hL sig sigx hχ hSol hPt hC2 hConst hStar)

end Clopen

end ChemotaxisBifurcation.MonotoneLocus
