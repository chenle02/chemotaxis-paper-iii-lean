module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
public import ChemotaxisBifurcation.MonotoneLocus

@[expose] public section

/-!
# General-exponent stationary monotonicity

Extends the existing m=1 ODE seam to u_x = χ u^m (1+v)^(-β) v_x.
Correspondence: frozen Paper III v2, Equation (4.18), page 32, and the
monotone-locus argument in the proof of Theorem 1.3(3).
Since profiles are strictly positive, the ODE deductions hold for every real m;
in particular they cover the manuscript range 1 ≤ m ≤ 2.

Reuses MonotoneLocus.linear_eq_zero, endpoint-margin and perturbation lemmas,
local-half-branch/constant-limit interfaces, and GlobalBranch consumers.
The stationary and clopen proofs adapt the existing proofs to the power flux.
No PDE compactness, local bifurcation expansion, or signal C² continuity is
claimed here: these remain explicit hypotheses of the locus consumers.
-/

set_option autoImplicit false
namespace ChemotaxisBifurcation.MonotoneLocusGeneral
open Set Filter Topology
open ChemotaxisBifurcation.Eigenmodes ChemotaxisBifurcation.GlobalBranch
open ChemotaxisBifurcation.MonotoneLocus

section Stationary


structure StationarySolution (χ μ ν γ β m L : ℝ) (u v y : ℝ → ℝ) : Prop where
  u_pos : ∀ x ∈ Icc 0 L, 0 < u x
  v_pos : ∀ x ∈ Icc 0 L, 0 < 1 + v x
  deriv_u : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (χ * (u x ^ m / (1 + v x) ^ β) * y x) (Icc 0 L) x
  deriv_v : ∀ x ∈ Icc 0 L, HasDerivWithinAt v (y x) (Icc 0 L) x
  deriv_y : ∀ x ∈ Icc 0 L, HasDerivWithinAt y (μ * v x - ν * u x ^ γ) (Icc 0 L) x
  bc_left : y 0 = 0
  bc_right : y L = 0


def IsConstOn (u : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ Icc 0 L, u x = u 0


noncomputable def coeff (χ μ ν γ β m : ℝ) (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  μ - ν * (χ * (u x ^ m / (1 + v x) ^ β) * γ * u x ^ (γ - 1))

namespace StationarySolution

variable {χ μ ν γ β m L : ℝ} {u v y : ℝ → ℝ}

theorem continuousOn_u (h : StationarySolution χ μ ν γ β m L u v y) :
    ContinuousOn u (Icc 0 L) :=
  fun x hx => (h.deriv_u x hx).continuousWithinAt

theorem continuousOn_v (h : StationarySolution χ μ ν γ β m L u v y) :
    ContinuousOn v (Icc 0 L) :=
  fun x hx => (h.deriv_v x hx).continuousWithinAt


theorem deriv_z (h : StationarySolution χ μ ν γ β m L u v y) :
    ∀ x ∈ Icc 0 L, HasDerivWithinAt (fun x => μ * v x - ν * u x ^ γ)
      (coeff χ μ ν γ β m u v x * y x) (Icc 0 L) x := by
  intro x hx
  have h1 := ((h.deriv_v x hx).const_mul μ).sub
    (((h.deriv_u x hx).rpow_const (p := γ) (Or.inl (h.u_pos x hx).ne')).const_mul ν)
  convert h1 using 1
  simp only [coeff]; ring

theorem continuousOn_coeff (h : StationarySolution χ μ ν γ β m L u v y) :
    ContinuousOn (coeff χ μ ν γ β m u v) (Icc 0 L) := by
  have hu := h.continuousOn_u
  have hv := h.continuousOn_v
  have hpow : ContinuousOn (fun x => (1 + v x) ^ β) (Icc 0 L) :=
    (continuousOn_const.add hv).rpow_const (fun x hx => Or.inl (h.v_pos x hx).ne')
  have hupow : ContinuousOn (fun x => u x ^ (γ - 1)) (Icc 0 L) :=
    hu.rpow_const (fun x hx => Or.inl (h.u_pos x hx).ne')
  have hdiv : ContinuousOn (fun x => u x ^ m / (1 + v x) ^ β) (Icc 0 L) :=
    (hu.rpow_const (fun x hx => Or.inl (h.u_pos x hx).ne')).div hpow (fun x hx => (Real.rpow_pos_of_pos (h.v_pos x hx) β).ne')
  exact continuousOn_const.sub (continuousOn_const.mul
    (((continuousOn_const.mul hdiv).mul continuousOn_const).mul hupow))


theorem eq_const_of_zero (h : StationarySolution χ μ ν γ β m L u v y) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc 0 L) (hy0 : y x₀ = 0) (hz0 : μ * v x₀ - ν * u x₀ ^ γ = 0) :
    ∀ x ∈ Icc 0 L, y x = 0 ∧ u x = u 0 := by
  have hyz := linear_eq_zero (z := fun x => μ * v x - ν * u x ^ γ) h.deriv_y h.deriv_z
    h.continuousOn_coeff hx₀ hy0 hz0
  have hc := constant_of_has_deriv_right_zero h.continuousOn_u (fun x hx => by
    have := (h.deriv_u x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hx)
    rwa [(hyz x (Ico_subset_Icc_self hx)).1, mul_zero] at this)
  exact fun x hx => ⟨(hyz x hx).1, hc x hx⟩


theorem factor_pos (h : StationarySolution χ μ ν γ β m L u v y) (hχ : 0 < χ) :
    ∀ x ∈ Icc 0 L, 0 < χ * (u x ^ m / (1 + v x) ^ β) :=
  fun x hx => mul_pos hχ (div_pos (Real.rpow_pos_of_pos (h.u_pos x hx) m) (Real.rpow_pos_of_pos (h.v_pos x hx) β))


theorem pos_L_of_not_const (hnc : ¬ IsConstOn u L) : 0 < L := by
  by_contra hL
  apply hnc
  intro x hx
  have : x = 0 := by linarith [hx.1, hx.2, not_lt.mp hL]
  rw [this]


/-- Every zero of the signal derivative is simple on a nonconstant solution,
including the Neumann endpoints. This derives nondegeneracy from the ODE. -/
theorem z_ne_zero_at (h : StationarySolution χ μ ν γ β m L u v y)
    (hnc : ¬ IsConstOn u L) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc 0 L) (hy0 : y x₀ = 0) :
    μ * v x₀ - ν * u x₀ ^ γ ≠ 0 := fun hz =>
  hnc fun x hx => (h.eq_const_of_zero hx₀ hy0 hz x hx).2

theorem z_ne_zero_left (h : StationarySolution χ μ ν γ β m L u v y) (hnc : ¬ IsConstOn u L) :
    μ * v 0 - ν * u 0 ^ γ ≠ 0 := fun hz =>
  hnc fun x hx => (h.eq_const_of_zero ⟨le_rfl, (pos_L_of_not_const hnc).le⟩ h.bc_left hz x hx).2


theorem z_ne_zero_right (h : StationarySolution χ μ ν γ β m L u v y) (hnc : ¬ IsConstOn u L) :
    μ * v L - ν * u L ^ γ ≠ 0 := fun hz =>
  hnc fun x hx => (h.eq_const_of_zero ⟨(pos_L_of_not_const hnc).le, le_rfl⟩ h.bc_right hz x hx).2


theorem sig_neg_of_antitoneOn (h : StationarySolution χ μ ν γ β m L u v y) (hχ : 0 < χ)
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


theorem sig_pos_of_monotoneOn (h : StationarySolution χ μ ν γ β m L u v y) (hχ : 0 < χ)
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


theorem strictAntiOn_of_sig_neg (h : StationarySolution χ μ ν γ β m L u v y) (hχ : 0 < χ)
    (hneg : ∀ x ∈ Ioo 0 L, y x < 0) : StrictAntiOn u (Icc 0 L) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 L) h.continuousOn_u
    (f' := fun x => χ * (u x ^ m / (1 + v x) ^ β) * y x) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx ⊢
    exact ((h.deriv_u x (Ioo_subset_Icc_self hx)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    exact mul_neg_of_pos_of_neg (h.factor_pos hχ x (Ioo_subset_Icc_self hx)) (hneg x hx)


theorem strictMonoOn_of_sig_pos (h : StationarySolution χ μ ν γ β m L u v y) (hχ : 0 < χ)
    (hpos : ∀ x ∈ Ioo 0 L, 0 < y x) : StrictMonoOn u (Icc 0 L) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 L) h.continuousOn_u
    (f' := fun x => χ * (u x ^ m / (1 + v x) ^ β) * y x) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx ⊢
    exact ((h.deriv_u x (Ioo_subset_Icc_self hx)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    exact mul_pos (h.factor_pos hχ x (Ioo_subset_Icc_self hx)) (hpos x hx)


theorem strictAntiOn_of_antitoneOn (h : StationarySolution χ μ ν γ β m L u v y) (hχ : 0 < χ)
    (hanti : AntitoneOn u (Icc 0 L)) (hnc : ¬ IsConstOn u L) : StrictAntiOn u (Icc 0 L) :=
  h.strictAntiOn_of_sig_neg hχ (h.sig_neg_of_antitoneOn hχ hanti hnc)


theorem strictMonoOn_of_monotoneOn (h : StationarySolution χ μ ν γ β m L u v y) (hχ : 0 < χ)
    (hmono : MonotoneOn u (Icc 0 L)) (hnc : ¬ IsConstOn u L) : StrictMonoOn u (Icc 0 L) :=
  h.strictMonoOn_of_sig_pos hχ (h.sig_pos_of_monotoneOn hχ hmono hnc)

end StationarySolution

end Stationary


section Clopen
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E]


theorem isClopen_decreasingLocus [T1Space E] (prof : E →+ (ℝ → ℝ)) {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hSol : ∀ q ∈ C, StationarySolution q.1 μ ν γ β m L (prof q.2) (sig q) (sigx q))
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


theorem isClopen_increasingLocus [T1Space E] (prof : E →+ (ℝ → ℝ)) {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hSol : ∀ q ∈ C, StationarySolution q.1 μ ν γ β m L (prof q.2) (sig q) (sigx q))
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


theorem part3_strictAnti_of_ode [T1Space E] (prof : E →+ (ℝ → ℝ)) {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hConn : IsPreconnected C) (hStarC : pStar ∈ C)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hSol : ∀ q ∈ C, StationarySolution q.1 μ ν γ β m L (prof q.2) (sig q) (sigx q))
    (hPt : ∀ x ∈ Icc 0 L, ContinuousOn (fun q : ℝ × E => prof q.2 x) C)
    (hC2 : ∀ p ∈ C, p ≠ pStar → SignalC2Close prof sig μ ν γ L C p)
    (hConst : ∀ p ∈ C, IsConstOn (prof p.2) L →
      p ∈ closure (C ∩ {q | StrictAntiOn (prof q.2) (Icc 0 L)}) →
      ConstLimitRep prof L (C ∩ {q | StrictAntiOn (prof q.2) (Icc 0 L)}) p pStar)
    (hStar : LocalHalfBranch prof L C pStar 1) :
    ∀ p ∈ C, p ≠ pStar → StrictAntiOn (prof p.2) (Icc 0 L) :=
  part3_strictAnti prof L hConn hStarC
    (isClopen_decreasingLocus prof hL sig sigx hχ hSol hPt hC2 hConst hStar)


theorem part3_strictMono_of_ode [T1Space E] (prof : E →+ (ℝ → ℝ)) {L μ ν γ β m : ℝ}
    (hL : 0 < L) {C : Set (ℝ × E)} {pStar : ℝ × E} (sig sigx : ℝ × E → ℝ → ℝ)
    (hConn : IsPreconnected C) (hStarC : pStar ∈ C)
    (hχ : ∀ q ∈ C, 0 < q.1)
    (hSol : ∀ q ∈ C, StationarySolution q.1 μ ν γ β m L (prof q.2) (sig q) (sigx q))
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


end ChemotaxisBifurcation.MonotoneLocusGeneral
