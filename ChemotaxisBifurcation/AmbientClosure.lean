module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
public import ChemotaxisBifurcation.GlobalBranch
public import ChemotaxisBifurcation.IntervalMoments
public import ChemotaxisBifurcation.MinimalFlux

@[expose] public section

/-!
# Admissibility of finite limits

The historical draft called this Lemma 4.3 (`L:ambient-closure`). That label is
absent from arXiv v1 and frozen v2. In v2 the corresponding positivity and
zero-sensitivity exclusion occur in the proofs of Theorem 1.3(2)–(3), source
lines 2899–2921 and 3040–3064, with Remark 1.1(2). Equation (1.20) alone uses
relative closure in `ℝ × A`, so it must not be identified with the stronger
ambient-closure conclusion below. Subsequent historical line numbers describe
the original proof packet, not current manuscript locators.

The manuscript proves `closure S ⊆ V` (closure in `ℝ × H²(0,L)`) for `m ≥ 1`.
This module formalizes every finite, real-analysis or calculus step of that
proof and keeps the genuinely analytic inputs as named hypotheses:

* `hLimit` — passage to the limit in the stationary equation (convergence of
  the signals in `C²`, TeX lines 3123–3125): limits of solutions are solutions;
* `hSMP` — the strong maximum principle with Neumann conditions for the
  limiting linear equation with bounded coefficients (TeX lines 3126–3139);
  `limit_coeffs_bounded` proves the boundedness of those coefficients, which is
  where `m ≥ 1` enters;
* `hIFT` — the implicit-function-theorem local uniqueness at `(0, u*)` (TeX
  lines 3150–3157): stationary solutions near `(0, u*)` are trivial;
* the embedding `H² ↪ C⁰([0,L])` as a continuous map `prof : E → C([0,L], ℝ)`,
  its injectivity, and (for the specialized assemblies) the classical
  `C²` regularity of the zero-sensitivity limit and the mass identities.

What is proved here:
* `χ̄ ≥ 0`, `ū ≥ 0`, `max ū ≥ u*` and the affine constraint pass to the limit
  (closedness in the compact-open topology, no sequences or metrizability);
* `max u ≥ u*` for solutions: from the prescribed average (minimal model) and
  from the logistic mass identity (non-minimal model, the content of
  Lemma 4.1(1) used at TeX line 3121, including constant profiles);
* the zero-sensitivity uniqueness `ū ≡ u*`: the energy identity of TeX lines
  3141–3147 (non-minimal) and `ū_xx = 0` with Neumann data and prescribed
  average (minimal, TeX line 3142);
* exclusion of `χ̄ = 0` from local uniqueness, hence `χ̄ > 0`;
* `closure S ⊆ V`, in the exact form `GlobalBranch` consumes it, and the
  corresponding versions of Theorem 1.3(2),(3) with that hypothesis discharged.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.AmbientClosure

open Set Filter Topology MeasureTheory

/-! ## Function-level deductions on `[0,L]` -/

section Profiles

/-- A continuous profile on `[0,L]` with average `u*` (that is,
`∫_0^L u = L u*`) attains a value `≥ u*` (its maximum). This is the
"prescribed average" step for `a = b = 0` at TeX line 3121. -/
theorem exists_ge_mean (L uStar : ℝ) (u : ℝ → ℝ) (hL : 0 < L)
    (hu : ContinuousOn u (Icc 0 L)) (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) :
    ∃ y ∈ Icc 0 L, uStar ≤ u y := by
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hL.le) hu
  refine ⟨y, hy, ?_⟩
  have h := IntervalMoments.integral_le_of_le hL.le hu (fun z hz => hmax hz)
  rw [hmass] at h
  exact le_of_mul_le_mul_left h hL

/-- For `a, b, α > 0` and `u* = (a/b)^(1/α)`, a continuous positive profile on
`[0,L]` satisfying the logistic mass identity `a ∫_0^L u = b ∫_0^L u^(1+α)`
(TeX `E:mass-identity`, the PDE input) attains a value `≥ u*`.  This is the use
of Lemma 4.1(1) (`L:spiky-solu-lm1`) at TeX line 3121; unlike Lemma 4.1(1) it
needs no nonconstancy, so it also covers constant profiles. -/
theorem logistic_exists_ge_uStar (a b alpha L : ℝ) (u : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hmass : a * ∫ x in (0 : ℝ)..L, u x = b * ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha)) :
    ∃ x ∈ Icc 0 L, (a / b) ^ (1 / alpha) ≤ u x := by
  set uStar := (a / b) ^ (1 / alpha) with huStar_def
  have hab : 0 < a / b := div_pos ha hb
  have hequil : uStar ^ alpha = a / b := by
    rw [huStar_def, one_div, Real.rpow_inv_rpow hab.le halpha.ne']
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hg_pos : ∀ x ∈ Icc 0 L, 0 < u x * (uStar ^ alpha - u x ^ alpha) := fun x hx =>
    mul_pos (hpos x hx)
      (sub_pos.mpr (Real.rpow_lt_rpow (hpos x hx).le (hcon x hx) halpha))
  have hg_cont : ContinuousOn (fun x => u x * (uStar ^ alpha - u x ^ alpha)) (Icc 0 L) :=
    hcont.mul (continuousOn_const.sub (hcont.rpow_const fun _ _ => Or.inr halpha.le))
  have hpowc : ContinuousOn (fun x => u x ^ (1 + alpha)) (Icc 0 L) :=
    hcont.rpow_const fun _ _ => Or.inr (by linarith)
  have hg_int : ∫ x in (0 : ℝ)..L, u x * (uStar ^ alpha - u x ^ alpha) = 0 := by
    have e1 : ∫ x in (0 : ℝ)..L, u x * (uStar ^ alpha - u x ^ alpha) =
        ∫ x in (0 : ℝ)..L, (uStar ^ alpha * u x - u x ^ (1 + alpha)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hL.le] at hx
      simp only [Real.rpow_add (hpos x hx), Real.rpow_one]
      ring
    rw [e1, intervalIntegral.integral_sub
      ((hcont.intervalIntegrable_of_Icc hL.le).const_mul _)
      (hpowc.intervalIntegrable_of_Icc hL.le), intervalIntegral.integral_const_mul, hequil]
    have : a / b * ∫ x in (0 : ℝ)..L, u x = ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) := by
      field_simp
      linarith
    linarith
  have := intervalIntegral.intervalIntegral_pos_of_pos_on
    (hg_cont.intervalIntegrable_of_Icc hL.le) (fun x hx => hg_pos x (Ioo_subset_Icc_self hx)) hL
  linarith

/-- **Zero-sensitivity uniqueness, non-minimal model** (TeX lines 3141–3147).
Let `a, b, α > 0`, `u* = (a/b)^(1/α)`, and let `u` be a positive `C²` profile
on `[0,L]` solving `u_xx + a u - b u^(1+α) = 0` on `(0,L)` with
`u_x(0) = u_x(L) = 0`.  Testing with `u - u*` gives
`0 = ∫_0^L (u_x² + b u (u - u*)(u^α - (u*)^α))` with both terms nonnegative
(the manuscript's display, with the sign written out), so `u ≡ u*`. -/
theorem logistic_zero_sensitivity_eq (a b alpha L : ℝ) (u du ddu : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hu : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x) (hdu_cont : ContinuousOn du (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hstat : ∀ x ∈ Ioo 0 L, ddu x + a * u x - b * u x ^ (1 + alpha) = 0)
    (hbc0 : du 0 = 0) (hbcL : du L = 0) :
    ∀ x ∈ Icc 0 L, u x = (a / b) ^ (1 / alpha) := by
  set uStar := (a / b) ^ (1 / alpha) with huStar_def
  have hab : 0 < a / b := div_pos ha hb
  have huStar : 0 < uStar := Real.rpow_pos_of_pos hab _
  have hequil : uStar ^ alpha = a / b := by
    rw [huStar_def, one_div, Real.rpow_inv_rpow hab.le halpha.ne']
  have hA : b * uStar ^ alpha = a := by rw [hequil]; field_simp
  -- the factor `(u - u*)(u^α - u*^α)` is nonnegative, and zero only at `u*`
  have hfac_nonneg : ∀ x ∈ Icc 0 L,
      0 ≤ (u x - uStar) * (u x ^ alpha - uStar ^ alpha) := by
    intro x hx
    rcases le_total (u x) uStar with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
        (sub_nonpos.mpr (Real.rpow_le_rpow (hpos x hx).le h halpha.le))
    · exact mul_nonneg (by linarith) (sub_nonneg.mpr (Real.rpow_le_rpow huStar.le h halpha.le))
  set g : ℝ → ℝ := fun x =>
    du x ^ 2 + b * (u x * ((u x - uStar) * (u x ^ alpha - uStar ^ alpha))) with hg_def
  have hg_cont : ContinuousOn g (Icc 0 L) :=
    (hdu_cont.pow 2).add (continuousOn_const.mul (hu.mul ((hu.sub continuousOn_const).mul
      ((hu.rpow_const fun _ _ => Or.inr halpha.le).sub continuousOn_const))))
  have hg_nonneg : ∀ x ∈ Icc 0 L, 0 ≤ g x := fun x hx =>
    add_nonneg (sq_nonneg _) (mul_nonneg hb.le (mul_nonneg (hpos x hx).le (hfac_nonneg x hx)))
  have hg_int : ∫ x in (0 : ℝ)..L, g x = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL.le
      (f := fun x => (u x - uStar) * du x) ((hu.sub continuousOn_const).mul hdu_cont)
      (fun x hx => ?_) (hg_cont.intervalIntegrable_of_Icc hL.le)]
    · simp [hbc0, hbcL]
    · have hd := ((hdu x hx).sub_const uStar).mul (hddu x hx)
      convert hd using 1
      have hux := hpos x (Ioo_subset_Icc_self hx)
      have hs : ddu x = b * (u x * u x ^ alpha) - a * u x := by
        have := hstat x hx
        rw [Real.rpow_add hux, Real.rpow_one] at this
        linarith
      simp only [hg_def]
      linear_combination (-(u x - uStar)) * hs - (u x - uStar) * u x * hA
  have hzero := IntervalMoments.eq_zero_of_integral_eq_zero hL hg_cont hg_nonneg hg_int
  intro x hx
  have hgx := hzero x hx
  have h2 : b * (u x * ((u x - uStar) * (u x ^ alpha - uStar ^ alpha))) = 0 := by
    have h1 : 0 ≤ du x ^ 2 := sq_nonneg _
    have h3 := mul_nonneg hb.le (mul_nonneg (hpos x hx).le (hfac_nonneg x hx))
    simp only [hg_def] at hgx
    linarith
  have hprod : (u x - uStar) * (u x ^ alpha - uStar ^ alpha) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hb.ne')).resolve_left (hpos x hx).ne'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := Real.rpow_lt_rpow (hpos x hx).le hlt halpha
    have : 0 < (u x - uStar) * (u x ^ alpha - uStar ^ alpha) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    linarith
  · have := Real.rpow_lt_rpow huStar.le hgt halpha
    have : 0 < (u x - uStar) * (u x ^ alpha - uStar ^ alpha) :=
      mul_pos (by linarith) (by linarith)
    linarith

/-- **Zero-sensitivity uniqueness, minimal model** (TeX line 3142): a `C²`
profile with `u_xx = 0` on `(0,L)`, `u_x(0) = 0` and prescribed average
`∫_0^L u = L u*` is identically `u*` on `[0,L]`.  (Only the Neumann condition
at `0` is used.) -/
theorem minimal_zero_sensitivity_eq (L uStar : ℝ) (u du ddu : ℝ → ℝ) (hL : 0 < L)
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hdu_cont : ContinuousOn du (Icc 0 L)) (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hstat : ∀ x ∈ Ioo 0 L, ddu x = 0) (hbc0 : du 0 = 0)
    (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) :
    ∀ x ∈ Icc 0 L, u x = uStar := by
  have hdu0 : ∀ x ∈ Icc 0 L, du x = 0 := by
    intro x hx
    rw [MinimalFlux.eq_left_of_hasDerivAt_zero hdu_cont
      (fun y hy => by simpa [hstat y hy] using hddu y hy) x hx, hbc0]
  have hconst : ∀ x ∈ Icc 0 L, u x = u 0 :=
    MinimalFlux.eq_left_of_hasDerivAt_zero hu (fun y hy => by
      have := hdu y hy
      rwa [hdu0 y (Ioo_subset_Icc_self hy)] at this)
  have hint : ∫ x in (0 : ℝ)..L, u x = L * u 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => u 0) (fun x hx => by
      rw [uIcc_of_le hL.le] at hx; exact hconst x hx)]
    simp
  have h0 : u 0 = uStar := mul_left_cancel₀ hL.ne' (hint.symm.trans hmass)
  intro x hx
  rw [hconst x hx, h0]

/-- The drift coefficient `d = χ m u^(m-1) v_x / (1+v)^β` of the limiting
linear equation (TeX lines 3128–3131). -/
noncomputable def driftCoeff (chi m beta : ℝ) (u v dv : ℝ → ℝ) (x : ℝ) : ℝ :=
  chi * m * u x ^ (m - 1) * dv x / (1 + v x) ^ beta

/-- The zeroth-order coefficient
`c = a - b u^α - χ u^(m-1) (v_xx/(1+v)^β - β v_x²/(1+v)^(β+1))` of the
limiting linear equation (TeX lines 3128–3134). -/
noncomputable def zeroCoeff (a b alpha chi m beta : ℝ) (u v dv ddv : ℝ → ℝ) (x : ℝ) : ℝ :=
  a - b * u x ^ alpha -
    chi * u x ^ (m - 1) * (ddv x / (1 + v x) ^ beta - beta * dv x ^ 2 / (1 + v x) ^ (beta + 1))

/-- **Bounded coefficients for `m ≥ 1`** (TeX lines 3135–3137): for a
continuous nonnegative limit `ū` and a `C²` signal with `1 + v̄ > 0`, the
coefficients `d, c` are bounded on `[0,L]`; `ū^(m-1)` is continuous even at
zeros of `ū` because `m - 1 ≥ 0`.  This is the input the strong maximum
principle (hypothesis `hSMP` below) requires. -/
theorem limit_coeffs_bounded (L a b alpha chi m beta : ℝ) (u v dv ddv : ℝ → ℝ)
    (hm : 1 ≤ m) (halpha : 0 < alpha)
    (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hv1 : ∀ x ∈ Icc 0 L, 0 < 1 + v x)
    (hdv : ContinuousOn dv (Icc 0 L)) (hddv : ContinuousOn ddv (Icc 0 L)) :
    ∃ K : ℝ, ∀ x ∈ Icc 0 L,
      |driftCoeff chi m beta u v dv x| ≤ K ∧ |zeroCoeff a b alpha chi m beta u v dv ddv x| ≤ K := by
  have hum : ContinuousOn (fun x => u x ^ (m - 1)) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr (by linarith)
  have hua : ContinuousOn (fun x => u x ^ alpha) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr halpha.le
  have hw : ContinuousOn (fun x => 1 + v x) (Icc 0 L) := continuousOn_const.add hv
  have hwb : ContinuousOn (fun x => (1 + v x) ^ beta) (Icc 0 L) :=
    hw.rpow_const fun x hx => Or.inl (hv1 x hx).ne'
  have hwb1 : ContinuousOn (fun x => (1 + v x) ^ (beta + 1)) (Icc 0 L) :=
    hw.rpow_const fun x hx => Or.inl (hv1 x hx).ne'
  have hne : ∀ x ∈ Icc 0 L, (1 + v x) ^ beta ≠ 0 := fun x hx =>
    (Real.rpow_pos_of_pos (hv1 x hx) _).ne'
  have hne1 : ∀ x ∈ Icc 0 L, (1 + v x) ^ (beta + 1) ≠ 0 := fun x hx =>
    (Real.rpow_pos_of_pos (hv1 x hx) _).ne'
  have hd : ContinuousOn (driftCoeff chi m beta u v dv) (Icc 0 L) :=
    ((continuousOn_const.mul hum).mul hdv).div hwb hne
  have hc : ContinuousOn (zeroCoeff a b alpha chi m beta u v dv ddv) (Icc 0 L) :=
    (continuousOn_const.sub (continuousOn_const.mul hua)).sub
      ((continuousOn_const.mul hum).mul ((hddv.div hwb hne).sub
        ((continuousOn_const.mul (hdv.pow 2)).div hwb1 hne1)))
  obtain ⟨K₁, hK₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  obtain ⟨K₂, hK₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max K₁ K₂, fun x hx => ⟨?_, ?_⟩⟩
  · exact (Real.norm_eq_abs _ ▸ hK₁ x hx).trans (le_max_left _ _)
  · exact (Real.norm_eq_abs _ ▸ hK₂ x hx).trans (le_max_right _ _)

end Profiles

/-! ## The ambient closure, abstractly -/

section Closure

variable {E : Type*} [TopologicalSpace E] {L : ℝ}

/-- The admissible set `V = (0,∞) × A` with `A = {u ∈ Aff : u > 0 on [0,L]}`
(TeX lines 855–876, `E:A-eq`): `Aff` is the affine constraint `u - u* ∈ X`
and `prof : E → C([0,L], ℝ)` the embedding `H²(0,L) ↪ C⁰([0,L])`. -/
def admissibleSet (prof : E → C(Icc (0 : ℝ) L, ℝ)) (Aff : Set E) : Set (ℝ × E) :=
  Ioi 0 ×ˢ (Aff ∩ {u | ∀ x, 0 < prof u x})

/-- Nonnegativity on a compact interval is closed under uniform convergence. -/
theorem isClosed_setOf_forall_nonneg {K : Type*} [TopologicalSpace K] :
    IsClosed {f : C(K, ℝ) | ∀ x, 0 ≤ f x} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun x =>
    isClosed_le continuous_const (continuous_eval_const x)

/-- "`max f ≥ c`" is closed in the compact-open topology over a compact domain:
the complement `{f | f < c everywhere}` is a basic open set.  This is the step
"uniform convergence gives `max ū ≥ u*`" (TeX line 3122). -/
theorem isClosed_setOf_exists_ge {K : Type*} [TopologicalSpace K] [CompactSpace K] (c : ℝ) :
    IsClosed {f : C(K, ℝ) | ∃ x, c ≤ f x} := by
  have h : {f : C(K, ℝ) | ∃ x, c ≤ f x} = {f : C(K, ℝ) | MapsTo f univ (Iio c)}ᶜ := by
    ext f
    simp [MapsTo]
  rw [h]
  exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ isOpen_Iio).isClosed_compl

/-- **The closed conditions pass to limits** (TeX lines 3119–3122): every
point of the ambient closure of `S` has `χ̄ ≥ 0`, satisfies the affine
constraint, is nonnegative on `[0,L]`, and attains a value `≥ u*`. -/
theorem closure_subset_limitConditions
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {S : Set (ℝ × E)} {cStar : ℝ}
    (hProf : Continuous prof) (hAff : IsClosed Aff)
    (hS : S ⊆ admissibleSet prof Aff) (hMax : ∀ p ∈ S, ∃ x, cStar ≤ prof p.2 x) :
    ∀ p ∈ closure S, 0 ≤ p.1 ∧ p.2 ∈ Aff ∧ (∀ x, 0 ≤ prof p.2 x) ∧
      ∃ x, cStar ≤ prof p.2 x := by
  set Z : Set (ℝ × E) := {p | 0 ≤ p.1} ∩ (Prod.snd ⁻¹' Aff) ∩
    (fun p : ℝ × E => prof p.2) ⁻¹' {f | ∀ x, 0 ≤ f x} ∩
    (fun p : ℝ × E => prof p.2) ⁻¹' {f | ∃ x, cStar ≤ f x} with hZ
  have hcont : Continuous fun p : ℝ × E => prof p.2 := hProf.comp continuous_snd
  have hZc : IsClosed Z :=
    (((isClosed_le continuous_const continuous_fst).inter (hAff.preimage continuous_snd)).inter
      (isClosed_setOf_forall_nonneg.preimage hcont)).inter
      ((isClosed_setOf_exists_ge cStar).preimage hcont)
  have hSZ : S ⊆ Z := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hS hp
    exact ⟨⟨⟨(le_of_lt (show (0 : ℝ) < p.1 from h1) : 0 ≤ p.1), h2⟩, fun x => (h3 x).le⟩, hMax p hp⟩
  intro p hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := closure_minimal hSZ hZc hp
  exact ⟨h1, h2, h3, h4⟩

/-- **Exclusion of zero sensitivity** (TeX lines 3140–3158): if solutions near
`(0, u*)` are trivial (`hIFT`, implicit function theorem) and the points of
`S` are nonconstant, then `(0, u*)` is not in the closure of `S`. -/
theorem zero_trivial_not_mem_closure {S Sol : Set (ℝ × E)} {uStar : E}
    (hSSol : S ⊆ Sol) (hSne : ∀ p ∈ S, p.2 ≠ uStar)
    (hIFT : ∀ᶠ p in 𝓝 ((0 : ℝ), uStar), p ∈ Sol → p.2 = uStar) :
    ((0 : ℝ), uStar) ∉ closure S := by
  intro hp
  obtain ⟨q, hqS, hq⟩ := ((mem_closure_iff_frequently.mp hp).and_eventually hIFT).exists
  exact hSne q hqS (hq (hSSol hqS))

/-- **Lemma 4.3 (`L:ambient-closure`), abstract form** (TeX lines 3114–3159):
`closure S ⊆ V`.

Analytic inputs (explicit hypotheses):
* `hProf`: `H² ↪ C⁰([0,L])` is continuous; `hAff`: `u* + X` is closed;
* `hMax`: `max u ≥ u*` on `S` (see `exists_ge_mean`,
  `logistic_exists_ge_uStar`);
* `hLimit`: limits of solutions solve the stationary system (TeX 3123–3125);
* `hSMP`: strong maximum principle with Neumann conditions (TeX 3126–3139);
* `hZero`: positive admissible solutions at `χ = 0` equal `u*` (TeX
  3140–3147; see `logistic_zero_sensitivity_eq`, `minimal_zero_sensitivity_eq`);
* `hIFT`: implicit-function local uniqueness at `(0, u*)` (TeX 3148–3157). -/
theorem closure_subset_admissible
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {S Sol : Set (ℝ × E)}
    {uStar : E} {cStar : ℝ}
    (hProf : Continuous prof) (hAff : IsClosed Aff) (hc : 0 < cStar)
    (hS : S ⊆ admissibleSet prof Aff) (hSne : ∀ p ∈ S, p.2 ≠ uStar)
    (hMax : ∀ p ∈ S, ∃ x, cStar ≤ prof p.2 x)
    (hSSol : S ⊆ Sol) (hLimit : closure S ⊆ Sol)
    (hSMP : ∀ p ∈ Sol, 0 ≤ p.1 → p.2 ∈ Aff → (∀ x, 0 ≤ prof p.2 x) →
      (∃ x, 0 < prof p.2 x) → ∀ x, 0 < prof p.2 x)
    (hZero : ∀ u, ((0 : ℝ), u) ∈ Sol → u ∈ Aff → (∀ x, 0 < prof u x) → u = uStar)
    (hIFT : ∀ᶠ p in 𝓝 ((0 : ℝ), uStar), p ∈ Sol → p.2 = uStar) :
    closure S ⊆ admissibleSet prof Aff := by
  intro p hp
  obtain ⟨h0, hA, hnn, x₀, hx₀⟩ := closure_subset_limitConditions hProf hAff hS hMax p hp
  have hpos : ∀ x, 0 < prof p.2 x :=
    hSMP p (hLimit hp) h0 hA hnn ⟨x₀, lt_of_lt_of_le hc hx₀⟩
  refine ⟨?_, hA, hpos⟩
  rcases eq_or_lt_of_le h0 with hz | hz
  · exfalso
    have hpeq : p = ((0 : ℝ), p.2) := Prod.ext hz.symm rfl
    have hu : p.2 = uStar := hZero p.2 (hpeq ▸ hLimit hp) hA hpos
    apply zero_trivial_not_mem_closure hSSol hSne hIFT
    rw [← hu, ← hpeq]
    exact hp
  · exact hz

/-- The profile of `u` extended from `[0,L]` to `ℝ` (constantly outside), the
function to which the real-analysis lemmas are applied. -/
noncomputable def profFun (hL : (0 : ℝ) ≤ L) (prof : E → C(Icc (0 : ℝ) L, ℝ)) (u : E) :
    ℝ → ℝ :=
  IccExtend hL (prof u)

omit [TopologicalSpace E] in
theorem profFun_continuousOn (hL : (0 : ℝ) ≤ L) (prof : E → C(Icc (0 : ℝ) L, ℝ)) (u : E) :
    ContinuousOn (profFun hL prof u) (Icc 0 L) :=
  (continuous_IccExtend_iff.mpr (prof u).continuous).continuousOn

omit [TopologicalSpace E] in
theorem profFun_of_mem (hL : (0 : ℝ) ≤ L) (prof : E → C(Icc (0 : ℝ) L, ℝ)) (u : E)
    {x : ℝ} (hx : x ∈ Icc 0 L) : profFun hL prof u x = prof u ⟨x, hx⟩ :=
  IccExtend_of_mem hL _ hx

/-- **Lemma 4.3, minimal model** (`a = b = 0`, TeX lines 3114–3159): `hMax`
and `hZero` of `closure_subset_admissible` are derived from the prescribed
average `∫_0^L u = L u*` on `S` and on `Aff`, and from the `C²` form of the
zero-sensitivity equation `u_xx = 0` with `u_x(0) = 0` (elliptic regularity
kept as hypothesis `hReg0`); `hInj` is injectivity of `H² ↪ C⁰`. -/
theorem closure_subset_admissible_minimal
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {S Sol : Set (ℝ × E)}
    {uStar : E} {cStar : ℝ} (hL : 0 < L)
    (hProf : Continuous prof) (hAff : IsClosed Aff) (hc : 0 < cStar)
    (hS : S ⊆ admissibleSet prof Aff) (hSne : ∀ p ∈ S, p.2 ≠ uStar)
    (hMassS : ∀ p ∈ S, ∫ x in (0 : ℝ)..L, profFun hL.le prof p.2 x = L * cStar)
    (hSSol : S ⊆ Sol) (hLimit : closure S ⊆ Sol)
    (hSMP : ∀ p ∈ Sol, 0 ≤ p.1 → p.2 ∈ Aff → (∀ x, 0 ≤ prof p.2 x) →
      (∃ x, 0 < prof p.2 x) → ∀ x, 0 < prof p.2 x)
    (hReg0 : ∀ u, ((0 : ℝ), u) ∈ Sol → u ∈ Aff → ∃ du ddu : ℝ → ℝ,
      (∀ x ∈ Ioo 0 L, HasDerivAt (profFun hL.le prof u) (du x) x) ∧
      ContinuousOn du (Icc 0 L) ∧ (∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x) ∧
      (∀ x ∈ Ioo 0 L, ddu x = 0) ∧ du 0 = 0 ∧
      ∫ x in (0 : ℝ)..L, profFun hL.le prof u x = L * cStar)
    (hInj : ∀ u, (∀ x, prof u x = cStar) → u = uStar)
    (hIFT : ∀ᶠ p in 𝓝 ((0 : ℝ), uStar), p ∈ Sol → p.2 = uStar) :
    closure S ⊆ admissibleSet prof Aff := by
  refine closure_subset_admissible hProf hAff hc hS hSne ?_ hSSol hLimit hSMP ?_ hIFT
  · intro p hp
    obtain ⟨y, hy, hle⟩ :=
      exists_ge_mean L cStar _ hL (profFun_continuousOn hL.le prof p.2) (hMassS p hp)
    exact ⟨⟨y, hy⟩, by rwa [profFun_of_mem hL.le prof p.2 hy] at hle⟩
  · intro u hu hA _
    obtain ⟨du, ddu, h1, h2, h3, h4, h5, h6⟩ := hReg0 u hu hA
    have heq := minimal_zero_sensitivity_eq L cStar _ du ddu hL
      (profFun_continuousOn hL.le prof u) h1 h2 h3 h4 h5 h6
    exact hInj u fun x => by rw [← profFun_of_mem hL.le prof u x.2]; exact heq x x.2

/-- **Lemma 4.3, non-minimal model** (`a, b > 0`, TeX lines 3114–3159), with
`u* = (a/b)^(1/α)`: `hMax` is derived from the logistic mass identity on `S`
(`E:mass-identity`) and `hZero` from the energy identity for the `C²`
zero-sensitivity equation `u_xx + a u - b u^(1+α) = 0` with Neumann data
(elliptic regularity kept as hypothesis `hReg0`). -/
theorem closure_subset_admissible_logistic
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {S Sol : Set (ℝ × E)}
    {uStar : E} {a b alpha : ℝ} (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hProf : Continuous prof) (hAff : IsClosed Aff)
    (hS : S ⊆ admissibleSet prof Aff) (hSne : ∀ p ∈ S, p.2 ≠ uStar)
    (hMassS : ∀ p ∈ S, a * ∫ x in (0 : ℝ)..L, profFun hL.le prof p.2 x =
      b * ∫ x in (0 : ℝ)..L, profFun hL.le prof p.2 x ^ (1 + alpha))
    (hSSol : S ⊆ Sol) (hLimit : closure S ⊆ Sol)
    (hSMP : ∀ p ∈ Sol, 0 ≤ p.1 → p.2 ∈ Aff → (∀ x, 0 ≤ prof p.2 x) →
      (∃ x, 0 < prof p.2 x) → ∀ x, 0 < prof p.2 x)
    (hReg0 : ∀ u, ((0 : ℝ), u) ∈ Sol → u ∈ Aff → ∃ du ddu : ℝ → ℝ,
      (∀ x ∈ Ioo 0 L, HasDerivAt (profFun hL.le prof u) (du x) x) ∧
      ContinuousOn du (Icc 0 L) ∧ (∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x) ∧
      (∀ x ∈ Ioo 0 L, ddu x + a * profFun hL.le prof u x -
        b * profFun hL.le prof u x ^ (1 + alpha) = 0) ∧ du 0 = 0 ∧ du L = 0)
    (hInj : ∀ u, (∀ x, prof u x = (a / b) ^ (1 / alpha)) → u = uStar)
    (hIFT : ∀ᶠ p in 𝓝 ((0 : ℝ), uStar), p ∈ Sol → p.2 = uStar) :
    closure S ⊆ admissibleSet prof Aff := by
  have hc : 0 < (a / b) ^ (1 / alpha) := Real.rpow_pos_of_pos (div_pos ha hb) _
  have hposF : ∀ u : E, (∀ x, 0 < prof u x) → ∀ x ∈ Icc 0 L, 0 < profFun hL.le prof u x :=
    fun u hu x hx => by rw [profFun_of_mem hL.le prof u hx]; exact hu _
  refine closure_subset_admissible hProf hAff hc hS hSne ?_ hSSol hLimit hSMP ?_ hIFT
  · intro p hp
    obtain ⟨y, hy, hle⟩ := logistic_exists_ge_uStar a b alpha L _ ha hb halpha hL
      (profFun_continuousOn hL.le prof p.2) (hposF p.2 (hS hp).2.2) (hMassS p hp)
    exact ⟨⟨y, hy⟩, by rwa [profFun_of_mem hL.le prof p.2 hy] at hle⟩
  · intro u hu hA hpos
    obtain ⟨du, ddu, h1, h2, h3, h4, h5, h6⟩ := hReg0 u hu hA
    have heq := logistic_zero_sensitivity_eq a b alpha L _ du ddu ha hb halpha hL
      (profFun_continuousOn hL.le prof u) (hposF u hpos) h1 h2 h3 h4 h5 h6
    exact hInj u fun x => by rw [← profFun_of_mem hL.le prof u x.2]; exact heq x x.2

end Closure

/-! ## Plugging into `GlobalBranch` -/

section Global

variable {E : Type*} [TopologicalSpace E] {L : ℝ}

/-- **Theorem 1.3(2) with Lemma 4.3 discharged** (TeX lines 925–933,
3163–3198): `GlobalBranch.part2_sSup_eq_top` for `V = admissibleSet prof Aff`,
with its hypothesis `closure S ⊆ V` replaced by the analytic inputs of
`closure_subset_admissible`. -/
theorem part2_sSup_eq_top_of_ambient
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {C S Sol : Set (ℝ × E)}
    {uStar : E} {cStar : ℝ}
    (hRelClosed : IsClosed (((↑) : admissibleSet prof Aff → ℝ × E) ⁻¹' C))
    (hCV : C ⊆ admissibleSet prof Aff) (hCS : C ⊆ closure S)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (hNC : ¬ IsCompact C)
    (hProf : Continuous prof) (hAff : IsClosed Aff) (hc : 0 < cStar)
    (hS : S ⊆ admissibleSet prof Aff) (hSne : ∀ p ∈ S, p.2 ≠ uStar)
    (hMax : ∀ p ∈ S, ∃ x, cStar ≤ prof p.2 x)
    (hSSol : S ⊆ Sol) (hLimit : closure S ⊆ Sol)
    (hSMP : ∀ p ∈ Sol, 0 ≤ p.1 → p.2 ∈ Aff → (∀ x, 0 ≤ prof p.2 x) →
      (∃ x, 0 < prof p.2 x) → ∀ x, 0 < prof p.2 x)
    (hZero : ∀ u, ((0 : ℝ), u) ∈ Sol → u ∈ Aff → (∀ x, 0 < prof u x) → u = uStar)
    (hIFT : ∀ᶠ p in 𝓝 ((0 : ℝ), uStar), p ∈ Sol → p.2 = uStar) :
    (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ :=
  GlobalBranch.part2_sSup_eq_top hRelClosed hCV hCS
    (closure_subset_admissible hProf hAff hc hS hSne hMax hSSol hLimit hSMP hZero hIFT)
    hPrecompact hNC

variable [AddCommGroup E]

/-- **Theorem 1.3(3) with Lemma 4.3 discharged** (TeX lines 934–938,
3205–3319): `GlobalBranch.part3_global` for `V = admissibleSet prof Aff`, with
`closure S ⊆ V` replaced by the inputs of `closure_subset_admissible`. -/
theorem part3_global_of_ambient
    {prof' : E →+ (ℝ → ℝ)} {c chiStar : ℝ} {uStar : E} {W : Set E}
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {C S Sol : Set (ℝ × E)} {cStar : ℝ}
    (hL : 0 < L)
    (hAlt : GlobalBranch.GlobalAlternatives C chiStar uStar W)
    (hConst : prof' uStar = fun _ => c)
    (hCont : ∀ e : E, ContinuousOn (prof' e) (Icc 0 L))
    (hW : ∀ w ∈ W, ∫ x in (0 : ℝ)..L, prof' w x * Eigenmodes.mode L 1 x = 0)
    (hMono : ∀ p ∈ C, p ≠ (chiStar, uStar) →
      StrictAntiOn (prof' p.2) (Icc 0 L) ∨ StrictMonoOn (prof' p.2) (Icc 0 L))
    (hRelClosed : IsClosed (((↑) : admissibleSet prof Aff → ℝ × E) ⁻¹' C))
    (hCV : C ⊆ admissibleSet prof Aff) (hCS : C ⊆ closure S)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (hProf : Continuous prof) (hAff : IsClosed Aff) (hc : 0 < cStar)
    (hS : S ⊆ admissibleSet prof Aff) (hSne : ∀ p ∈ S, p.2 ≠ uStar)
    (hMax : ∀ p ∈ S, ∃ x, cStar ≤ prof p.2 x)
    (hSSol : S ⊆ Sol) (hLimit : closure S ⊆ Sol)
    (hSMP : ∀ p ∈ Sol, 0 ≤ p.1 → p.2 ∈ Aff → (∀ x, 0 ≤ prof p.2 x) →
      (∃ x, 0 < prof p.2 x) → ∀ x, 0 < prof p.2 x)
    (hZero : ∀ u, ((0 : ℝ), u) ∈ Sol → u ∈ Aff → (∀ x, 0 < prof u x) → u = uStar)
    (hIFT : ∀ᶠ p in 𝓝 ((0 : ℝ), uStar), p ∈ Sol → p.2 = uStar) :
    ¬ GlobalBranch.AltOtherTrivial C chiStar uStar ∧ ¬ GlobalBranch.AltComplement C uStar W ∧
      ¬ IsCompact C ∧ (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ :=
  GlobalBranch.part3_global hL hAlt hConst hCont hW hMono hRelClosed hCV hCS
    (closure_subset_admissible hProf hAff hc hS hSne hMax hSSol hLimit hSMP hZero hIFT)
    hPrecompact

end Global

end ChemotaxisBifurcation.AmbientClosure
