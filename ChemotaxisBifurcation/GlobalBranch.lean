module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
public import ChemotaxisBifurcation.Eigenmodes
public import ChemotaxisBifurcation.RelativeComponentClosure

@[expose] public section

/-!
# Theorem 1.3: the global-branch logic as a conditional consumer

TeX label `T:global-extension` (statement, lines 906–952; proofs of parts
(1)–(3), lines 3033–3392 of the October manuscript).

This module formalizes the *logical* deductions of Theorem 1.3 on an abstract
unilateral component `C ⊆ ℝ × E`, where `E` is the ambient state space
(`H²(0,L)` in the manuscript) and the first coordinate is the sensitivity `χ₀`.
The analytic inputs stay explicit hypotheses:

* the unilateral global bifurcation theorem of Shi–Wang (Theorem 4.4), which
  yields `GlobalAlternatives` (part (1), line 3097);
* relative closedness of the component in the admissible set `V`
  (part (1), lines 3099–3106; formalized in `RelativeComponentClosure`);
* ambient admissibility of finite limits, Lemma `L:ambient-closure`
  (lines 3114–3159), as `closure S ⊆ V`;
* the a priori bounds of Lemma `L:spiky-solu-lm1`(2) (part (2)) and
  Lemma `L:minimal-spike-bounds`(5) (part (3)), in the form the proofs use:
  nonconstant solutions with bounded sensitivity are relatively compact;
* the persistence of strict monotonicity along `C₁^±` (lines 3240–3297), as
  relative clopenness of the monotone set in the component.

What is proved here: elimination of alternatives, closedness and compactness of
bounded-sensitivity slices, `sup χ₀ = +∞` (in `EReal`), the connectedness
propagation of monotonicity, the exclusion of alternatives (ii) and (iii) for
strictly monotone branches, and the finite trigonometric facts that the first
cosine mode is strictly decreasing on `[0,L]` while the higher modes, even
after a small perturbation, are not monotone.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.GlobalBranch

open Set Filter Topology MeasureTheory intervalIntegral
open ChemotaxisBifurcation.Eigenmodes

section Alternatives

variable {E : Type*}

/-- Alternative (i) of Theorem 1.3(1) (TeX lines 916–917): the component is not
compact. -/
def AltNoncompact [TopologicalSpace E] (C : Set (ℝ × E)) : Prop :=
  ¬ IsCompact C

/-- Alternative (ii) of Theorem 1.3(1) (TeX lines 918–920): the component meets
the trivial branch `{(χ₀, u*)}` at another sensitivity `χ̂₀ ≠ χ*`. -/
def AltOtherTrivial (C : Set (ℝ × E)) (chiStar : ℝ) (uStar : E) : Prop :=
  ∃ chi : ℝ, chi ≠ chiStar ∧ (chi, uStar) ∈ C

/-- Alternative (iii) of Theorem 1.3(1) (TeX lines 921–923): the component
contains a point `(χ̂₀, u* + w)` with `w ∈ W \ {0}`. -/
def AltComplement [Add E] [Zero E] (C : Set (ℝ × E)) (uStar : E) (W : Set E) :
    Prop :=
  ∃ chi : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (chi, uStar + w) ∈ C

/-- The disjunction delivered by the unilateral global bifurcation theorem
(Shi–Wang, Theorem 4.4) for each of `C^±` (TeX lines 913–924, 3097). -/
def GlobalAlternatives [TopologicalSpace E] [Add E] [Zero E] (C : Set (ℝ × E))
    (chiStar : ℝ) (uStar : E) (W : Set E) : Prop :=
  AltNoncompact C ∨ AltOtherTrivial C chiStar uStar ∨ AltComplement C uStar W

/-- **Alternative elimination** (the "and hence" of Theorem 1.3(3), TeX lines
935–938 and 3306): if alternatives (ii) and (iii) fail, the component is not
compact. -/
theorem not_isCompact_of_alternatives [TopologicalSpace E] [Add E] [Zero E]
    {C : Set (ℝ × E)} {chiStar : ℝ} {uStar : E} {W : Set E}
    (hAlt : GlobalAlternatives C chiStar uStar W)
    (hNotII : ¬ AltOtherTrivial C chiStar uStar)
    (hNotIII : ¬ AltComplement C uStar W) :
    ¬ IsCompact C := by
  rcases hAlt with h | h | h
  · exact h
  · exact absurd h hNotII
  · exact absurd h hNotIII

end Alternatives

section Compactness

variable {E : Type*} [TopologicalSpace E]

/-- A set relatively closed in `V` is closed in the ambient space once its
ambient closure stays inside `V`.  This is how Lemma `L:ambient-closure`
(TeX lines 3114–3159) is combined with relative closedness (Theorem 1.3(1))
in the proofs of parts (2) and (3), TeX lines 3166–3168, 3194–3195 and 3313–3314. -/
theorem isClosed_of_relClosed {C V : Set (ℝ × E)}
    (hRelClosed : IsClosed (((↑) : V → ℝ × E) ⁻¹' C)) (hCV : C ⊆ V)
    (hClosureV : closure C ⊆ V) :
    IsClosed C := by
  obtain ⟨t, ht, hEq⟩ := isClosed_induced_iff.mp hRelClosed
  have hCt : C ⊆ t := by
    intro p hp
    have : (⟨p, hCV hp⟩ : V) ∈ ((↑) : V → ℝ × E) ⁻¹' t := by
      rw [hEq]; exact hp
    exact this
  refine closure_subset_iff_isClosed.mp ?_
  intro p hp
  have hpt : p ∈ t := closure_minimal hCt ht hp
  have : (⟨p, hClosureV hp⟩ : V) ∈ ((↑) : V → ℝ × E) ⁻¹' C := by
    rw [← hEq]; exact hpt
  exact this

/-- **Bounded-sensitivity slices are compact** (TeX lines 3164–3197 for part
(2), and the explicit statement at lines 3316–3318 for part (3)).

Inputs: the component is closed, it lies in the ambient closure of the
nonconstant solution set `S`, and (the a priori bounds of Lemma
`L:spiky-solu-lm1`(2) or `L:minimal-spike-bounds`(5) plus the compact embedding
`C^{2+θ} ↪ H²`) each bounded-sensitivity piece of `S` is relatively compact. -/
theorem isCompact_slice {C S : Set (ℝ × E)} (hClosed : IsClosed C)
    (hCS : C ⊆ closure S)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (Xbar : ℝ) :
    IsCompact (C ∩ {p | p.1 ≤ Xbar}) := by
  have hSliceClosed : IsClosed (C ∩ {p : ℝ × E | p.1 ≤ Xbar}) :=
    hClosed.inter (isClosed_le continuous_fst continuous_const)
  refine (hPrecompact (Xbar + 1)).of_isClosed_subset hSliceClosed ?_
  have hOpen : IsOpen {p : ℝ × E | p.1 < Xbar + 1} :=
    isOpen_lt continuous_fst continuous_const
  intro p ⟨hpC, hpX⟩
  have hp : p ∈ {p : ℝ × E | p.1 < Xbar + 1} ∩ closure S :=
    ⟨show p.1 < Xbar + 1 by have : p.1 ≤ Xbar := hpX; linarith, hCS hpC⟩
  have := hOpen.inter_closure hp
  refine closure_mono ?_ this
  rintro q ⟨hq1, hq2⟩
  exact ⟨hq2, show q.1 ≤ Xbar + 1 from le_of_lt hq1⟩

/-- **Unbounded sensitivity from non-compactness** (Theorem 1.3(2),
TeX lines 925–933 and 3163–3198): if every bounded-sensitivity slice is
compact, a non-compact component has unbounded sensitivity. -/
theorem unbounded_of_not_isCompact {C : Set (ℝ × E)}
    (hSlice : ∀ Xbar : ℝ, IsCompact (C ∩ {p | p.1 ≤ Xbar}))
    (hNC : ¬ IsCompact C) :
    ∀ M : ℝ, ∃ p ∈ C, M < p.1 := by
  intro M
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  apply hNC
  have hEq : C ∩ {p | p.1 ≤ M} = C := by
    ext p
    exact ⟨fun h => h.1, fun h => ⟨h, hcon p h⟩⟩
  simpa [hEq] using hSlice M

omit [TopologicalSpace E] in
/-- Unbounded sensitivity, written as the manuscript's display
`sup {χ₀ : (χ₀,u) ∈ C} = +∞` (TeX lines 929–932, `E:bifurcation-branches`), with the
supremum taken in the extended reals. -/
theorem sSup_eq_top_of_unbounded {C : Set (ℝ × E)}
    (hUnb : ∀ M : ℝ, ∃ p ∈ C, M < p.1) :
    sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ := by
  rw [sSup_eq_top]
  intro b hb
  induction b using EReal.rec with
  | bot =>
    obtain ⟨p, hp, -⟩ := hUnb 0
    exact ⟨(p.1 : EReal), ⟨p, hp, rfl⟩, EReal.bot_lt_coe _⟩
  | coe x =>
    obtain ⟨p, hp, hlt⟩ := hUnb x
    exact ⟨(p.1 : EReal), ⟨p, hp, rfl⟩, EReal.coe_lt_coe_iff.mpr hlt⟩
  | top => exact absurd hb (lt_irrefl _)

/-- **Theorem 1.3(2), conditional form** (TeX lines 925–933; proof lines
3163–3198).  Hypotheses:
* `hRelClosed`, `hCV`: the component is relatively closed in `V`
  (Theorem 1.3(1));
* `hCS`: the component lies in the closure of the nonconstant solution set;
* `hAdmissible`: Lemma `L:ambient-closure` (`m ≥ 1`): `closure S ⊆ V`;
* `hPrecompact`: the a priori bound of Lemma `L:spiky-solu-lm1`(2) (under
  `a,b>0`, `0<γ≤1+α`, `1≤m<(α+2)/2`) with Arzelà–Ascoli: bounded-sensitivity
  nonconstant solutions are relatively compact in `ℝ × H²`.
Conclusion: a non-compact component has `sup χ₀ = +∞`. -/
theorem part2_sSup_eq_top {C S V : Set (ℝ × E)}
    (hRelClosed : IsClosed (((↑) : V → ℝ × E) ⁻¹' C)) (hCV : C ⊆ V)
    (hCS : C ⊆ closure S) (hAdmissible : closure S ⊆ V)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (hNC : ¬ IsCompact C) :
    (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ := by
  have hClosed : IsClosed C :=
    isClosed_of_relClosed hRelClosed hCV
      ((closure_mono hCS).trans (closure_closure (s := S)).le |>.trans hAdmissible)
  have hUnb := unbounded_of_not_isCompact (isCompact_slice hClosed hCS hPrecompact) hNC
  exact ⟨hUnb, sSup_eq_top_of_unbounded hUnb⟩

/-- The manuscript's unilateral component `C_{n₀}^±` as a subset of `ℝ × E`:
the selected component of `RelativeComponentClosure`, built in the admissible
subtype `V` from the relative closure of the nonconstant solutions `S`, and
included into `ℝ × E` (TeX lines 880–902). -/
def selectedImage (S V : Set (ℝ × E)) (removedArc : Set V) (base selector : V) :
    Set (ℝ × E) :=
  ((↑) : V → ℝ × E) ''
    selectedComponent (closure (((↑) : V → ℝ × E) ⁻¹' S)) removedArc base selector

/-- Bridge to `RelativeComponentClosure`: the selected unilateral component,
built inside the admissible subtype `V` from the relative closure of the
nonconstant solutions, is (after inclusion into `ℝ × E`) relatively closed in
`V`, contained in `V`, contained in the ambient closure of `S`, and
preconnected (Theorem 1.3(1), TeX lines 911–912, 3103–3106). -/
theorem selectedImage_properties {S V : Set (ℝ × E)}
    {removedArc : Set V} {base selector : V}
    (hBase : base ∈ closure (((↑) : V → ℝ × E) ⁻¹' S))
    (hRemovedRelOpen :
      IsOpen (((↑) : parentComponent (closure (((↑) : V → ℝ × E) ⁻¹' S)) base → V) ⁻¹'
        removedArc))
    (hSelectorInRemainder :
      selector ∈ unilateralRemainder (closure (((↑) : V → ℝ × E) ⁻¹' S)) removedArc base) :
    IsClosed (((↑) : V → ℝ × E) ⁻¹' selectedImage S V removedArc base selector) ∧
      selectedImage S V removedArc base selector ⊆ V ∧
      selectedImage S V removedArc base selector ⊆ closure S ∧
      IsPreconnected (selectedImage S V removedArc base selector) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [selectedImage, Subtype.val_injective.preimage_image]
    exact selectedComponent_isClosed isClosed_closure hBase hRemovedRelOpen
      hSelectorInRemainder
  · rintro _ ⟨q, -, rfl⟩
    exact q.property
  · rintro _ ⟨q, hq, rfl⟩
    have hq' := selectedComponent_subset_solutionClosure hq
    have := image_closure_subset_closure_image continuous_subtype_val ⟨q, hq', rfl⟩
    exact closure_mono (image_preimage_subset _ _) this
  · exact (isPreconnected_connectedComponentIn).image _ continuous_subtype_val.continuousOn

end Compactness

section Modes

/-- The first Neumann cosine mode, written out. -/
theorem mode_one_eq (L x : ℝ) : mode L 1 x = Real.cos (Real.pi / L * x) := by
  simp [mode, waveNumber]

/-- **`cos(πx/L)` is strictly decreasing on `[0,L]`** (the `k = 1` case of the
fact used at TeX lines 3275–3277). -/
theorem mode_one_strictAntiOn {L : ℝ} (hL : 0 < L) :
    StrictAntiOn (mode L 1) (Icc 0 L) := by
  intro x hx y hy hxy
  rw [mode_one_eq, mode_one_eq]
  have hk : 0 < Real.pi / L := div_pos Real.pi_pos hL
  have mem : ∀ z ∈ Icc (0 : ℝ) L, Real.pi / L * z ∈ Icc 0 Real.pi := by
    intro z hz
    refine ⟨mul_nonneg hk.le hz.1, ?_⟩
    calc Real.pi / L * z ≤ Real.pi / L * L := mul_le_mul_of_nonneg_left hz.2 hk.le
      _ = Real.pi := by field_simp
  exact Real.strictAntiOn_cos (mem x hx) (mem y hy) (mul_lt_mul_of_pos_left hxy hk)

/-- **Higher modes are not monotone, stably** (TeX lines 3270–3277).  If
`u_j = c + s_j φ_n + r_j` with `s_j ≠ 0`, `sup_{[0,L]} |r_j| ≤ ε_j |s_j|`,
`ε_j → 0` and `n ≥ 2`, then the `u_j` cannot all be monotone (in either
direction) on `[0,L]`.  The manuscript states this via the derivative of
`φ_n` taking both signs and `H² ↪ C¹`; only `C⁰` smallness of the remainder is
needed here. -/
theorem not_monotone_of_higher_mode {L c : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
    (u r : ℕ → ℝ → ℝ) (s ε : ℕ → ℝ)
    (hu : ∀ j x, u j x = c + s j * mode L n x + r j x)
    (hs : ∀ j, s j ≠ 0)
    (hr : ∀ j, ∀ x ∈ Icc 0 L, |r j x| ≤ ε j * |s j|)
    (hε : Tendsto ε atTop (𝓝 0))
    (hmono : ∀ j, MonotoneOn (u j) (Icc 0 L) ∨ AntitoneOn (u j) (Icc 0 L)) :
    False := by
  obtain ⟨j, hj⟩ := (hε.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set a : ℝ := L / n with ha
  have ha0 : 0 < a := div_pos hL hnpos
  have h2a : 2 * a ≤ L := by
    rw [ha, ← mul_div_assoc, div_le_iff₀ hnpos]; nlinarith
  have m0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have m1 : a ∈ Icc 0 L := ⟨ha0.le, by linarith⟩
  have m2 : 2 * a ∈ Icc 0 L := ⟨by linarith, h2a⟩
  have hw : waveNumber L n * a = Real.pi := by
    simp only [waveNumber, ha]; field_simp
  have v0 : mode L n 0 = 1 := by simp [mode]
  have v1 : mode L n a = -1 := by simp [mode, hw]
  have v2 : mode L n (2 * a) = 1 := by
    simp only [mode]
    rw [show waveNumber L n * (2 * a) = 2 * Real.pi by rw [← hw]; ring]
    simp
  have r0 := abs_le.mp (hr j 0 m0)
  have r1 := abs_le.mp (hr j a m1)
  have r2 := abs_le.mp (hr j (2 * a) m2)
  have u0 := hu j 0
  have u1 := hu j a
  have u2 := hu j (2 * a)
  rw [v0] at u0; rw [v1] at u1; rw [v2] at u2
  have hsj := abs_pos.mpr (hs j)
  have hε' : ε j * |s j| < |s j| / 2 := by nlinarith
  rcases lt_or_gt_of_ne (hs j) with hneg | hpos
  · rw [abs_of_neg hneg] at r0 r1 r2 hε'
    rcases hmono j with hM | hA
    · have := hM m1 m2 (by linarith); linarith
    · have := hA m0 m1 ha0.le; linarith
  · rw [abs_of_pos hpos] at r0 r1 r2 hε'
    rcases hmono j with hM | hA
    · have := hM m0 m1 ha0.le; linarith
    · have := hA m1 m2 (by linarith); linarith

/-- **`cos(nπx/L)` is not monotone on `[0,L]` for `n ≥ 2`** (TeX line 3275),
neither nondecreasing nor nonincreasing. -/
theorem mode_not_monotoneOn {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n) :
    ¬ MonotoneOn (mode L n) (Icc 0 L) ∧ ¬ AntitoneOn (mode L n) (Icc 0 L) := by
  have key : ¬ (MonotoneOn (mode L n) (Icc 0 L) ∨ AntitoneOn (mode L n) (Icc 0 L)) := by
    intro h
    exact not_monotone_of_higher_mode (c := 0) hL hn (fun _ => mode L n) (fun _ _ => 0)
      (fun _ => 1) (fun _ => 0) (fun _ x => by simp) (fun _ => one_ne_zero)
      (fun _ _ _ => by simp) tendsto_const_nhds (fun _ => h)
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

/-- **Constant limits of monotone solutions occur only at the first mode**
(TeX lines 3265–3279).  If a sequence of monotone solutions approaches the
trivial branch at the bifurcation point of mode `n ≥ 1` along the local
representation `u_j = u* + s_j φ_n + r_j` of the local simple-eigenvalue
bifurcation theorem, kept as an explicit hypothesis, then `n = 1`. -/
theorem mode_eq_one_of_monotone_limit {L c : ℝ} (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n)
    (u r : ℕ → ℝ → ℝ) (s ε : ℕ → ℝ)
    (hu : ∀ j x, u j x = c + s j * mode L n x + r j x)
    (hs : ∀ j, s j ≠ 0)
    (hr : ∀ j, ∀ x ∈ Icc 0 L, |r j x| ≤ ε j * |s j|)
    (hε : Tendsto ε atTop (𝓝 0))
    (hmono : ∀ j, MonotoneOn (u j) (Icc 0 L) ∨ AntitoneOn (u j) (Icc 0 L)) :
    n = 1 := by
  by_contra hne
  exact not_monotone_of_higher_mode hL (by omega) u r s ε hu hs hr hε hmono

/-- **The first Fourier coefficient of a strictly decreasing profile is
positive**: for `g` continuous and strictly decreasing on `[0,L]`,
`∫_0^L g(x) cos(πx/L) dx > 0`.  This is the exclusion of alternative (iii) at
TeX lines 3299–3305, proved by pairing `x` with `L - x` (no derivative of `g`
is needed). -/
theorem integral_mul_mode_one_pos {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 L)) (hanti : StrictAntiOn g (Icc 0 L)) :
    0 < ∫ x in (0 : ℝ)..L, g x * mode L 1 x := by
  set f : ℝ → ℝ := fun x => g x * mode L 1 x with hf
  have hk : Continuous fun x : ℝ => mode L 1 x := by
    simp only [mode_one_eq]; fun_prop
  have hfc : ContinuousOn f (Icc 0 L) := hg.mul hk.continuousOn
  have hL2 : 0 ≤ L / 2 := by linarith
  have hI1 : IntervalIntegrable f volume 0 (L / 2) := by
    refine (hfc.mono ?_).intervalIntegrable
    rw [uIcc_of_le hL2]; exact Icc_subset_Icc le_rfl (by linarith)
  have hI2 : IntervalIntegrable f volume (L / 2) L := by
    refine (hfc.mono ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc hL2 le_rfl
  have hrefl : ContinuousOn (fun x => f (L - x)) (Icc 0 (L / 2)) := by
    refine hfc.comp (by fun_prop) ?_
    intro x hx; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hI3 : IntervalIntegrable (fun x => f (L - x)) volume 0 (L / 2) := by
    refine hrefl.intervalIntegrable_of_Icc hL2
  have hsub : ∫ x in (L / 2)..L, f x = ∫ x in (0 : ℝ)..(L / 2), f (L - x) := by
    rw [intervalIntegral.integral_comp_sub_left]
    congr 1 <;> ring
  have hsym : ∀ x, f x + f (L - x) =
      (g x - g (L - x)) * Real.cos (Real.pi / L * x) := by
    intro x
    simp only [hf, mode_one_eq]
    have : Real.pi / L * (L - x) = Real.pi - Real.pi / L * x := by
      field_simp
    rw [this, Real.cos_pi_sub]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, hsub,
    ← intervalIntegral.integral_add hI1 hI3]
  simp_rw [hsym]
  have hkpos : 0 < Real.pi / L := div_pos Real.pi_pos hL
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ (by linarith)
  · refine ContinuousOn.intervalIntegrable_of_Icc hL2 ?_
    refine ContinuousOn.mul ?_ (by fun_prop)
    refine (hg.mono ?_).sub (hg.comp (by fun_prop) ?_)
    · exact Icc_subset_Icc le_rfl (by linarith)
    · intro x hx; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · intro x hx
    have hx0 := hx.1
    have hx1 := hx.2
    refine mul_pos ?_ (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · have := hanti ⟨hx0.le, by linarith⟩ ⟨by linarith, by linarith⟩
        (show x < L - x by linarith)
      linarith
    · have := mul_pos hkpos hx0; linarith [Real.pi_pos]
    · calc Real.pi / L * x < Real.pi / L * (L / 2) := mul_lt_mul_of_pos_left hx1 hkpos
        _ = Real.pi / 2 := by field_simp

/-- Mirror of `integral_mul_mode_one_pos` for strictly increasing profiles. -/
theorem integral_mul_mode_one_neg {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 L)) (hmono : StrictMonoOn g (Icc 0 L)) :
    ∫ x in (0 : ℝ)..L, g x * mode L 1 x < 0 := by
  have h := integral_mul_mode_one_pos hL hg.neg (fun x hx y hy hxy => neg_lt_neg (hmono hx hy hxy))
  simp only [Pi.neg_apply, neg_mul, intervalIntegral.integral_neg] at h
  linarith

end Modes

section Part3

variable {E : Type*} [TopologicalSpace E]

/-- **Connectedness propagation** (TeX lines 3281–3297): a property holding at
the bifurcation point whose locus is relatively open and closed in a
preconnected component holds on the whole component. -/
theorem subset_of_relClopen {C M : Set (ℝ × E)} {pStar : ℝ × E}
    (hConn : IsPreconnected C) (hStar : pStar ∈ C) (hStarM : pStar ∈ M)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹' M)) :
    C ⊆ M := by
  have := isPreconnected_iff_preconnectedSpace.mp hConn
  have hUniv := hClopen.eq_univ ⟨⟨pStar, hStar⟩, hStarM⟩
  intro p hp
  have : (⟨p, hp⟩ : C) ∈ ((↑) : C → ℝ × E) ⁻¹' M := by rw [hUniv]; trivial
  exact this

variable [AddCommGroup E]

/-- The set of points of `C₁^+` that are either the bifurcation point or
strictly decreasing profiles (TeX lines 3281–3289). -/
def DecreasingLocus (prof : E →+ (ℝ → ℝ)) (L : ℝ) (pStar : ℝ × E) : Set (ℝ × E) :=
  {p | p = pStar ∨ StrictAntiOn (prof p.2) (Icc 0 L)}

/-- The set of points of `C₁^-` that are either the bifurcation point or
strictly increasing profiles. -/
def IncreasingLocus (prof : E →+ (ℝ → ℝ)) (L : ℝ) (pStar : ℝ × E) : Set (ℝ × E) :=
  {p | p = pStar ∨ StrictMonoOn (prof p.2) (Icc 0 L)}

/-- **Theorem 1.3(3), monotonicity on `C₁^+`** (TeX lines 939–942,
3281–3297): every point of `C₁^+` other than `(χ*, u*)` is strictly decreasing.
Input: the decreasing locus is relatively clopen in the component (the
persistence argument and the local bifurcation analysis at constant limits,
which uses `mode_eq_one_of_monotone_limit`). -/
theorem part3_strictAnti (prof : E →+ (ℝ → ℝ)) (L : ℝ) {C : Set (ℝ × E)}
    {pStar : ℝ × E} (hConn : IsPreconnected C) (hStar : pStar ∈ C)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹' DecreasingLocus prof L pStar)) :
    ∀ p ∈ C, p ≠ pStar → StrictAntiOn (prof p.2) (Icc 0 L) := by
  intro p hp hne
  rcases subset_of_relClopen hConn hStar (Or.inl rfl) hClopen hp with h | h
  · exact absurd h hne
  · exact h

/-- **Theorem 1.3(3), monotonicity on `C₁^-`**: every point other than
`(χ*, u*)` is strictly increasing. -/
theorem part3_strictMono (prof : E →+ (ℝ → ℝ)) (L : ℝ) {C : Set (ℝ × E)}
    {pStar : ℝ × E} (hConn : IsPreconnected C) (hStar : pStar ∈ C)
    (hClopen : IsClopen (((↑) : C → ℝ × E) ⁻¹' IncreasingLocus prof L pStar)) :
    ∀ p ∈ C, p ≠ pStar → StrictMonoOn (prof p.2) (Icc 0 L) := by
  intro p hp hne
  rcases subset_of_relClopen hConn hStar (Or.inl rfl) hClopen hp with h | h
  · exact absurd h hne
  · exact h

omit [TopologicalSpace E] in
/-- **Alternative (ii) fails for a strictly monotone branch** (TeX line 3298):
the constant `u*` is not strictly monotone. -/
theorem not_altOtherTrivial {prof : E →+ (ℝ → ℝ)} {L c chiStar : ℝ} {uStar : E}
    {C : Set (ℝ × E)} (hL : 0 < L) (hConst : prof uStar = fun _ => c)
    (hMono : ∀ p ∈ C, p ≠ (chiStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L)) :
    ¬ AltOtherTrivial C chiStar uStar := by
  rintro ⟨chi, hne, hmem⟩
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have h1 : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
  rcases hMono _ hmem (fun h => hne (Prod.ext_iff.mp h).1) with h | h
  · have := h h0 h1 hL; simp [hConst] at this
  · have := h h0 h1 hL; simp [hConst] at this

omit [TopologicalSpace E] in
/-- **Alternative (iii) fails for a strictly monotone branch** (TeX lines
3299–3305): for `w ∈ W`, i.e. `∫_0^L w φ₁ = 0`, the profile `u* + w` cannot be
strictly monotone, because its first cosine coefficient is nonzero. -/
theorem not_altComplement {prof : E →+ (ℝ → ℝ)} {L c chiStar : ℝ} {uStar : E}
    {C : Set (ℝ × E)} {W : Set E} (hL : 0 < L) (hConst : prof uStar = fun _ => c)
    (hCont : ∀ e : E, ContinuousOn (prof e) (Icc 0 L))
    (hW : ∀ w ∈ W, ∫ x in (0 : ℝ)..L, prof w x * mode L 1 x = 0)
    (hMono : ∀ p ∈ C, p ≠ (chiStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L)) :
    ¬ AltComplement C uStar W := by
  rintro ⟨chi, w, hwW, hw0, hmem⟩
  have hne : (chi, uStar + w) ≠ (chiStar, uStar) := by
    intro h
    exact hw0 (by simpa using (Prod.ext_iff.mp h).2)
  have hprof : prof (uStar + w) = fun x => c + prof w x := by
    rw [map_add, hConst]; rfl
  have hzero := hW w hwW
  rcases hMono _ hmem hne with h | h
  · have hw : StrictAntiOn (prof w) (Icc 0 L) := by
      intro x hx y hy hxy
      have := h hx hy hxy
      simp only [hprof] at this
      linarith
    have := integral_mul_mode_one_pos hL (hCont w) hw
    linarith
  · have hw : StrictMonoOn (prof w) (Icc 0 L) := by
      intro x hx y hy hxy
      have := h hx hy hxy
      simp only [hprof] at this
      linarith
    have := integral_mul_mode_one_neg hL (hCont w) hw
    linarith

/-- **Theorem 1.3(3), conditional form** (TeX lines 934–938; proof lines
3205–3319), for either unilateral component `C = C₁^±` with a fixed
orientation of monotonicity encoded by `hMono`.

Hypotheses kept explicit:
* `hAlt`: Shi–Wang's alternatives for `C` (Theorem 1.3(1));
* `hMono`: strict monotonicity away from `(χ*, u*)` (from `part3_strictAnti`
  or `part3_strictMono`);
* `hW`: `W` is the `L²`-orthogonal complement of `φ₁` (definition, TeX lines
  874–876);
* `hRelClosed`, `hCV`, `hCS`, `hAdmissible`: relative closedness and Lemma
  `L:ambient-closure` (`m = 1`);
* `hPrecompact`: Lemma `L:minimal-spike-bounds`(5) with fixed mass.
Conclusions: alternatives (ii) and (iii) fail, `C` is not compact, and
`sup χ₀ = +∞`. -/
theorem part3_global {prof : E →+ (ℝ → ℝ)} {L c chiStar : ℝ} {uStar : E}
    {C S V : Set (ℝ × E)} {W : Set E} (hL : 0 < L)
    (hAlt : GlobalAlternatives C chiStar uStar W)
    (hConst : prof uStar = fun _ => c)
    (hCont : ∀ e : E, ContinuousOn (prof e) (Icc 0 L))
    (hW : ∀ w ∈ W, ∫ x in (0 : ℝ)..L, prof w x * mode L 1 x = 0)
    (hMono : ∀ p ∈ C, p ≠ (chiStar, uStar) →
      StrictAntiOn (prof p.2) (Icc 0 L) ∨ StrictMonoOn (prof p.2) (Icc 0 L))
    (hRelClosed : IsClosed (((↑) : V → ℝ × E) ⁻¹' C)) (hCV : C ⊆ V)
    (hCS : C ⊆ closure S) (hAdmissible : closure S ⊆ V)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar}))) :
    ¬ AltOtherTrivial C chiStar uStar ∧ ¬ AltComplement C uStar W ∧
      ¬ IsCompact C ∧ (∀ M : ℝ, ∃ p ∈ C, M < p.1) ∧
      sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ := by
  have hII := not_altOtherTrivial (c := c) hL hConst hMono
  have hIII := not_altComplement (chiStar := chiStar) hL hConst hCont hW hMono
  have hNC := not_isCompact_of_alternatives hAlt hII hIII
  exact ⟨hII, hIII, hNC, part2_sSup_eq_top hRelClosed hCV hCS hAdmissible hPrecompact hNC⟩

end Part3

end ChemotaxisBifurcation.GlobalBranch
