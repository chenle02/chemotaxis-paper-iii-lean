module
public import ChemotaxisBifurcation.MixedRemainder

@[expose] public section

/-!
# Uniqueness and continuity of the scalar bifurcation branches (Theorem 1.1, Step 5)

Theorem 1.1 of the 44-page manuscript (`\label{T:local-bifurcation}`, TeX lines
592--640) asserts two *continuous curves* `Γ^±_{n₀}` of stationary solutions
through `(u*, v*)`. Step 5 of its proof (TeX lines 1975--1995,
`\label{E:two-branches}`) and the sentence "local uniqueness in the
construction of Theorem 1.1" (TeX line 884) give no argument for uniqueness
of the scalar roots `u_{n₀}^±(χ̃)` or for their continuity in `χ̃`.
`MixedRemainder.mixed_branch_eventually` proves existence, amplitude and
derivative sign only.

This module supplies the missing scalar argument, under the same remainder
interface as `MixedRemainder` (value bound, `HasDerivAt (R η) (Rs η s) s`,
derivative bound on the box `|η|, |s| ≤ r ≤ 1`):

* `root_localize`: in a fixed window `0 < |s| ≤ ρ`
  (`ρ = branchRadius`) every nontrivial root lies on the side `η β > 0` and
  satisfies `|s| ∈ [7/8 √(αη/β), 9/8 √(αη/β)]`;
* `scaled_field_strictAntiOn`: on the amplitude window
  `s² ∈ [αη/(2β), 2αη/β]` the field is strictly monotone (its derivative has
  the sign of `-β`, from the derivative bound);
* `branchRoot_existsUnique`: hence the positive and the negative nontrivial
  root in the window are unique (clause "two branches", TeX line 1981);
* `small_roots_classification`: these two roots are the only small nontrivial
  equilibria (clause 3 of the task);
* `branch_continuousOn`, `branch_tendsto_zero`: the branch functions
  `η ↦ s^±(η)` are continuous on a neighbourhood of `0`, vanish exactly off the
  side `η β > 0`, and tend to `0` as `η → 0`; with `s^±(0) = 0` they are the
  continuous curves `Γ^±` of Theorem 1.1 in the scalar coordinate.

Only continuity needs one extra hypothesis, `hRcont`: for each fixed small
`s`, the map `η ↦ R η s` is continuous. The value/derivative interface gives
no information about the dependence of `R` on `η` beyond size bounds, so
without it the roots could jump. It is implied by the joint continuity of the
center-manifold reduction in `(χ̃, u)`, which the manuscript uses implicitly.
No continuity of `Rs` is needed. No hypothesis on the roots themselves is
assumed.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.BranchCurves

open ChemotaxisBifurcation.NormalForm ChemotaxisBifurcation.MixedRemainder Filter Topology

/-- The `O(|η|)` amplitude constant of `mixed_equilibrium_core`. -/
noncomputable def ampErr (alpha beta C : ℝ) : ℝ :=
  2 * alpha * absorbedConst alpha beta C * (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2

/-- The fixed radius of the uniqueness window in `s`. -/
noncomputable def branchRadius (alpha beta C r : ℝ) : ℝ :=
  min r (|beta| / (4 * (absorbedConst alpha beta C + 1)))

/-- Strict smallness conditions on `η`; they define an open neighbourhood of `0`. -/
def CurveSmall (alpha beta C r eta : ℝ) : Prop :=
  |eta| < r ∧ 2 * C * |eta| < alpha ∧
    2 * (alpha * eta / beta) < branchRadius alpha beta C r ^ 2 ∧
    C * (|eta| + 2 * (alpha * eta / beta) +
      2 * alpha * Real.sqrt (2 * (alpha * eta / beta)) / |beta|) < alpha / 2 ∧
    absorbedConst alpha beta C * (|eta| + Real.sqrt (2 * (alpha * eta / beta))) < |beta| / 2 ∧
    absorbedConst alpha beta C * |eta| < |beta| / 4 ∧
    64 * ampErr alpha beta C ^ 2 * |eta| < alpha / |beta|

/-- `s` is a nontrivial root of sign `sgn` in the window `|s| ≤ ρ`. -/
def BranchRoot (alpha beta rho : ℝ) (R : ℝ → ℝ → ℝ) (sgn eta s : ℝ) : Prop :=
  0 < sgn * s ∧ |s| ≤ rho ∧ reducedField alpha beta R eta s = 0

/-- The branch function `η ↦ s^±(η)`: the root of sign `sgn` in the window if
there is one, and `0` otherwise. -/
noncomputable def branch (alpha beta rho : ℝ) (R : ℝ → ℝ → ℝ) (sgn eta : ℝ) : ℝ := by
  classical
  exact if h : ∃ s, BranchRoot alpha beta rho R sgn eta s then h.choose else 0

/-- The field in the coordinate `x = sgn · s`, multiplied by `sgn · β`; on the
amplitude window it is strictly decreasing in `x`. -/
def scaledField (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (sgn eta x : ℝ) : ℝ :=
  sgn * beta * reducedField alpha beta R eta (sgn * x)

/-! ## Elementary facts -/

theorem abs_eq_sgn_mul (sgn u : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) (h : 0 < sgn * u) :
    |u| = sgn * u := by
  rcases hsgn with rfl | rfl
  · rw [one_mul] at h ⊢; exact abs_of_pos h
  · have hu : u < 0 := by linarith
    rw [abs_of_neg hu]; ring

theorem ampErr_nonneg (alpha beta C : ℝ) (halpha : 0 < alpha) (hC : 0 ≤ C) :
    0 ≤ ampErr alpha beta C := by
  unfold ampErr
  have := absorbedConst_nonneg alpha beta C halpha hC
  positivity

theorem branchRadius_pos (alpha beta C r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hC : 0 ≤ C) (hr : 0 < r) : 0 < branchRadius alpha beta C r := by
  have := absorbedConst_nonneg alpha beta C halpha hC
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  exact lt_min hr (by positivity)

theorem branchRadius_le (alpha beta C r : ℝ) : branchRadius alpha beta C r ≤ r :=
  min_le_left _ _

theorem absorbed_mul_radius (alpha beta C r : ℝ) (halpha : 0 < alpha) (hC : 0 ≤ C) :
    absorbedConst alpha beta C * branchRadius alpha beta C r ≤ |beta| / 4 := by
  have hK := absorbedConst_nonneg alpha beta C halpha hC
  have hρ : branchRadius alpha beta C r ≤ |beta| / (4 * (absorbedConst alpha beta C + 1)) :=
    min_le_right _ _
  calc absorbedConst alpha beta C * branchRadius alpha beta C r
      ≤ absorbedConst alpha beta C * (|beta| / (4 * (absorbedConst alpha beta C + 1))) :=
        mul_le_mul_of_nonneg_left hρ hK
    _ ≤ |beta| / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg beta]

theorem curveSmall_branchSmall (alpha beta C r eta : ℝ) (halpha : 0 < alpha)
    (hbeta : beta ≠ 0) (hC : 0 ≤ C) (hr : 0 < r)
    (h : CurveSmall alpha beta C r eta) : BranchSmall alpha beta C r eta := by
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := h
  have hρ := branchRadius_pos alpha beta C r halpha hbeta hC hr
  have hρr : branchRadius alpha beta C r ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ hρ.le (branchRadius_le alpha beta C r) 2
  exact ⟨h1.le, h2.le, (h3.trans_le hρr).le, h4, h5.le⟩

/-- On the side `η β > 0`, smallness gives `8 · ampErr · |η| ≤ √(αη/β)`. -/
theorem amp_err_le_sqrt (alpha beta C r eta : ℝ) (halpha : 0 < alpha)
    (hC : 0 ≤ C) (hside : 0 < eta * beta) (h : CurveSmall alpha beta C r eta) :
    8 * ampErr alpha beta C * |eta| ≤ Real.sqrt (alpha * eta / beta) := by
  obtain ⟨-, -, -, -, -, -, h7⟩ := h
  have hb : 0 < |beta| := abs_pos.mpr (by rintro rfl; simp at hside)
  have hE := ampErr_nonneg alpha beta C halpha hC
  rw [Real.le_sqrt (by positivity) (amplitude_sq_pos alpha beta eta halpha hside).le,
    amp_sq_eq_abs alpha beta eta hside, le_div_iff₀ hb]
  rw [lt_div_iff₀ hb] at h7
  have he := abs_nonneg eta
  have : 64 * ampErr alpha beta C ^ 2 * |eta| * |beta| * |eta| ≤ alpha * |eta| :=
    mul_le_mul_of_nonneg_right h7.le he
  nlinarith

/-- Points with `x ∈ [13/16, 19/16] · √t` lie in the amplitude window. -/
theorem mem_window (t x : ℝ) (ht : 0 < t)
    (h1 : 13 / 16 * Real.sqrt t ≤ x) (h2 : x ≤ 19 / 16 * Real.sqrt t) :
    x ∈ Set.Icc (Real.sqrt (t / 2)) (Real.sqrt (2 * t)) := by
  have hs := Real.sq_sqrt ht.le
  have hs0 := Real.sqrt_nonneg t
  have hx : 0 ≤ x := le_trans (by positivity) h1
  constructor
  · rw [Real.sqrt_le_left hx]
    nlinarith
  · rw [Real.le_sqrt hx (by positivity)]
    nlinarith

/-! ## Localization of every small nontrivial root -/

/-- Every nontrivial root in the window `|s| ≤ ρ` lies on the side `η β > 0`
and has `|s| ∈ [7/8, 9/8] · √(αη/β)`. -/
theorem root_localize (alpha beta C r eta s : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : CurveSmall alpha beta C r eta) (hs : s ≠ 0)
    (hsρ : |s| ≤ branchRadius alpha beta C r)
    (hroot : reducedField alpha beta R eta s = 0) :
    0 < eta * beta ∧ 7 / 8 * Real.sqrt (alpha * eta / beta) ≤ |s| ∧
      |s| ≤ 9 / 8 * Real.sqrt (alpha * eta / beta) := by
  have hsmall' := hsmall
  obtain ⟨h1, h2, -, -, -, h6, -⟩ := hsmall
  have hsr : |s| ≤ r := hsρ.trans (branchRadius_le alpha beta C r)
  have hK := absorbedConst_nonneg alpha beta C halpha hC
  have hrect : absorbedConst alpha beta C * (|eta| + |s|) ≤ |beta| / 2 := by
    have h1' := absorbed_mul_radius alpha beta C r halpha hC
    have h2' : absorbedConst alpha beta C * |s| ≤
        absorbedConst alpha beta C * branchRadius alpha beta C r :=
      mul_le_mul_of_nonneg_left hsρ hK
    rw [mul_add]
    linarith
  obtain ⟨hside, -, hamp⟩ := mixed_equilibrium_core alpha beta eta s (R eta s) (Rs eta s)
    (alpha * eta - 3 * beta * s ^ 2 + Rs eta s) C halpha hbeta hs hC (hsr.trans hr1)
    (h1.le.trans hr1) h2.le (by simpa [reducedField] using hroot) rfl
    (hRval eta s h1.le hsr) (hRs eta s h1.le hsr) hrect
  have h8 := amp_err_le_sqrt alpha beta C r eta halpha hC hside hsmall'
  have hamp' : abs (|s| - Real.sqrt (alpha * eta / beta)) ≤ ampErr alpha beta C * |eta| :=
    hamp
  obtain ⟨ha, hb⟩ := abs_le.mp hamp'
  refine ⟨hside, ?_, ?_⟩ <;> nlinarith

/-! ## Strict monotonicity on the amplitude window -/

/-- On the amplitude window the derivative of the field has the sign of `-β`. -/
theorem field_deriv_neg_on_window (alpha beta C eta x Rs : ℝ)
    (hside : 0 < eta * beta) (hC : 0 ≤ C) (hx : 0 < x)
    (hx1 : alpha * eta / beta / 2 ≤ x ^ 2) (hx2 : x ^ 2 ≤ 2 * (alpha * eta / beta))
    (hRs : |Rs| ≤ C * (eta ^ 2 + x ^ 2 * |eta| + |x| ^ 3))
    (hwin : C * (|eta| + 2 * (alpha * eta / beta) +
        2 * alpha * Real.sqrt (2 * (alpha * eta / beta)) / |beta|) < alpha / 2) :
    beta * (alpha * eta - 3 * beta * x ^ 2 + Rs) < 0 := by
  have hbeta : beta ≠ 0 := by rintro rfl; simp at hside
  have hxR : |x * Rs| ≤ C * (|x| * eta ^ 2 + |x| ^ 3 * |eta| + x ^ 4) := by
    have hxa : |x| = x := abs_of_pos hx
    rw [hxa] at hRs
    rw [abs_mul, hxa]
    calc x * |Rs| ≤ x * (C * (eta ^ 2 + x ^ 2 * |eta| + x ^ 3)) :=
          mul_le_mul_of_nonneg_left hRs hx.le
      _ = C * (x * eta ^ 2 + x ^ 3 * |eta| + x ^ 4) := by ring
  have hlt := weak_value_lt_on_window alpha beta eta x (x * Rs) C hside hC hx hx2 hxR hwin
  rw [abs_mul, abs_of_pos hx] at hlt
  have hRs' : |Rs| < alpha / 2 * |eta| := lt_of_mul_lt_mul_left hlt hx.le
  have hbt : beta * (alpha * eta / beta) = alpha * eta := by field_simp
  have hb2 : beta ^ 2 * (alpha * eta / beta / 2) ≤ beta ^ 2 * x ^ 2 :=
    mul_le_mul_of_nonneg_left hx1 (sq_nonneg beta)
  have hb2' : beta ^ 2 * (alpha * eta / beta / 2) = alpha * (eta * beta) / 2 := by
    field_simp
  have habs : |beta| * |eta| = eta * beta := by
    rw [← abs_mul, mul_comm, abs_of_pos hside]
  have hbR : beta * Rs ≤ |beta| * |Rs| := by rw [← abs_mul]; exact le_abs_self _
  have hbR' : |beta| * |Rs| < |beta| * (alpha / 2 * |eta|) :=
    mul_lt_mul_of_pos_left hRs' (abs_pos.mpr hbeta)
  have hexp : beta * (alpha * eta - 3 * beta * x ^ 2 + Rs) =
      alpha * (eta * beta) - 3 * (beta ^ 2 * x ^ 2) + beta * Rs := by ring
  rw [hexp]
  have : |beta| * (alpha / 2 * |eta|) = alpha * (eta * beta) / 2 := by
    rw [← habs]; ring
  linarith

/-- The field seen in the coordinate `x = sgn · s`, multiplied by `sgn · β`. -/
theorem scaled_field_hasDerivAt (alpha beta : ℝ) (R Rs : ℝ → ℝ → ℝ) (sgn eta x : ℝ)
    (hd : HasDerivAt (R eta) (Rs eta (sgn * x)) (sgn * x)) :
    HasDerivAt (scaledField alpha beta R sgn eta)
      (sgn * beta * ((alpha * eta - 3 * beta * (sgn * x) ^ 2 + Rs eta (sgn * x)) * sgn)) x := by
  have hf := reducedField_hasDerivAt alpha beta R Rs eta (sgn * x) hd
  have hm : HasDerivAt (fun y : ℝ => sgn * y) sgn x := by
    simpa using (hasDerivAt_id x).const_mul sgn
  exact (hf.comp x hm).const_mul (sgn * beta)

/-- Strict monotonicity of the (scaled) field on the amplitude window. -/
theorem scaled_field_strictAntiOn (alpha beta C r eta sgn : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hC : 0 ≤ C)
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : BranchSmall alpha beta C r eta) (hside : 0 < eta * beta)
    (hsgn : sgn = 1 ∨ sgn = -1) :
    StrictAntiOn (scaledField alpha beta R sgn eta)
      (Set.Icc (Real.sqrt (alpha * eta / beta / 2)) (Real.sqrt (2 * (alpha * eta / beta)))) := by
  obtain ⟨hetar, -, h2t, hwin, -⟩ := hsmall
  have ht := amplitude_sq_pos alpha beta eta halpha hside
  have hsq : sgn * sgn = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsabs (x : ℝ) : |sgn * x| = |x| := by rcases hsgn with rfl | rfl <;> simp
  have hssq (x : ℝ) : (sgn * x) ^ 2 = x ^ 2 := by rcases hsgn with rfl | rfl <;> ring
  -- facts on the window
  have hwinfacts : ∀ x ∈ Set.Icc (Real.sqrt (alpha * eta / beta / 2))
      (Real.sqrt (2 * (alpha * eta / beta))),
      0 < x ∧ alpha * eta / beta / 2 ≤ x ^ 2 ∧ x ^ 2 ≤ 2 * (alpha * eta / beta) ∧
        |sgn * x| ≤ r := by
    intro x hx
    have hx0 : 0 < x := (Real.sqrt_pos.mpr (by positivity)).trans_le hx.1
    have hlo : alpha * eta / beta / 2 ≤ x ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx.1 2
      rwa [Real.sq_sqrt (by positivity)] at this
    have hhi : x ^ 2 ≤ 2 * (alpha * eta / beta) := by
      have := pow_le_pow_left₀ hx0.le hx.2 2
      rwa [Real.sq_sqrt (by positivity)] at this
    refine ⟨hx0, hlo, hhi, ?_⟩
    rw [hsabs, abs_of_pos hx0]
    have hr0 : 0 ≤ r := (abs_nonneg _).trans hetar
    nlinarith
  have hder : ∀ x ∈ Set.Icc (Real.sqrt (alpha * eta / beta / 2))
      (Real.sqrt (2 * (alpha * eta / beta))),
      HasDerivAt (scaledField alpha beta R sgn eta)
        (beta * (alpha * eta - 3 * beta * x ^ 2 + Rs eta (sgn * x))) x := by
    intro x hx
    obtain ⟨-, -, -, hxr⟩ := hwinfacts x hx
    have h := scaled_field_hasDerivAt alpha beta R Rs sgn eta x (hRder eta _ hetar hxr)
    convert h using 1
    rw [hssq]
    linear_combination (-(beta * (alpha * eta - 3 * beta * x ^ 2 + Rs eta (sgn * x)))) * hsq
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro x hx
    exact (hder x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(hder x hx').deriv]
    obtain ⟨hx0, hlo, hhi, hxr⟩ := hwinfacts x hx'
    have hb := hRs eta (sgn * x) hetar hxr
    rw [hssq, hsabs] at hb
    exact field_deriv_neg_on_window alpha beta C eta x _ hside hC hx0 hlo hhi hb hwin

/-! ## The neighbourhood of `η = 0` -/

theorem isOpen_curveSmall (alpha beta C r : ℝ) :
    IsOpen {eta | CurveSmall alpha beta C r eta} := by
  simp only [CurveSmall, Set.ofPred_and]
  refine IsOpen.inter (isOpen_lt ?_ ?_) (IsOpen.inter (isOpen_lt ?_ ?_)
    (IsOpen.inter (isOpen_lt ?_ ?_) (IsOpen.inter (isOpen_lt ?_ ?_)
    (IsOpen.inter (isOpen_lt ?_ ?_) (IsOpen.inter (isOpen_lt ?_ ?_) (isOpen_lt ?_ ?_)))))) <;>
    fun_prop

theorem curveSmall_zero (alpha beta C r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hC : 0 ≤ C) (hr : 0 < r) : CurveSmall alpha beta C r 0 := by
  have hρ := branchRadius_pos alpha beta C r halpha hbeta hC hr
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  refine ⟨by simpa using hr, by simpa using halpha, by simpa using pow_pos hρ 2,
    by simpa using half_pos halpha, by simpa using half_pos hb, by simpa using hb,
    by simpa using div_pos halpha hb⟩

theorem curveSmall_mem_nhds (alpha beta C r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hC : 0 ≤ C) (hr : 0 < r) : {eta | CurveSmall alpha beta C r eta} ∈ 𝓝 (0 : ℝ) :=
  (isOpen_curveSmall alpha beta C r).mem_nhds (curveSmall_zero alpha beta C r halpha hbeta hC hr)

/-! ## Existence and uniqueness of the root of each sign -/

/-- Existence of the root of sign `sgn` in the window, with amplitude and
derivative sign (from `mixed_branch_at`). -/
theorem branch_root_exists (alpha beta C r eta : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : CurveSmall alpha beta C r eta) (hside : 0 < eta * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    ∃ s, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta s ∧
      abs (|s| - Real.sqrt (alpha * eta / beta)) ≤ ampErr alpha beta C * |eta| ∧
      deriv (reducedField alpha beta R eta) s * beta < 0 := by
  obtain ⟨s, hs0, hroot, hamp, hder⟩ := mixed_branch_at alpha beta C r eta R Rs halpha hbeta
    hC hr hr1 hRval hRder hRs
    (curveSmall_branchSmall alpha beta C r eta halpha hbeta hC hr hsmall) hside sgn hsgn
  have h8 := amp_err_le_sqrt alpha beta C r eta halpha hC hside hsmall
  have hamp' : abs (|s| - Real.sqrt (alpha * eta / beta)) ≤ ampErr alpha beta C * |eta| :=
    hamp
  refine ⟨s, ⟨hs0, ?_, hroot⟩, hamp', hder⟩
  obtain ⟨-, hb⟩ := abs_le.mp hamp'
  have ht := amplitude_sq_pos alpha beta eta halpha hside
  have hsq0 := Real.sqrt_nonneg (alpha * eta / beta)
  have hρ := branchRadius_pos alpha beta C r halpha hbeta hC hr
  obtain ⟨-, -, h3, -⟩ := hsmall
  have hw := mem_window (alpha * eta / beta) (9 / 8 * Real.sqrt (alpha * eta / beta)) ht
    (by linarith) (by linarith)
  have h2 : Real.sqrt (2 * (alpha * eta / beta)) < branchRadius alpha beta C r :=
    (Real.sqrt_lt' hρ).mpr h3
  linarith [hw.2]

/-- Uniqueness of the root of sign `sgn` in the window `0 < sgn · s`, `|s| ≤ ρ`. -/
theorem branchRoot_unique (alpha beta C r eta : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : CurveSmall alpha beta C r eta) (hside : 0 < eta * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) {s s' : ℝ}
    (hs : BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta s)
    (hs' : BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta s') :
    s = s' := by
  have hsq : sgn * sgn = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsgn0 : sgn ≠ 0 := by rcases hsgn with rfl | rfl <;> norm_num
  have ht := amplitude_sq_pos alpha beta eta halpha hside
  have hsq0 := Real.sqrt_nonneg (alpha * eta / beta)
  have key : ∀ u, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta u →
      sgn * u ∈ Set.Icc (Real.sqrt (alpha * eta / beta / 2))
        (Real.sqrt (2 * (alpha * eta / beta))) ∧
      scaledField alpha beta R sgn eta (sgn * u) = 0 := by
    intro u ⟨hu0, huρ, hur⟩
    have hu : u ≠ 0 := by rintro rfl; simp at hu0
    obtain ⟨-, hlo, hhi⟩ := root_localize alpha beta C r eta u R Rs halpha hbeta hC hr1
      hRval hRs hsmall hu huρ hur
    rw [abs_eq_sgn_mul sgn u hsgn hu0] at hlo hhi
    have hw := mem_window (alpha * eta / beta) (sgn * u) ht (by linarith) (by linarith)
    refine ⟨?_, ?_⟩
    · exact hw
    · unfold scaledField
      rw [← mul_assoc, hsq, one_mul, hur, mul_zero]
  obtain ⟨hx, hFx⟩ := key s hs
  obtain ⟨hx', hFx'⟩ := key s' hs'
  have hanti := scaled_field_strictAntiOn alpha beta C r eta sgn R Rs halpha hC hRder hRs
    (curveSmall_branchSmall alpha beta C r eta halpha hbeta hC hr hsmall) hside hsgn
  exact mul_left_cancel₀ hsgn0 (hanti.injOn hx hx' (hFx.trans hFx'.symm))

/-- **Uniqueness** (Theorem 1.1, Step 5, TeX line 1981): on the side `η β > 0`
there is exactly one root of each sign in the fixed window `|s| ≤ ρ`. -/
theorem branchRoot_existsUnique (alpha beta C r eta : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : CurveSmall alpha beta C r eta) (hside : 0 < eta * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    ∃! s, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta s := by
  obtain ⟨s, hs, -, -⟩ := branch_root_exists alpha beta C r eta R Rs halpha hbeta hC hr hr1
    hRval hRder hRs hsmall hside sgn hsgn
  exact ⟨s, hs, fun y hy => branchRoot_unique alpha beta C r eta R Rs halpha hbeta hC hr hr1
    hRval hRder hRs hsmall hside sgn hsgn hy hs⟩

/-- **Local uniqueness of the two branches**, in Mathlib vocabulary. In arXiv:2610.20976v1,
Step 5 of the proof of Theorem 1.1 (TeX line 1969) gives existence only; uniqueness is used,
not argued, in the proofs of Theorem 1.3(1) (TeX line 2866) and Theorem 1.3(3) (TeX line 3024),
finding `v1-proof-gap-local-uniqueness`. Statement: on a fixed window `|s| ≤ ρ`, with `ρ`
independent of `η`, for each small `η` on the bifurcating side `η β > 0` there is exactly one root of each sign of
the reduced field `α η s - β s³ + R η s`. Here `ρ = branchRadius α β C r` and the
neighbourhood of `0` is `{η | CurveSmall α β C r η}`; this restates
`branchRoot_existsUnique` with `BranchRoot` and `reducedField` unfolded. -/
theorem branchRoot_existsUnique_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) :
    ∃ ρ > 0, ∀ᶠ eta in 𝓝 (0 : ℝ), 0 < eta * beta → ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
      ∃! s, 0 < sgn * s ∧ |s| ≤ ρ ∧ alpha * eta * s - beta * s ^ 3 + R eta s = 0 := by
  refine ⟨branchRadius alpha beta C r, branchRadius_pos alpha beta C r halpha hbeta hC hr, ?_⟩
  filter_upwards [curveSmall_mem_nhds alpha beta C r halpha hbeta hC hr] with eta hsmall
  intro hside sgn hsgn
  exact branchRoot_existsUnique alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs
    hsmall hside sgn hsgn

/-! ## The branch functions -/

/-- The branch value is the root of sign `sgn`, with the amplitude estimate and
the derivative sign. -/
theorem branch_spec (alpha beta C r eta : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : CurveSmall alpha beta C r eta) (hside : 0 < eta * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta
        (branch alpha beta (branchRadius alpha beta C r) R sgn eta) ∧
      abs (|branch alpha beta (branchRadius alpha beta C r) R sgn eta| -
          Real.sqrt (alpha * eta / beta)) ≤ ampErr alpha beta C * |eta| ∧
      deriv (reducedField alpha beta R eta)
          (branch alpha beta (branchRadius alpha beta C r) R sgn eta) * beta < 0 := by
  obtain ⟨s, hs, hamp, hder⟩ := branch_root_exists alpha beta C r eta R Rs halpha hbeta hC
    hr hr1 hRval hRder hRs hsmall hside sgn hsgn
  have hex : ∃ s, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta s := ⟨s, hs⟩
  have hb : branch alpha beta (branchRadius alpha beta C r) R sgn eta = s := by
    have hc : branch alpha beta (branchRadius alpha beta C r) R sgn eta = hex.choose := by
      unfold branch
      rw [dite_eq_left hex]
    rw [hc]
    exact branchRoot_unique alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs
      hsmall hside sgn hsgn hex.choose_spec hs
  rw [hb]
  exact ⟨hs, hamp, hder⟩

theorem branch_eq_of_root (alpha beta C r eta : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : CurveSmall alpha beta C r eta) (hside : 0 < eta * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) {s : ℝ}
    (hs : BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta s) :
    branch alpha beta (branchRadius alpha beta C r) R sgn eta = s :=
  branchRoot_unique alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs hsmall hside
    sgn hsgn (branch_spec alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs hsmall
      hside sgn hsgn).1 hs

/-- Off the side `η β > 0` there is no nontrivial small root, so the branch
function is `0` there (in particular at `η = 0`). -/
theorem branch_eq_zero_of_not_side (alpha beta C r eta : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : CurveSmall alpha beta C r eta) (hside : eta * beta ≤ 0) (sgn : ℝ) :
    branch alpha beta (branchRadius alpha beta C r) R sgn eta = 0 := by
  have hne : ¬ ∃ s, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta s := by
    rintro ⟨s, hs0, hsρ, hroot⟩
    have hs : s ≠ 0 := by rintro rfl; simp at hs0
    exact absurd (root_localize alpha beta C r eta s R Rs halpha hbeta hC hr1 hRval hRs
      hsmall hs hsρ hroot).1 (not_lt.mpr hside)
  unfold branch
  rw [dite_eq_right hne]

/-- **Classification** (clause 3): every small nontrivial equilibrium lies on the
side `η β > 0` and is one of the two branch values. -/
theorem small_roots_classification (alpha beta C r eta s : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : CurveSmall alpha beta C r eta) (hs : s ≠ 0)
    (hsρ : |s| ≤ branchRadius alpha beta C r)
    (hroot : reducedField alpha beta R eta s = 0) :
    0 < eta * beta ∧
      (s = branch alpha beta (branchRadius alpha beta C r) R 1 eta ∨
        s = branch alpha beta (branchRadius alpha beta C r) R (-1) eta) := by
  have hside := (root_localize alpha beta C r eta s R Rs halpha hbeta hC hr1 hRval hRs hsmall
    hs hsρ hroot).1
  refine ⟨hside, ?_⟩
  rcases lt_or_gt_of_ne hs with h | h
  · right
    exact (branch_eq_of_root alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs
      hsmall hside (-1) (Or.inr rfl) ⟨by linarith, hsρ, hroot⟩).symm
  · left
    exact (branch_eq_of_root alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs
      hsmall hside 1 (Or.inl rfl) ⟨by linarith, hsρ, hroot⟩).symm

/-- The branch functions are bounded by `9/8 · √(αη/β)` on the whole
neighbourhood (and vanish off the side). -/
theorem branch_abs_le (alpha beta C r eta : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : CurveSmall alpha beta C r eta) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    |branch alpha beta (branchRadius alpha beta C r) R sgn eta| ≤
      9 / 8 * Real.sqrt (alpha * eta / beta) := by
  rcases lt_or_ge 0 (eta * beta) with hside | hside
  · obtain ⟨⟨hpos, hρ, hroot⟩, -, -⟩ := branch_spec alpha beta C r eta R Rs halpha hbeta hC hr
      hr1 hRval hRder hRs hsmall hside sgn hsgn
    have hne : branch alpha beta (branchRadius alpha beta C r) R sgn eta ≠ 0 := by
      intro h; rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
    exact (root_localize alpha beta C r eta _ R Rs halpha hbeta hC hr1 hRval hRs hsmall hne hρ
      hroot).2.2
  · rw [branch_eq_zero_of_not_side alpha beta C r eta R Rs halpha hbeta hC hr1 hRval hRs hsmall
      hside sgn, abs_zero]
    positivity

/-! ## Continuity of the branch functions -/

theorem scaledField_continuousAt_eta (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (sgn y eta0 : ℝ)
    (h : ContinuousAt (fun e => R e (sgn * y)) eta0) :
    ContinuousAt (fun e => scaledField alpha beta R sgn e y) eta0 := by
  unfold scaledField reducedField
  fun_prop

/-- Continuity of the branch function at a point on the side `η β > 0`. The
only input beyond the value/derivative interface is `hRcont`: continuity of
`η ↦ R η s` for each fixed small `s`. -/
theorem branch_continuousAt_side (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hRcont : ∀ e s, |e| < r → |s| ≤ r → ContinuousAt (fun e' => R e' s) e)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) (eta0 : ℝ)
    (hsmall0 : CurveSmall alpha beta C r eta0) (hside0 : 0 < eta0 * beta) :
    ContinuousAt (branch alpha beta (branchRadius alpha beta C r) R sgn) eta0 := by
  have hsq : sgn * sgn = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsgn0 : sgn ≠ 0 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsabs : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hρ := branchRadius_pos alpha beta C r halpha hbeta hC hr
  have ht0 := amplitude_sq_pos alpha beta eta0 halpha hside0
  have hsqrt0 : 0 < Real.sqrt (alpha * eta0 / beta) := Real.sqrt_pos.mpr ht0
  obtain ⟨⟨hpos0, hρ0, hroot0⟩, -, -⟩ := branch_spec alpha beta C r eta0 R Rs halpha hbeta hC
    hr hr1 hRval hRder hRs hsmall0 hside0 sgn hsgn
  obtain ⟨b0, hb0⟩ : ∃ b0, b0 = branch alpha beta (branchRadius alpha beta C r) R sgn eta0 :=
    ⟨_, rfl⟩
  rw [← hb0] at hpos0 hρ0 hroot0
  have hb0ne : b0 ≠ 0 := by intro h; rw [h, mul_zero] at hpos0; exact lt_irrefl _ hpos0
  obtain ⟨-, hlo, hhi⟩ := root_localize alpha beta C r eta0 b0 R Rs halpha hbeta hC hr1 hRval
    hRs hsmall0 hb0ne hρ0 hroot0
  rw [abs_eq_sgn_mul sgn b0 hsgn hpos0] at hlo hhi
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = sgn * b0 := ⟨_, rfl⟩
  rw [← hx0] at hlo hhi
  have hbx : b0 = sgn * x0 := by rw [hx0, ← mul_assoc, hsq, one_mul]
  have h2t0 : Real.sqrt (2 * (alpha * eta0 / beta)) < branchRadius alpha beta C r :=
    (Real.sqrt_lt' hρ).mpr hsmall0.2.2.1
  have hρr := branchRadius_le alpha beta C r
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = min (ε / 2) (Real.sqrt (alpha * eta0 / beta) / 16) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by positivity)
  have hδ1 : δ ≤ ε / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδ2 : δ ≤ Real.sqrt (alpha * eta0 / beta) / 16 := by rw [hδdef]; exact min_le_right _ _
  have hmemA := mem_window (alpha * eta0 / beta) (x0 - δ) ht0 (by linarith) (by linarith)
  have hmemC := mem_window (alpha * eta0 / beta) (x0 + δ) ht0 (by linarith) (by linarith)
  have hmem0 := mem_window (alpha * eta0 / beta) x0 ht0 (by linarith) (by linarith)
  have hwin : ∀ x ∈ Set.Icc (Real.sqrt (alpha * eta0 / beta / 2))
      (Real.sqrt (2 * (alpha * eta0 / beta))), |sgn * x| ≤ r := by
    intro x hx
    have hx0' : 0 ≤ x := (Real.sqrt_nonneg _).trans hx.1
    rw [abs_mul, hsabs, one_mul, abs_of_nonneg hx0']
    linarith [hx.2]
  have hanti := scaled_field_strictAntiOn alpha beta C r eta0 sgn R Rs halpha hC hRder hRs
    (curveSmall_branchSmall alpha beta C r eta0 halpha hbeta hC hr hsmall0) hside0 hsgn
  have hF0 : scaledField alpha beta R sgn eta0 x0 = 0 := by
    unfold scaledField
    rw [← hbx, hroot0, mul_zero]
  have hFa : 0 < scaledField alpha beta R sgn eta0 (x0 - δ) := by
    rw [← hF0]; exact hanti hmemA hmem0 (by linarith)
  have hFc : scaledField alpha beta R sgn eta0 (x0 + δ) < 0 := by
    rw [← hF0]; exact hanti hmem0 hmemC (by linarith)
  have hη0r : |eta0| < r := hsmall0.1
  have ev1 : ∀ᶠ eta in 𝓝 eta0, CurveSmall alpha beta C r eta :=
    (isOpen_curveSmall alpha beta C r).mem_nhds hsmall0
  have ev2 : ∀ᶠ eta in 𝓝 eta0, 0 < eta * beta :=
    (continuousAt_id.mul continuousAt_const : ContinuousAt (fun e : ℝ => e * beta) eta0).eventually
      (lt_mem_nhds hside0)
  have ev3 : ∀ᶠ eta in 𝓝 eta0, 0 < scaledField alpha beta R sgn eta (x0 - δ) :=
    (scaledField_continuousAt_eta alpha beta R sgn (x0 - δ) eta0
      (hRcont eta0 _ hη0r (hwin _ hmemA))).eventually (lt_mem_nhds hFa)
  have ev4 : ∀ᶠ eta in 𝓝 eta0, scaledField alpha beta R sgn eta (x0 + δ) < 0 :=
    (scaledField_continuousAt_eta alpha beta R sgn (x0 + δ) eta0
      (hRcont eta0 _ hη0r (hwin _ hmemC))).eventually (gt_mem_nhds hFc)
  filter_upwards [ev1, ev2, ev3, ev4] with eta hsm hsd hFa' hFc'
  have hsub : Set.Icc (x0 - δ) (x0 + δ) ⊆ Set.Icc (Real.sqrt (alpha * eta0 / beta / 2))
      (Real.sqrt (2 * (alpha * eta0 / beta))) :=
    fun y hy => ⟨hmemA.1.trans hy.1, hy.2.trans hmemC.2⟩
  have hcont : ContinuousOn (scaledField alpha beta R sgn eta) (Set.Icc (x0 - δ) (x0 + δ)) := by
    intro y hy
    exact (scaled_field_hasDerivAt alpha beta R Rs sgn eta y
      (hRder eta _ hsm.1.le (hwin y (hsub hy)))).continuousAt.continuousWithinAt
  obtain ⟨y, hy, hFy⟩ := intermediate_value_Icc' (by linarith) hcont ⟨hFc'.le, hFa'.le⟩
  have hy0 : 0 < y := by linarith [hy.1]
  have hroot : BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta (sgn * y) := by
    refine ⟨by rw [← mul_assoc, hsq, one_mul]; exact hy0, ?_, ?_⟩
    · rw [abs_mul, hsabs, one_mul, abs_of_pos hy0]
      linarith [hy.2, hmemC.2]
    · unfold scaledField at hFy
      exact (mul_eq_zero.mp hFy).resolve_left (mul_ne_zero hsgn0 hbeta)
  rw [branch_eq_of_root alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs hsm hsd
    sgn hsgn hroot, ← hb0, hbx, Real.dist_eq, ← mul_sub, abs_mul, hsabs, one_mul, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

/-- The branch functions vanish at `η = 0`. -/
theorem branch_zero (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) (sgn : ℝ) :
    branch alpha beta (branchRadius alpha beta C r) R sgn 0 = 0 :=
  branch_eq_zero_of_not_side alpha beta C r 0 R Rs halpha hbeta hC hr1 hRval hRs
    (curveSmall_zero alpha beta C r halpha hbeta hC hr) (by simp) sgn

/-- **Through the origin**: `s^±(η) → 0` as `η → 0`. -/
theorem branch_tendsto_zero (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    Tendsto (branch alpha beta (branchRadius alpha beta C r) R sgn) (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun eta : ℝ => 9 / 8 * Real.sqrt (alpha * eta / beta) := by fun_prop
  have hlim : Tendsto (fun eta : ℝ => 9 / 8 * Real.sqrt (alpha * eta / beta)) (𝓝 0) (𝓝 0) := by
    simpa using hc.tendsto 0
  apply squeeze_zero_norm' _ hlim
  filter_upwards [curveSmall_mem_nhds alpha beta C r halpha hbeta hC hr] with eta h
  rw [Real.norm_eq_abs]
  exact branch_abs_le alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs h sgn hsgn

/-- **Continuity** (Theorem 1.1, "continuous curves `Γ^±`"): each branch function
is continuous on the open neighbourhood `{η | CurveSmall η}` of `0`. -/
theorem branch_continuousOn (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hRcont : ∀ e s, |e| < r → |s| ≤ r → ContinuousAt (fun e' => R e' s) e)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    ContinuousOn (branch alpha beta (branchRadius alpha beta C r) R sgn)
      {eta | CurveSmall alpha beta C r eta} := by
  intro eta0 h0
  apply ContinuousAt.continuousWithinAt
  rcases lt_trichotomy (eta0 * beta) 0 with hneg | hzero | hpos
  · have ev : ∀ᶠ eta in 𝓝 eta0, CurveSmall alpha beta C r eta ∧ eta * beta < 0 :=
      Filter.Eventually.and ((isOpen_curveSmall alpha beta C r).mem_nhds h0)
        ((continuousAt_id.mul continuousAt_const :
          ContinuousAt (fun e : ℝ => e * beta) eta0).eventually (gt_mem_nhds hneg))
    have heq : (fun _ => (0 : ℝ)) =ᶠ[𝓝 eta0]
        branch alpha beta (branchRadius alpha beta C r) R sgn :=
      ev.mono fun eta h => (branch_eq_zero_of_not_side alpha beta C r eta R Rs halpha hbeta hC
        hr1 hRval hRs h.1 h.2.le sgn).symm
    exact continuousAt_const.congr heq
  · have he : eta0 = 0 := (mul_eq_zero.mp hzero).resolve_right hbeta
    subst he
    rw [ContinuousAt, branch_zero alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRs sgn]
    exact branch_tendsto_zero alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRder hRs sgn hsgn
  · exact branch_continuousAt_side alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRder hRs
      hRcont sgn hsgn eta0 h0 hpos

/-! ## The packaged statement -/

/-- **Theorem 1.1, scalar branch curves `Γ^±` (Step 5, TeX lines 1975--1995;
"local uniqueness", TeX line 884).** Under the weak mixed remainder interface
of `MixedRemainder` plus continuity of `η ↦ R η s`, there are a window radius
`ρ > 0` and an open neighbourhood `U` of `η = 0` such that, for each sign
`sgn = ±1`, the branch function `s^{sgn}(η)`:
* is continuous on `U`, vanishes at `η = 0`, and tends to `0` as `η → 0`;
* vanishes for `η ∈ U` with `η β ≤ 0`;
* for `η ∈ U` with `η β > 0` is the unique root of sign `sgn` in `|s| ≤ ρ`,
  with amplitude `√(αη/β) + O(|η|)` and `(∂ₛ field) · β < 0`;
and every nontrivial root `0 < |s| ≤ ρ` at `η ∈ U` is one of `s^±(η)`. -/
theorem branch_curves (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hRcont : ∀ e s, |e| < r → |s| ≤ r → ContinuousAt (fun e' => R e' s) e) :
    0 < branchRadius alpha beta C r ∧ IsOpen {eta | CurveSmall alpha beta C r eta} ∧
      {eta | CurveSmall alpha beta C r eta} ∈ 𝓝 (0 : ℝ) ∧
      (∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
        ContinuousOn (branch alpha beta (branchRadius alpha beta C r) R sgn)
            {eta | CurveSmall alpha beta C r eta} ∧
          branch alpha beta (branchRadius alpha beta C r) R sgn 0 = 0 ∧
          Tendsto (branch alpha beta (branchRadius alpha beta C r) R sgn) (𝓝 0) (𝓝 0) ∧
          (∀ eta, CurveSmall alpha beta C r eta → eta * beta ≤ 0 →
            branch alpha beta (branchRadius alpha beta C r) R sgn eta = 0) ∧
          (∀ eta, CurveSmall alpha beta C r eta → 0 < eta * beta →
            (∃! s, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta s) ∧
            BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta
                (branch alpha beta (branchRadius alpha beta C r) R sgn eta) ∧
            abs (|branch alpha beta (branchRadius alpha beta C r) R sgn eta| -
                Real.sqrt (alpha * eta / beta)) ≤ ampErr alpha beta C * |eta| ∧
            deriv (reducedField alpha beta R eta)
                (branch alpha beta (branchRadius alpha beta C r) R sgn eta) * beta < 0)) ∧
      (∀ eta s, CurveSmall alpha beta C r eta → s ≠ 0 →
        |s| ≤ branchRadius alpha beta C r → reducedField alpha beta R eta s = 0 →
        0 < eta * beta ∧
          (s = branch alpha beta (branchRadius alpha beta C r) R 1 eta ∨
            s = branch alpha beta (branchRadius alpha beta C r) R (-1) eta)) := by
  refine ⟨branchRadius_pos alpha beta C r halpha hbeta hC hr, isOpen_curveSmall alpha beta C r,
    curveSmall_mem_nhds alpha beta C r halpha hbeta hC hr, fun sgn hsgn => ?_,
    fun eta s h hs hsρ hroot => small_roots_classification alpha beta C r eta s R Rs halpha hbeta
      hC hr hr1 hRval hRder hRs h hs hsρ hroot⟩
  refine ⟨branch_continuousOn alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRder hRs hRcont
      sgn hsgn, branch_zero alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRs sgn,
    branch_tendsto_zero alpha beta C r R Rs halpha hbeta hC hr hr1 hRval hRder hRs sgn hsgn,
    fun eta h hside => branch_eq_zero_of_not_side alpha beta C r eta R Rs halpha hbeta hC hr1
      hRval hRs h hside sgn, fun eta h hside => ?_⟩
  exact ⟨branchRoot_existsUnique alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs
    h hside sgn hsgn, branch_spec alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs
    h hside sgn hsgn⟩

/-- The same packaged statement from the Eq. 2.43 bounds (`u² χ̃²` in the value,
`|u| χ̃²` in the derivative), through the weak interface. -/
theorem center_ODE_final_branch_curves (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hRcont : ∀ e s, |e| < r → |s| ≤ r → ContinuousAt (fun e' => R e' s) e) (sgn : ℝ)
    (hsgn : sgn = 1 ∨ sgn = -1) :
    ContinuousOn (branch alpha beta (branchRadius alpha beta C r) R sgn)
        {eta | CurveSmall alpha beta C r eta} ∧
      Tendsto (branch alpha beta (branchRadius alpha beta C r) R sgn) (𝓝 0) (𝓝 0) ∧
      ∀ eta, CurveSmall alpha beta C r eta → 0 < eta * beta →
        ∃! s, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta s := by
  have hRval' : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4) := fun e s he hs =>
    center_ODE_final_value_bound_weak e s (R e s) C hC (hs.trans hr1) (hRval e s he hs)
  have hRs' : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3) := fun e s he hs =>
    center_ODE_final_deriv_bound_weak e s (Rs e s) C hC (hs.trans hr1) (hRs e s he hs)
  exact ⟨branch_continuousOn alpha beta C r R Rs halpha hbeta hC hr hr1 hRval' hRder hRs' hRcont
      sgn hsgn,
    branch_tendsto_zero alpha beta C r R Rs halpha hbeta hC hr hr1 hRval' hRder hRs' sgn hsgn,
    fun eta h hside => branchRoot_existsUnique alpha beta C r eta R Rs halpha hbeta hC hr hr1
      hRval' hRder hRs' h hside sgn hsgn⟩

end ChemotaxisBifurcation.BranchCurves
