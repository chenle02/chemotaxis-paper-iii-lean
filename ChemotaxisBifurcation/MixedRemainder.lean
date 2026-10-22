module
public import ChemotaxisBifurcation.RemainderBounds

@[expose] public section

/-!
# The mixed center-manifold remainder (Eq. 2.43, Eq. 2.48, Remark 1.1)

The 44-page manuscript states the reduced scalar equation on the center
manifold in two forms:

* `\label{E:center-ODE-final}` (Eq. 2.43, non-minimal model, TeX line 1943)
  has remainder `O(|u|² |χ̃|² + |u|³ |χ̃| + |u|⁴)`;
* `\label{E:center-ODE-initial-minimal}` (Eq. 2.48, minimal model, TeX line
  2139) and `\label{R:local-bifurcation-minimal}` (Remark 1.1, TeX line 648)
  use `O(|u| |χ̃|² + |u|³ |χ̃| + |u|⁴)`.

This module does not choose between them. It states the scalar consumer of
Step 5 (TeX line 1975) and Step 4' under the weaker bound

`|R(u, χ̃)| ≤ C (|u| χ̃² + |u|³ |χ̃| + u⁴)`,

together with the matching derivative bound
`|∂ᵤR(u, χ̃)| ≤ C (χ̃² + u² |χ̃| + |u|³)`, and shows that the Eq. 2.43 bound
implies this interface when `|u| ≤ 1`. The manuscript states no derivative
bound; the derivative input is an explicit hypothesis here.

The bridge lemma absorbs the extra `|u| χ̃²` term along an equilibrium:
there `|χ̃| ≤ D u²`, so `|u| χ̃² ≤ D |χ̃| |u|³`, which is of the form already
handled by `NormalForm.paper_equilibrium_core`.

The function-level theorems take the remainder `R(η, s)` and a derivative
`Rs(η, s)` (`HasDerivAt (R η) (Rs η s) s`) on a box `|η|, |s| ≤ r ≤ 1`,
prove existence of nontrivial equilibria of both signs by the intermediate
value theorem, and conclude the side condition, the amplitude and the
derivative sign for all `η` near `0` (`mixed_branch_eventually`,
`mixed_side_condition_eventually`). Uniqueness and continuity in `η` of the
branch (the curves `Γ^±`) are not proved here.

Center-manifold existence, the graph estimates that produce the remainder
bounds, and the lifting of the scalar derivative sign to PDE stability are not
proved here; they are the remainder hypotheses and are not used as conclusions.
Notation: `eta = χ̃ = χ₀ - χ*`, `s = u_{n₀}`, `alpha = α_{n₀}`,
`beta = β_{n₀}`.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.MixedRemainder

open ChemotaxisBifurcation.NormalForm Filter Topology

/-- The constant `D` in `|χ̃| ≤ D u²` along a small equilibrium. -/
noncomputable def ampConst (alpha beta C : ℝ) : ℝ :=
  2 * (|beta| + 2 * C) / alpha

/-- The constant of the absorbed (Eq. 2.43-free) remainder bound. -/
noncomputable def absorbedConst (alpha beta C : ℝ) : ℝ :=
  C * (ampConst alpha beta C + 1)

theorem ampConst_nonneg (alpha beta C : ℝ) (halpha : 0 < alpha) (hC : 0 ≤ C) :
    0 ≤ ampConst alpha beta C := by
  unfold ampConst
  positivity

theorem absorbedConst_nonneg (alpha beta C : ℝ) (halpha : 0 < alpha) (hC : 0 ≤ C) :
    0 ≤ absorbedConst alpha beta C := by
  unfold absorbedConst
  have := ampConst_nonneg alpha beta C halpha hC
  positivity

/-! ## Eq. 2.43 implies the weaker interface -/

/-- The Eq. 2.43 value bound implies the weaker (Remark 1.1 / Eq. 2.48) value
bound when `|s| ≤ 1`. -/
theorem center_ODE_final_value_bound_weak (eta s R C : ℝ)
    (hC : 0 ≤ C) (hs1 : |s| ≤ 1)
    (hR : |R| ≤ C * (s ^ 2 * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4)) :
    |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4) := by
  have hss : s ^ 2 ≤ |s| := by nlinarith [sq_abs s, abs_nonneg s]
  have h1 : s ^ 2 * eta ^ 2 ≤ |s| * eta ^ 2 :=
    mul_le_mul_of_nonneg_right hss (sq_nonneg eta)
  calc
    |R| ≤ C * (s ^ 2 * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4) := hR
    _ ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4) := by gcongr

/-- The derivative of the Eq. 2.43 remainder form, `|s| χ̃² + s² |χ̃| + |s|³`,
implies the weaker derivative bound when `|s| ≤ 1`. -/
theorem center_ODE_final_deriv_bound_weak (eta s Rs C : ℝ)
    (hC : 0 ≤ C) (hs1 : |s| ≤ 1)
    (hRs : |Rs| ≤ C * (|s| * eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3)) :
    |Rs| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := by
  have h1 : |s| * eta ^ 2 ≤ eta ^ 2 := by
    nlinarith [sq_nonneg eta]
  calc
    |Rs| ≤ C * (|s| * eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := hRs
    _ ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := by gcongr

/-! ## Bridge: absorbing `|u| χ̃²` along an equilibrium -/

/-- Along a small nonzero equilibrium of the divided equation with the weak
divided remainder, the parameter is controlled by the squared amplitude:
`|η| ≤ D s²`. -/
theorem mixed_parameter_le_amp_sq (alpha beta eta s e C : ℝ)
    (halpha : 0 < alpha) (hC : 0 ≤ C)
    (heta1 : |eta| ≤ 1) (hs1 : |s| ≤ 1) (hetaC : 2 * C * |eta| ≤ alpha)
    (hroot : alpha * eta - beta * s ^ 2 + e = 0)
    (he : |e| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3)) :
    |eta| ≤ ampConst alpha beta C * s ^ 2 := by
  have hid : alpha * eta = beta * s ^ 2 + -e := by linarith
  have h1 := abs_add_le (beta * s ^ 2) (-e)
  rw [← hid] at h1
  simp only [abs_mul, abs_neg, abs_of_pos halpha, abs_of_nonneg (sq_nonneg s)] at h1
  have hs3 : |s| ^ 3 ≤ s ^ 2 := by
    rw [← sq_abs s]
    nlinarith [abs_nonneg s, sq_nonneg |s|]
  have heta2 : eta ^ 2 = |eta| * |eta| := by rw [← sq_abs eta]; ring
  have hCeta : C * eta ^ 2 ≤ alpha / 2 * |eta| := by
    rw [heta2]; nlinarith [abs_nonneg eta]
  have hsC : C * (s ^ 2 * |eta|) ≤ C * s ^ 2 := by
    have := mul_le_mul_of_nonneg_left heta1 (sq_nonneg s)
    nlinarith
  have hs3C : C * |s| ^ 3 ≤ C * s ^ 2 := mul_le_mul_of_nonneg_left hs3 hC
  have hmain : alpha / 2 * |eta| ≤ (|beta| + 2 * C) * s ^ 2 := by nlinarith
  unfold ampConst
  rw [div_mul_eq_mul_div, le_div_iff₀ halpha]
  nlinarith

/-- Pure absorption step: once `|η| ≤ D s²`, the weak divided remainder form
is bounded by `(D + 1) (|η| + |s|) s²`, the form of the existing core. -/
theorem mixed_divided_absorb (eta s D : ℝ)
    (heta : |eta| ≤ D * s ^ 2) :
    eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3 ≤ (D + 1) * (|eta| + |s|) * s ^ 2 := by
  have heta2 : eta ^ 2 ≤ D * s ^ 2 * |eta| := by
    rw [← sq_abs eta, sq]
    exact mul_le_mul_of_nonneg_right heta (abs_nonneg eta)
  have hs3 : |s| ^ 3 = |s| * s ^ 2 := by rw [← sq_abs s]; ring
  rw [hs3]
  have hDs : 0 ≤ D * s ^ 2 := (abs_nonneg eta).trans heta
  nlinarith [abs_nonneg eta, abs_nonneg s, sq_nonneg s, mul_nonneg hDs (abs_nonneg s)]

/-- Bridge for the value remainder: along an equilibrium (`|η| ≤ D s²`) the
weak value bound implies the bound assumed by `paper_equilibrium_core`. -/
theorem mixed_value_bound_absorbed (eta s R C D : ℝ) (hC : 0 ≤ C)
    (heta : |eta| ≤ D * s ^ 2)
    (hR : |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4)) :
    |R| ≤ (C * (D + 1)) * (|eta| * |s| ^ 3 + |s| ^ 4) := by
  have hab := mixed_divided_absorb eta s D heta
  have hfac : |s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4 =
      |s| * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := by
    rw [← (by decide : Even 4).pow_abs s, ← sq_abs s]; ring
  calc
    |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4) := hR
    _ = C * |s| * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := by rw [hfac]; ring
    _ ≤ C * |s| * ((D + 1) * (|eta| + |s|) * s ^ 2) := by
      have : 0 ≤ C * |s| := mul_nonneg hC (abs_nonneg s)
      exact mul_le_mul_of_nonneg_left hab this
    _ = (C * (D + 1)) * (|eta| * |s| ^ 3 + |s| ^ 4) := by rw [← sq_abs s]; ring

/-- Bridge for the derivative remainder: along an equilibrium the weak
derivative bound implies the derivative bound of `paper_equilibrium_core`. -/
theorem mixed_deriv_bound_absorbed (eta s Rs C D : ℝ) (hC : 0 ≤ C)
    (heta : |eta| ≤ D * s ^ 2)
    (hRs : |Rs| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3)) :
    |Rs| ≤ (C * (D + 1)) * (|eta| * s ^ 2 + |s| ^ 3) := by
  have hab := mixed_divided_absorb eta s D heta
  calc
    |Rs| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := hRs
    _ ≤ C * ((D + 1) * (|eta| + |s|) * s ^ 2) := mul_le_mul_of_nonneg_left hab hC
    _ = (C * (D + 1)) * (|eta| * s ^ 2 + |s| ^ 3) := by rw [← sq_abs s]; ring

/-! ## The scalar endgame under the weak interface -/

/-- Step 5 / Step 4' scalar conclusions under the weak mixed remainder.
For a nonzero small equilibrium `s` of
`α η s - β s³ + R = 0` with `|R| ≤ C (|s| η² + |s|³ |η| + s⁴)` and derivative
`ds = α η - 3 β s² + Rs` with `|Rs| ≤ C (η² + s² |η| + |s|³)`:
the side condition `η β > 0`, the derivative sign `ds β < 0`, and the
square-root amplitude `|s| = √(α η / β) + O(|η|)`. -/
theorem mixed_equilibrium_core (alpha beta eta s R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : s ≠ 0) (hC : 0 ≤ C)
    (hs1 : |s| ≤ 1) (heta1 : |eta| ≤ 1) (hetaC : 2 * C * |eta| ≤ alpha)
    (hroot : alpha * eta * s - beta * s ^ 3 + R = 0)
    (hderiv : ds = alpha * eta - 3 * beta * s ^ 2 + Rs)
    (hR : |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4))
    (hRs : |Rs| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3))
    (hrectangle : absorbedConst alpha beta C * (|eta| + |s|) ≤ |beta| / 2) :
    0 < eta * beta ∧ ds * beta < 0 ∧
      abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
        (2 * alpha * absorbedConst alpha beta C *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| := by
  have hsabs : 0 < |s| := abs_pos.mpr hs
  have hdivroot : alpha * eta - beta * s ^ 2 + R / s = 0 := by
    calc
      alpha * eta - beta * s ^ 2 + R / s =
          (alpha * eta * s - beta * s ^ 3 + R) / s := by
        field_simp [hs]
      _ = 0 := by rw [hroot]; simp
  have hdivR : |R / s| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := by
    rw [abs_div]
    apply (div_le_iff₀ hsabs).mpr
    calc
      |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4) := hR
      _ = C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) * |s| := by
        rw [← (by decide : Even 4).pow_abs s, ← sq_abs s]; ring
  have heta := mixed_parameter_le_amp_sq alpha beta eta s (R / s) C
    halpha hC heta1 hs1 hetaC hdivroot hdivR
  exact paper_equilibrium_core alpha beta eta s R Rs ds (absorbedConst alpha beta C)
    halpha hbeta hs (absorbedConst_nonneg alpha beta C halpha hC) hs1 hroot hderiv
    (mixed_value_bound_absorbed eta s R C _ hC heta hR)
    (mixed_deriv_bound_absorbed eta s Rs C _ hC heta hRs) hrectangle

/-- The same conclusions from the Eq. 2.43 bounds, through the weak interface. -/
theorem center_ODE_final_equilibrium_core (alpha beta eta s R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : s ≠ 0) (hC : 0 ≤ C)
    (hs1 : |s| ≤ 1) (heta1 : |eta| ≤ 1) (hetaC : 2 * C * |eta| ≤ alpha)
    (hroot : alpha * eta * s - beta * s ^ 3 + R = 0)
    (hderiv : ds = alpha * eta - 3 * beta * s ^ 2 + Rs)
    (hR : |R| ≤ C * (s ^ 2 * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4))
    (hRs : |Rs| ≤ C * (|s| * eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3))
    (hrectangle : absorbedConst alpha beta C * (|eta| + |s|) ≤ |beta| / 2) :
    0 < eta * beta ∧ ds * beta < 0 ∧
      abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
        (2 * alpha * absorbedConst alpha beta C *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| :=
  mixed_equilibrium_core alpha beta eta s R Rs ds C halpha hbeta hs hC hs1 heta1 hetaC
    hroot hderiv (center_ODE_final_value_bound_weak eta s R C hC hs1 hR)
    (center_ODE_final_deriv_bound_weak eta s Rs C hC hs1 hRs) hrectangle

/-! ## Existence of the two nontrivial equilibria (intermediate value theorem) -/

/-- On the side `η β > 0`, the leading squared amplitude `α η / β` equals
`α |η| / |β|`. -/
theorem amp_sq_eq_abs (alpha beta eta : ℝ) (hside : 0 < eta * beta) :
    alpha * eta / beta = alpha * |eta| / |beta| := by
  have hb : beta ≠ 0 := by rintro rfl; simp at hside
  rcases mul_pos_iff.mp hside with h | h
  · rw [abs_of_pos h.1, abs_of_pos h.2]
  · rw [abs_of_neg h.1, abs_of_neg h.2]
    field_simp

/-- Size of the weak value remainder below the amplitude scale `s² ≤ 2 α η / β`. -/
theorem weak_value_lt_on_window (alpha beta eta s R C : ℝ)
    (hside : 0 < eta * beta) (hC : 0 ≤ C) (hs : 0 < s)
    (hs2 : s ^ 2 ≤ 2 * (alpha * eta / beta))
    (hR : |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4))
    (hsmall : C * (|eta| + 2 * (alpha * eta / beta) +
        2 * alpha * Real.sqrt (2 * (alpha * eta / beta)) / |beta|) < alpha / 2) :
    |R| < s * (alpha / 2 * |eta|) := by
  have heta : 0 < |eta| := abs_pos.mpr (by rintro rfl; simp at hside)
  have hbeta : 0 < |beta| := abs_pos.mpr (by rintro rfl; simp at hside)
  set t := alpha * eta / beta with ht
  have htabs : t = alpha * |eta| / |beta| := amp_sq_eq_abs alpha beta eta hside
  have hsle : s ≤ Real.sqrt (2 * t) := by
    calc s = Real.sqrt (s ^ 2) := (Real.sqrt_sq hs.le).symm
      _ ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt hs2
  have hcube : s ^ 3 ≤ |eta| * (2 * alpha * Real.sqrt (2 * t) / |beta|) := by
    have h2t : 2 * t = |eta| * (2 * alpha / |beta|) := by rw [htabs]; ring
    have hpos : 0 ≤ s ^ 2 := sq_nonneg s
    calc s ^ 3 = s * s ^ 2 := by ring
      _ ≤ Real.sqrt (2 * t) * (2 * t) :=
        mul_le_mul hsle hs2 hpos (Real.sqrt_nonneg _)
      _ = |eta| * (2 * alpha * Real.sqrt (2 * t) / |beta|) := by rw [h2t]; ring
  have hmid : s ^ 2 * |eta| ≤ |eta| * (2 * t) := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hs2 heta.le
  have hin : eta ^ 2 + s ^ 2 * |eta| + s ^ 3 ≤
      |eta| * (|eta| + 2 * t + 2 * alpha * Real.sqrt (2 * t) / |beta|) := by
    have : eta ^ 2 = |eta| * |eta| := by rw [← sq_abs eta]; ring
    nlinarith
  have habs : |s| = s := abs_of_pos hs
  have hfac : |s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4 =
      s * (eta ^ 2 + s ^ 2 * |eta| + s ^ 3) := by rw [habs]; ring
  rw [hfac] at hR
  have hlt : C * (|eta| * (|eta| + 2 * t + 2 * alpha * Real.sqrt (2 * t) / |beta|)) <
      alpha / 2 * |eta| := by
    have := mul_lt_mul_of_pos_left hsmall heta
    nlinarith
  calc
    |R| ≤ C * (s * (eta ^ 2 + s ^ 2 * |eta| + s ^ 3)) := hR
    _ = s * (C * (eta ^ 2 + s ^ 2 * |eta| + s ^ 3)) := by ring
    _ ≤ s * (C * (|eta| * (|eta| + 2 * t + 2 * alpha * Real.sqrt (2 * t) / |beta|))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin hC) hs.le
    _ < s * (alpha / 2 * |eta|) := mul_lt_mul_of_pos_left hlt hs

/-- Existence of a positive nontrivial equilibrium on the side `η β > 0`, with
`s² ∈ [α η / (2 β), 2 α η / β]`. Only continuity of the remainder in `s` and
the weak value bound on the amplitude window are used. -/
theorem exists_pos_equilibrium (alpha beta eta C : ℝ) (R : ℝ → ℝ)
    (halpha : 0 < alpha) (hside : 0 < eta * beta) (hC : 0 ≤ C)
    (hcont : ContinuousOn R
      (Set.Icc (Real.sqrt (alpha * eta / beta / 2)) (Real.sqrt (2 * (alpha * eta / beta)))))
    (hR : ∀ s, 0 < s → s ^ 2 ≤ 2 * (alpha * eta / beta) →
      |R s| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4))
    (hsmall : C * (|eta| + 2 * (alpha * eta / beta) +
        2 * alpha * Real.sqrt (2 * (alpha * eta / beta)) / |beta|) < alpha / 2) :
    ∃ s, 0 < s ∧ alpha * eta / beta / 2 ≤ s ^ 2 ∧ s ^ 2 ≤ 2 * (alpha * eta / beta) ∧
      alpha * eta * s - beta * s ^ 3 + R s = 0 := by
  have hbeta : beta ≠ 0 := by rintro rfl; simp at hside
  have heta0 : eta ≠ 0 := by rintro rfl; simp at hside
  have ht : 0 < alpha * eta / beta := amplitude_sq_pos alpha beta eta halpha hside
  set t := alpha * eta / beta with htdef
  have hbt : beta * t = alpha * eta := by rw [htdef]; field_simp
  set s1 := Real.sqrt (t / 2) with hs1def
  set s2 := Real.sqrt (2 * t) with hs2def
  have hs1pos : 0 < s1 := Real.sqrt_pos.mpr (by positivity)
  have hs2pos : 0 < s2 := Real.sqrt_pos.mpr (by positivity)
  have hs1sq : s1 ^ 2 = t / 2 := Real.sq_sqrt (by positivity)
  have hs2sq : s2 ^ 2 = 2 * t := Real.sq_sqrt (by positivity)
  have hs12 : s1 ≤ s2 := Real.sqrt_le_sqrt (by linarith)
  set f : ℝ → ℝ := fun s => alpha * eta * s - beta * s ^ 3 + R s with hfdef
  set k : ℝ → ℝ := fun s => -(eta * f s) with hkdef
  have hR1 := weak_value_lt_on_window alpha beta eta s1 (R s1) C hside hC hs1pos
    (by rw [hs1sq]; linarith) (hR s1 hs1pos (by rw [hs1sq]; linarith)) hsmall
  have hR2 := weak_value_lt_on_window alpha beta eta s2 (R s2) C hside hC hs2pos
    (le_of_eq hs2sq) (hR s2 hs2pos (le_of_eq hs2sq)) hsmall
  have he2 : 0 < eta ^ 2 := by positivity
  have hetaR (x : ℝ) : |eta * R x| = |eta| * |R x| := abs_mul _ _
  have hf1 : f s1 = s1 * (alpha * eta / 2) + R s1 := by
    simp only [hfdef]
    have : s1 ^ 3 = s1 * (t / 2) := by rw [← hs1sq]; ring
    rw [this]; linear_combination (-s1 / 2) * hbt
  have hf2 : f s2 = -(s2 * (alpha * eta)) + R s2 := by
    simp only [hfdef]
    have : s2 ^ 3 = s2 * (2 * t) := by rw [← hs2sq]; ring
    rw [this]; linear_combination (-2 * s2) * hbt
  have habs_eta : |eta| * |eta| = eta ^ 2 := by rw [← sq_abs eta]; ring
  have hk1 : k s1 < 0 := by
    simp only [hkdef]
    rw [hf1]
    have hlt : |eta| * |R s1| < |eta| * (s1 * (alpha / 2 * |eta|)) :=
      mul_lt_mul_of_pos_left hR1 (abs_pos.mpr heta0)
    have hneg := neg_abs_le (eta * R s1)
    nlinarith [mul_pos hs1pos (mul_pos halpha he2), hetaR s1]
  have hk2 : 0 < k s2 := by
    simp only [hkdef]
    rw [hf2]
    have hlt : |eta| * |R s2| < |eta| * (s2 * (alpha / 2 * |eta|)) :=
      mul_lt_mul_of_pos_left hR2 (abs_pos.mpr heta0)
    have hle := le_abs_self (eta * R s2)
    nlinarith [mul_pos hs2pos (mul_pos halpha he2), hetaR s2]
  have hkcont : ContinuousOn k (Set.Icc s1 s2) := by
    have hpoly : Continuous fun s : ℝ => alpha * eta * s - beta * s ^ 3 := by fun_prop
    have hfc : ContinuousOn f (Set.Icc s1 s2) := hpoly.continuousOn.add hcont
    exact (continuousOn_const.mul hfc).neg
  obtain ⟨s, hsI, hks⟩ := intermediate_value_Icc hs12 hkcont ⟨hk1.le, hk2.le⟩
  have hfs : f s = 0 := by
    have : eta * f s = 0 := by simpa [hkdef] using hks
    exact (mul_eq_zero.mp this).resolve_left heta0
  have hspos : 0 < s := hs1pos.trans_le hsI.1
  refine ⟨s, hspos, ?_, ?_, hfs⟩
  · rw [← hs1sq]; exact pow_le_pow_left₀ hs1pos.le hsI.1 2
  · rw [← hs2sq]; exact pow_le_pow_left₀ hspos.le hsI.2 2

/-! ## Branch conclusions along `χ̃ → 0` -/

/-- The reduced vector field `α η s - β s³ + R(η, s)` on the center manifold. -/
def reducedField (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (eta s : ℝ) : ℝ :=
  alpha * eta * s - beta * s ^ 3 + R eta s

theorem reducedField_hasDerivAt (alpha beta : ℝ) (R Rs : ℝ → ℝ → ℝ) (eta s : ℝ)
    (hd : HasDerivAt (R eta) (Rs eta s) s) :
    HasDerivAt (reducedField alpha beta R eta)
      (alpha * eta - 3 * beta * s ^ 2 + Rs eta s) s := by
  have hlin : HasDerivAt (fun x : ℝ => alpha * eta * x) (alpha * eta) s := by
    simpa using (hasDerivAt_id s).const_mul (alpha * eta)
  have hcub : HasDerivAt (fun x : ℝ => beta * x ^ 3) (3 * beta * s ^ 2) s := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id s).pow 3).const_mul beta
  exact (hlin.sub hcub).add hd

/-- The smallness conditions used for one parameter value `η`. -/
def BranchSmall (alpha beta C r eta : ℝ) : Prop :=
  |eta| ≤ r ∧ 2 * C * |eta| ≤ alpha ∧ 2 * (alpha * eta / beta) ≤ r ^ 2 ∧
    C * (|eta| + 2 * (alpha * eta / beta) +
      2 * alpha * Real.sqrt (2 * (alpha * eta / beta)) / |beta|) < alpha / 2 ∧
    absorbedConst alpha beta C * (|eta| + Real.sqrt (2 * (alpha * eta / beta))) ≤ |beta| / 2

/-- All smallness conditions hold for every `η` near `0`; the hypotheses of
the branch theorem are therefore not vacuous. -/
theorem branchSmall_eventually (alpha beta C r : ℝ) (halpha : 0 < alpha) (hbeta : beta ≠ 0)
    (hr : 0 < r) :
    ∀ᶠ eta in 𝓝 (0 : ℝ), BranchSmall alpha beta C r eta := by
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have hc1 : Continuous fun eta : ℝ => |eta| := by fun_prop
  have hc2 : Continuous fun eta : ℝ => 2 * C * |eta| := by fun_prop
  have hc3 : Continuous fun eta : ℝ => 2 * (alpha * eta / beta) := by fun_prop
  have hsq : Continuous fun eta : ℝ => Real.sqrt (2 * (alpha * eta / beta)) :=
    Real.continuous_sqrt.comp hc3
  have hc4 : Continuous fun eta : ℝ => C * (|eta| + 2 * (alpha * eta / beta) +
      2 * alpha * Real.sqrt (2 * (alpha * eta / beta)) / |beta|) := by
    exact continuous_const.mul ((hc1.add hc3).add
      ((continuous_const.mul hsq).div_const _))
  have hc5 : Continuous fun eta : ℝ =>
      absorbedConst alpha beta C * (|eta| + Real.sqrt (2 * (alpha * eta / beta))) :=
    continuous_const.mul (hc1.add hsq)
  have e1 := (hc1.continuousAt (x := (0 : ℝ))).eventually_lt (continuousAt_const (y := r))
    (by simpa using hr)
  have e2 := (hc2.continuousAt (x := (0 : ℝ))).eventually_lt (continuousAt_const (y := alpha))
    (by simpa using halpha)
  have e3 := (hc3.continuousAt (x := (0 : ℝ))).eventually_lt (continuousAt_const (y := r ^ 2))
    (by simpa using pow_pos hr 2)
  have e4 := (hc4.continuousAt (x := (0 : ℝ))).eventually_lt (continuousAt_const (y := alpha / 2))
    (by simpa using half_pos halpha)
  have e5 := (hc5.continuousAt (x := (0 : ℝ))).eventually_lt (continuousAt_const (y := |beta| / 2))
    (by simpa using half_pos hb)
  filter_upwards [e1, e2, e3, e4, e5] with eta h1 h2 h3 h4 h5
  exact ⟨h1.le, h2.le, h3.le, h4, h5.le⟩

/-- Scalar Step 5 conclusions at one admissible `η` on the side `η β > 0`:
a positive and a negative nontrivial equilibrium, each with the square-root
amplitude up to `O(|η|)` and with `(∂ₛ field) · β < 0`. -/
theorem mixed_branch_at (alpha beta C r eta : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (hsmall : BranchSmall alpha beta C r eta) (hside : 0 < eta * beta) :
    ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ s, 0 < sgn * s ∧
      reducedField alpha beta R eta s = 0 ∧
      abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
        (2 * alpha * absorbedConst alpha beta C *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| ∧
      deriv (reducedField alpha beta R eta) s * beta < 0 := by
  obtain ⟨hetar, hetaC, h2t, hwin, hrect⟩ := hsmall
  intro sgn hsgn
  have hsgn2 : sgn * sgn = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsgnabs : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  set t := alpha * eta / beta with htdef
  -- the remainder seen in the coordinate `x = sgn * s`
  set R' : ℝ → ℝ := fun x => sgn * R eta (sgn * x) with hR'def
  have hwin_le (x : ℝ) (hx : 0 < x) (hx2 : x ^ 2 ≤ 2 * t) : |sgn * x| ≤ r := by
    rw [abs_mul, hsgnabs, one_mul, abs_of_pos hx]
    nlinarith
  have hR'b : ∀ x, 0 < x → x ^ 2 ≤ 2 * t →
      |R' x| ≤ C * (|x| * eta ^ 2 + |x| ^ 3 * |eta| + x ^ 4) := by
    intro x hx hx2
    have h := hRval eta (sgn * x) hetar (hwin_le x hx hx2)
    have hx4 : (sgn * x) ^ 4 = x ^ 4 := by
      rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq sgn, hsgn2]; ring
    rw [abs_mul, hsgnabs, one_mul] at h ⊢
    rwa [hx4] at h
  have hR'c : ContinuousOn R' (Set.Icc (Real.sqrt (t / 2)) (Real.sqrt (2 * t))) := by
    intro x hx
    have hx0 : 0 < x := (Real.sqrt_pos.mpr (by
      have := amplitude_sq_pos alpha beta eta halpha hside; positivity)).trans_le hx.1
    have hx2 : x ^ 2 ≤ 2 * t := by
      have h2 : 0 ≤ 2 * t := by
        have := amplitude_sq_pos alpha beta eta halpha hside; positivity
      calc x ^ 2 ≤ Real.sqrt (2 * t) ^ 2 := pow_le_pow_left₀ hx0.le hx.2 2
        _ = 2 * t := Real.sq_sqrt h2
    have hca : ContinuousAt (R eta) (sgn * x) :=
      (hRder eta (sgn * x) hetar (hwin_le x hx0 hx2)).continuousAt
    have : ContinuousAt R' x :=
      continuousAt_const.mul (hca.comp (continuousAt_const.mul continuousAt_id))
    exact this.continuousWithinAt
  obtain ⟨x, hx0, -, hx2, hxroot⟩ :=
    exists_pos_equilibrium alpha beta eta C R' halpha hside hC hR'c hR'b hwin
  refine ⟨sgn * x, by rw [← mul_assoc, hsgn2, one_mul]; exact hx0, ?_, ?_⟩
  · -- the root in the original coordinate
    have hfield : reducedField alpha beta R eta (sgn * x) =
        sgn * (alpha * eta * x - beta * x ^ 3 + R' x) := by
      simp only [reducedField, hR'def]
      have h3 : (sgn * x) ^ 3 = sgn * x ^ 3 := by
        rw [mul_pow, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq sgn, hsgn2]; ring
      rw [h3]
      linear_combination (-(R eta (sgn * x))) * hsgn2
    rw [hfield, hxroot, mul_zero]
  · set s := sgn * x with hsdef
    have hs0 : s ≠ 0 := by
      rw [hsdef]; exact mul_ne_zero (by rcases hsgn with rfl | rfl <;> norm_num) hx0.ne'
    have hsabs : |s| = x := by rw [hsdef, abs_mul, hsgnabs, one_mul, abs_of_pos hx0]
    have hsr : |s| ≤ r := hwin_le x hx0 hx2
    have hs1 : |s| ≤ 1 := hsr.trans hr1
    have hroot : alpha * eta * s - beta * s ^ 3 + R eta s = 0 := by
      have hfield : reducedField alpha beta R eta s = 0 := by
        simp only [reducedField, hsdef, hR'def] at hxroot ⊢
        have h3 : (sgn * x) ^ 3 = sgn * x ^ 3 := by
          rw [mul_pow, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq sgn, hsgn2]; ring
        rw [h3]
        linear_combination sgn * hxroot + (-(R eta (sgn * x))) * hsgn2
      simpa [reducedField] using hfield
    have hd := reducedField_hasDerivAt alpha beta R Rs eta s (hRder eta s hetar hsr)
    have hsx : |s| ≤ Real.sqrt (2 * t) := by
      rw [hsabs]
      calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx0.le).symm
        _ ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt hx2
    have hK := absorbedConst_nonneg alpha beta C halpha hC
    have hrect' : absorbedConst alpha beta C * (|eta| + |s|) ≤ |beta| / 2 :=
      (mul_le_mul_of_nonneg_left (by linarith) hK).trans hrect
    obtain ⟨-, hsign, hamp⟩ := mixed_equilibrium_core alpha beta eta s (R eta s) (Rs eta s)
      (deriv (reducedField alpha beta R eta) s) C halpha hbeta hs0 hC hs1 (hetar.trans hr1) hetaC
      hroot hd.deriv (hRval eta s hetar hsr) (hRs eta s hetar hsr) hrect'
    exact ⟨hamp, hsign⟩

/-- Theorem 1.1 part 1 / Remark 1.1 / Step 5, scalar core under the weak mixed
remainder, along `χ̃ → 0`: for all small `η` on the side `η β > 0` there are
nontrivial equilibria of both signs with amplitude `√(α η / β) + O(|η|)` and
`(∂ₛ field) · β < 0`. -/
theorem mixed_branch_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) :
    ∀ᶠ eta in 𝓝 (0 : ℝ), 0 < eta * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ s, 0 < sgn * s ∧
        reducedField alpha beta R eta s = 0 ∧
        abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
          (2 * alpha * absorbedConst alpha beta C *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| ∧
        deriv (reducedField alpha beta R eta) s * beta < 0 := by
  filter_upwards [branchSmall_eventually alpha beta C r halpha hbeta hr] with eta hsmall hside
  exact mixed_branch_at alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs hsmall
    hside

/-- Side condition (Step 5, `β_{n₀} χ̃ > 0`): near `(η, s) = (0, 0)` every
nontrivial equilibrium of the reduced field lies on the side `η β > 0`, and
its derivative has sign opposite to `β`. -/
theorem mixed_side_condition_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), p.2 ≠ 0 →
      reducedField alpha beta R p.1 p.2 = 0 →
        0 < p.1 * beta ∧ deriv (reducedField alpha beta R p.1) p.2 * beta < 0 := by
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have c1 : Continuous fun p : ℝ × ℝ => |p.1| := by fun_prop
  have c2 : Continuous fun p : ℝ × ℝ => |p.2| := by fun_prop
  have c3 : Continuous fun p : ℝ × ℝ => 2 * C * |p.1| := by fun_prop
  have c4 : Continuous fun p : ℝ × ℝ => absorbedConst alpha beta C * (|p.1| + |p.2|) := by
    fun_prop
  have e1 := (c1.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).eventually_lt
    (continuousAt_const (y := r)) (by simpa using hr)
  have e2 := (c2.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).eventually_lt
    (continuousAt_const (y := r)) (by simpa using hr)
  have e3 := (c3.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).eventually_lt
    (continuousAt_const (y := alpha))
    (by simpa using halpha)
  have e4 := (c4.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).eventually_lt
    (continuousAt_const (y := |beta| / 2))
    (by simpa using half_pos hb)
  filter_upwards [e1, e2, e3, e4] with p h1 h2 h3 h4 hs0 hroot
  have hd := reducedField_hasDerivAt alpha beta R Rs p.1 p.2 (hRder p.1 p.2 h1.le h2.le)
  obtain ⟨hside, hsign, -⟩ := mixed_equilibrium_core alpha beta p.1 p.2 (R p.1 p.2)
    (Rs p.1 p.2) (deriv (reducedField alpha beta R p.1) p.2) C halpha hbeta hs0 hC
    (h2.le.trans hr1) (h1.le.trans hr1) h3.le (by simpa [reducedField] using hroot) hd.deriv
    (hRval p.1 p.2 h1.le h2.le) (hRs p.1 p.2 h1.le h2.le) h4.le
  exact ⟨hside, hsign⟩

/-- The branch theorem from the Eq. 2.43 bounds (`u² χ̃²` in the value and
`|u| χ̃²` in the derivative), through the weak interface. -/
theorem center_ODE_final_branch_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) :
    ∀ᶠ eta in 𝓝 (0 : ℝ), 0 < eta * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ s, 0 < sgn * s ∧
        reducedField alpha beta R eta s = 0 ∧
        abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
          (2 * alpha * absorbedConst alpha beta C *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| ∧
        deriv (reducedField alpha beta R eta) s * beta < 0 :=
  mixed_branch_eventually alpha beta C r R Rs halpha hbeta hC hr hr1
    (fun e s he hs => center_ODE_final_value_bound_weak e s (R e s) C hC (hs.trans hr1)
      (hRval e s he hs))
    hRder
    (fun e s he hs => center_ODE_final_deriv_bound_weak e s (Rs e s) C hC (hs.trans hr1)
      (hRs e s he hs))

end ChemotaxisBifurcation.MixedRemainder
