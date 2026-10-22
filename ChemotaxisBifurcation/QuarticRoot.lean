module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# Unique roots of a real quartic on a closed interval

This module gives a Mathlib-only certificate for a unique real root of the
quartic `a x^4 + b x^3 + c x^2 + d x + e` on a closed interval `[lo, hi]`.
It replaces the external interval-arithmetic tactic that the root tables used
before (route C, 2026-10-17).

The certificate `existsUnique_root` has two hypotheses besides `lo ≤ hi`:

* a sign change, `q lo * q hi < 0`, which gives a root by the intermediate
  value theorem;
* a derivative bound: the third-order Taylor expansion of `q'` at `lo`, with
  its coefficients replaced by absolute values and `x - lo` by the width
  `hi - lo`, is smaller than `|q' lo|`.  Then `q'` has no zero and keeps one
  sign on `[lo, hi]`, so `q` is strictly monotone there and the root is unique.

For rational `a, …, e, lo, hi` both hypotheses are closed rational
inequalities, which `norm_num` decides.  The proofs use only Mathlib: no
compiled-code evaluation (`Lean.ofReduceBool`) and no external certificate
checker.
-/

@[expose] public section

namespace ChemotaxisBifurcation.QuarticRoot

/-- The quartic `a x^4 + b x^3 + c x^2 + d x + e`. -/
def q (a b c d e x : ℝ) : ℝ := a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e

/-- The derivative of `q` with respect to `x`. -/
def q' (a b c d x : ℝ) : ℝ := 4 * a * x ^ 3 + 3 * b * x ^ 2 + 2 * c * x + d

theorem hasDerivAt_q (a b c d e x : ℝ) :
    HasDerivAt (q a b c d e) (q' a b c d x) x := by
  unfold q q'
  have h := ((((hasDerivAt_pow 4 x).const_mul a).add
    ((hasDerivAt_pow 3 x).const_mul b)).add
    ((hasDerivAt_pow 2 x).const_mul c)).add ((hasDerivAt_id x).const_mul d)
    |>.add_const e
  convert h using 1
  · funext y; simp
  · simp; ring

/-- Taylor bound for the derivative: on `[lo, hi]`, `q'` stays within
`w*|g2| + w^2*|g3| + w^3*|g4|` of `q' lo`, where `w = hi - lo` and
`g2, g3, g4` are the Taylor coefficients of `q'` at `lo`. -/
theorem q'_close (a b c d lo hi x : ℝ) (hx : x ∈ Set.Icc lo hi) :
    |q' a b c d x - q' a b c d lo| ≤
      (hi - lo) * |12 * a * lo ^ 2 + 6 * b * lo + 2 * c| +
      (hi - lo) ^ 2 * |12 * a * lo + 3 * b| + (hi - lo) ^ 3 * |4 * a| := by
  obtain ⟨h1, h2⟩ := hx
  set t := x - lo with ht
  have ht0 : 0 ≤ t := by linarith
  have htw : t ≤ hi - lo := by linarith
  have hx' : x = lo + t := by linarith
  have key : q' a b c d x - q' a b c d lo =
      t * (12 * a * lo ^ 2 + 6 * b * lo + 2 * c) + t ^ 2 * (12 * a * lo + 3 * b) +
        t ^ 3 * (4 * a) := by
    rw [hx']; unfold q'; ring
  rw [key]
  calc |t * (12 * a * lo ^ 2 + 6 * b * lo + 2 * c) + t ^ 2 * (12 * a * lo + 3 * b) +
        t ^ 3 * (4 * a)|
      ≤ |t * (12 * a * lo ^ 2 + 6 * b * lo + 2 * c)| + |t ^ 2 * (12 * a * lo + 3 * b)| +
          |t ^ 3 * (4 * a)| := abs_add_three _ _ _
    _ = t * |12 * a * lo ^ 2 + 6 * b * lo + 2 * c| + t ^ 2 * |12 * a * lo + 3 * b| +
          t ^ 3 * |4 * a| := by
        have e1 : |t| = t := abs_of_nonneg ht0
        have e2 : |t ^ 2| = t ^ 2 := abs_of_nonneg (pow_nonneg ht0 2)
        have e3 : |t ^ 3| = t ^ 3 := abs_of_nonneg (pow_nonneg ht0 3)
        simp only [abs_mul, e1, e2, e3]
    _ ≤ _ := by
        gcongr

/-- **Unique root of a quartic on a closed interval.**  A sign change of `q`
across `[lo, hi]` gives a root (intermediate value theorem); the derivative
bound `hder` keeps `q'` away from zero on `[lo, hi]`, so `q` is strictly
monotone there and the root is unique.  For rational data every hypothesis is
a closed rational inequality that `norm_num` decides. -/
theorem existsUnique_root (a b c d e lo hi : ℝ) (hlh : lo ≤ hi)
    (hsign : q a b c d e lo * q a b c d e hi < 0)
    (hder : (hi - lo) * |12 * a * lo ^ 2 + 6 * b * lo + 2 * c| +
      (hi - lo) ^ 2 * |12 * a * lo + 3 * b| + (hi - lo) ^ 3 * |4 * a| <
        |q' a b c d lo|) :
    ∃! x : ℝ, x ∈ Set.Icc lo hi ∧ q a b c d e x = 0 := by
  have hcont : Continuous (q a b c d e) := by unfold q; fun_prop
  -- The derivative has no zero and keeps the sign of `q' lo` on `[lo, hi]`.
  have hne : ∀ x ∈ Set.Icc lo hi, q' a b c d x ≠ 0 ∧
      (0 < q' a b c d x ↔ 0 < q' a b c d lo) := by
    intro x hx
    have hlt := lt_of_le_of_lt (q'_close a b c d lo hi x hx) hder
    have hlo : q' a b c d lo ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hlt
      linarith [abs_nonneg (q' a b c d x - 0)]
    rcases lt_or_gt_of_ne hlo with h | h
    · rw [abs_of_neg h] at hlt
      have hb := (abs_lt.mp hlt).2
      have hx0 : q' a b c d x < 0 := by linarith
      exact ⟨hx0.ne, ⟨fun h' => absurd h' (not_lt.mpr hx0.le),
        fun h' => absurd h' (not_lt.mpr h.le)⟩⟩
    · rw [abs_of_pos h] at hlt
      have hb := (abs_lt.mp hlt).1
      have hx0 : 0 < q' a b c d x := by linarith
      exact ⟨hx0.ne', ⟨fun _ => h, fun _ => hx0⟩⟩
  -- Strict monotonicity or antitonicity gives injectivity on `[lo, hi]`.
  have hinj : Set.InjOn (q a b c d e) (Set.Icc lo hi) := by
    by_cases hpos : 0 < q' a b c d lo
    · apply StrictMonoOn.injOn
      apply strictMonoOn_of_deriv_pos (convex_Icc lo hi) hcont.continuousOn
      intro x hx
      rw [(hasDerivAt_q a b c d e x).deriv]
      exact ((hne x (interior_subset hx)).2).2 hpos
    · apply StrictAntiOn.injOn
      apply strictAntiOn_of_deriv_neg (convex_Icc lo hi) hcont.continuousOn
      intro x hx
      rw [(hasDerivAt_q a b c d e x).deriv]
      have h1 := (hne x (interior_subset hx)).1
      have h2 := (hne x (interior_subset hx)).2
      rcases lt_or_gt_of_ne h1 with h | h
      · exact h
      · exact absurd (h2.1 h) hpos
  -- Existence by the intermediate value theorem.
  have hex : ∃ x ∈ Set.Icc lo hi, q a b c d e x = 0 := by
    rcases mul_neg_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact intermediate_value_Icc' hlh hcont.continuousOn ⟨h2.le, h1.le⟩
    · exact intermediate_value_Icc hlh hcont.continuousOn ⟨h1.le, h2.le⟩
  obtain ⟨x, hx, hx0⟩ := hex
  exact ⟨x, ⟨hx, hx0⟩, fun y ⟨hy, hy0⟩ => hinj hy hx (hy0.trans hx0.symm)⟩

end ChemotaxisBifurcation.QuarticRoot
