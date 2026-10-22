module

public import ChemotaxisBifurcation.RootTableRemaining
public import Mathlib.Analysis.Convex.Deriv

/-!
# Exact two-root exhaustion for the beta=1 and beta=3 rows

The two roots in each row are supplied by the kernel-checked interval
certificates.  This module proves that no third real root exists.
-/

@[expose] public section

namespace ChemotaxisBifurcation.TwoRootExhaustion

open Set
open ChemotaxisBifurcation.SpecializedPolynomial
open ChemotaxisBifurcation.RootTableRemaining

noncomputable section

def f1 (x : ℝ) : ℝ := numerator x 1
def f3 (x : ℝ) : ℝ := numerator x 3

theorem f1_eq (x : ℝ) :
    f1 x = 128 * x ^ 4 + 40 * x ^ 3 - 112 * x ^ 2 + 60 * x + 66 := by
  norm_num [f1, numerator]
  ring

theorem f3_eq (x : ℝ) :
    f3 x = -64 * x ^ 4 - 264 * x ^ 3 - 448 * x ^ 2 - 60 * x + 80 := by
  norm_num [f3, numerator]
  ring

private def g1 (x : ℝ) : ℝ :=
  x * 60 - x ^ 2 * 112 + x ^ 3 * 40 + x ^ 4 * 128

private def g1d (x : ℝ) : ℝ :=
  60 - x * 224 + x ^ 2 * 120 + x ^ 3 * 512

private theorem g1_hasDerivAt (x : ℝ) :
    HasDerivAt g1 (g1d x) x := by
  unfold g1 g1d
  convert ((((hasDerivAt_id x).mul_const 60).sub
    (((hasDerivAt_id x).pow 2).mul_const 112)).add
    (((hasDerivAt_id x).pow 3).mul_const 40)).add
    (((hasDerivAt_id x).pow 4).mul_const 128) using 1
  all_goals try simp only [id_eq]
  all_goals norm_num
  all_goals first | rfl | ring

private theorem g1d_hasDerivAt (x : ℝ) :
    HasDerivAt g1d (1536 * x ^ 2 + 240 * x - 224) x := by
  unfold g1d
  convert ((((hasDerivAt_const x 60).sub
    ((hasDerivAt_id x).mul_const 224)).add
    (((hasDerivAt_id x).pow 2).mul_const 120)).add
    (((hasDerivAt_id x).pow 3).mul_const 512)) using 1
  all_goals try simp only [id_eq]
  all_goals norm_num
  all_goals first | rfl | ring

private def g3 (x : ℝ) : ℝ :=
  -(x * 60) - x ^ 2 * 448 - x ^ 3 * 264 - x ^ 4 * 64

private def g3d (x : ℝ) : ℝ :=
  -60 - x * 896 - x ^ 2 * 792 - x ^ 3 * 256

private theorem g3_hasDerivAt (x : ℝ) :
    HasDerivAt g3 (g3d x) x := by
  unfold g3 g3d
  convert (((((hasDerivAt_id x).mul_const 60).neg.sub
    (((hasDerivAt_id x).pow 2).mul_const 448)).sub
    (((hasDerivAt_id x).pow 3).mul_const 264)).sub
    (((hasDerivAt_id x).pow 4).mul_const 64)) using 1
  all_goals try simp only [id_eq]
  all_goals norm_num
  all_goals first | rfl | ring

private theorem g3d_hasDerivAt (x : ℝ) :
    HasDerivAt g3d (-768 * x ^ 2 - 1584 * x - 896) x := by
  unfold g3d
  convert ((((hasDerivAt_const x (-60)).sub
    ((hasDerivAt_id x).mul_const 896)).sub
    (((hasDerivAt_id x).pow 2).mul_const 792)).sub
    (((hasDerivAt_id x).pow 3).mul_const 256)) using 1
  all_goals try simp only [id_eq]
  all_goals norm_num
  all_goals first | rfl | ring

theorem f1_deriv2 (x : ℝ) :
    (deriv^[2] f1) x = 1536 * x ^ 2 + 240 * x - 224 := by
  have hf : f1 = fun y : ℝ => g1 y + 66 := by
    funext y
    rw [f1_eq]
    unfold g1
    ring
  have hd : deriv (fun y : ℝ => g1 y + 66) = g1d := by
    funext y
    exact ((g1_hasDerivAt y).add_const 66).deriv
  simp only [Function.iterate_succ_apply, hf, hd]
  exact (g1d_hasDerivAt x).deriv

theorem f3_deriv2 (x : ℝ) :
    (deriv^[2] f3) x = -768 * x ^ 2 - 1584 * x - 896 := by
  have hf : f3 = fun y : ℝ => g3 y + 80 := by
    funext y
    rw [f3_eq]
    unfold g3
    ring
  have hd : deriv (fun y : ℝ => g3 y + 80) = g3d := by
    funext y
    exact ((g3_hasDerivAt y).add_const 80).deriv
  simp only [Function.iterate_succ_apply, hf, hd]
  exact (g3d_hasDerivAt x).deriv

theorem f1_continuous : Continuous f1 := by
  unfold f1 numerator
  fun_prop

theorem f3_continuous : Continuous f3 := by
  unfold f3 numerator
  fun_prop

theorem f1_pos_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 < f1 x := by
  rw [f1_eq]
  have hsq : 0 ≤ (x ^ 2 - 1 / 2 : ℝ) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ x ^ 3 := by positivity
  have h2 : 0 ≤ x ^ 2 := sq_nonneg _
  nlinarith

theorem f1_pos_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (-1 / 2 : ℝ) 0) :
    0 < f1 x := by
  rcases hx with ⟨hxlo, hxhi⟩
  rw [f1_eq]
  have hcube : 0 ≤ x ^ 2 * (x + 1 / 2) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hsquare : 0 ≤ (-x) * (x + 1 / 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem f1_pos_of_neg_half_le {x : ℝ} (hx : -1 / 2 ≤ x) : 0 < f1 x := by
  by_cases hx0 : 0 ≤ x
  · exact f1_pos_of_nonneg hx0
  · exact f1_pos_of_mem_Icc ⟨hx, le_of_not_ge hx0⟩

theorem f1_deriv2_pos_of_mem_Iic {x : ℝ} (hx : x ∈ Iic (-1 / 2 : ℝ)) :
    0 < (deriv^[2] f1) x := by
  change x ≤ -1 / 2 at hx
  rw [f1_deriv2]
  have hsquare : 0 ≤ (x + 1 / 2) ^ 2 := sq_nonneg _
  nlinarith

theorem f3_deriv2_neg (x : ℝ) : (deriv^[2] f3) x < 0 := by
  rw [f3_deriv2]
  have hsquare : 0 ≤ (x + 33 / 32) ^ 2 := sq_nonneg _
  nlinarith

theorem f1_strictConvex : StrictConvexOn ℝ (Iic (-1 / 2 : ℝ)) f1 :=
  strictConvexOn_of_deriv2_pos' (convex_Iic _) f1_continuous.continuousOn
    fun x hx => f1_deriv2_pos_of_mem_Iic hx

theorem f3_strictConcave : StrictConcaveOn ℝ univ f3 :=
  strictConcaveOn_univ_of_deriv2_neg f3_continuous f3_deriv2_neg

theorem mem_openSegment_of_lt {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    y ∈ openSegment ℝ x z := by
  rw [mem_openSegment_iff_div]
  refine ⟨z - y, y - x, sub_pos.mpr hyz, sub_pos.mpr hxy, ?_⟩
  dsimp only [smul_eq_mul]
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hxy.trans hyz))
  field_simp [hzx]
  ring

theorem no_three_zeros_of_strictConvexOn
    {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ s f)
    {x y z : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z)
    (hfx : f x = 0) (hfy : f y = 0) (hfz : f z = 0) : False := by
  have hseg := mem_openSegment_of_lt hxy hyz
  have hlt := hf.lt_on_openSegment hx hz (ne_of_lt (hxy.trans hyz)) hseg
  rw [hfx, hfz, max_self, hfy] at hlt
  exact (lt_irrefl 0 hlt)

theorem no_three_zeros_of_strictConcaveOn
    {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ s f)
    {x y z : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z)
    (hfx : f x = 0) (hfy : f y = 0) (hfz : f z = 0) : False := by
  have hseg := mem_openSegment_of_lt hxy hyz
  have hlt := hf.lt_on_openSegment hx hz (ne_of_lt (hxy.trans hyz)) hseg
  rw [hfx, hfz, min_self, hfy] at hlt
  exact (lt_irrefl 0 hlt)

theorem f1_zero_eq_certified_roots :
    ∃ r1 r2 : ℝ,
      r1 ∈ Ioo (-11057955 / 10000000 : ℝ) (-11057945 / 10000000 : ℝ) ∧
      r2 ∈ Ioo (-5815655 / 10000000 : ℝ) (-5815645 / 10000000 : ℝ) ∧
      ∀ x : ℝ, f1 x = 0 ↔ x = r1 ∨ x = r2 := by
  rcases b1r1_root with ⟨r1, ⟨hr1mem, hr1zero⟩, hr1uniq⟩
  rcases b1r2_root with ⟨r2, ⟨hr2mem, hr2zero⟩, hr2uniq⟩
  refine ⟨r1, r2, hr1mem, hr2mem, ?_⟩
  have hr1 : f1 r1 = 0 := by simpa [f1] using hr1zero
  have hr2 : f1 r2 = 0 := by simpa [f1] using hr2zero
  have hr12 : r1 < r2 := by nlinarith [hr1mem.2, hr2mem.1]
  intro x
  constructor
  · intro hx
    have hxleft : x < -1 / 2 := by
      by_contra hnot
      have hpos := f1_pos_of_neg_half_le (le_of_not_gt hnot)
      linarith
    by_cases hx1 : x = r1
    · exact Or.inl hx1
    by_cases hx2 : x = r2
    · exact Or.inr hx2
    rcases lt_or_gt_of_ne hx1 with hxr1 | hr1x
    · exact (no_three_zeros_of_strictConvexOn f1_strictConvex
        (show x ≤ -1 / 2 by linarith)
        (show r1 ≤ -1 / 2 by linarith [hr1mem.2])
        (show r2 ≤ -1 / 2 by linarith [hr2mem.2])
        hxr1 hr12 hx hr1 hr2).elim
    · rcases lt_or_gt_of_ne hx2 with hxr2 | hr2x
      · exact (no_three_zeros_of_strictConvexOn f1_strictConvex
          (show r1 ≤ -1 / 2 by linarith [hr1mem.2])
          (show x ≤ -1 / 2 by linarith)
          (show r2 ≤ -1 / 2 by linarith [hr2mem.2])
          hr1x hxr2 hr1 hx hr2).elim
      · exact (no_three_zeros_of_strictConvexOn f1_strictConvex
          (show r1 ≤ -1 / 2 by linarith [hr1mem.2])
          (show r2 ≤ -1 / 2 by linarith [hr2mem.2])
          (show x ≤ -1 / 2 by linarith)
          hr12 hr2x hr1 hr2 hx).elim
  · rintro (rfl | rfl) <;> assumption

theorem f3_zero_eq_certified_roots :
    ∃ r1 r2 : ℝ,
      r1 ∈ Ioo (-6138385 / 10000000 : ℝ) (-6138375 / 10000000 : ℝ) ∧
      r2 ∈ Ioo (3325745 / 10000000 : ℝ) (3325755 / 10000000 : ℝ) ∧
      ∀ x : ℝ, f3 x = 0 ↔ x = r1 ∨ x = r2 := by
  rcases b3r1_root with ⟨r1, ⟨hr1mem, hr1zero⟩, hr1uniq⟩
  rcases b3r2_root with ⟨r2, ⟨hr2mem, hr2zero⟩, hr2uniq⟩
  refine ⟨r1, r2, hr1mem, hr2mem, ?_⟩
  have hr1 : f3 r1 = 0 := by simpa [f3] using hr1zero
  have hr2 : f3 r2 = 0 := by simpa [f3] using hr2zero
  have hr12 : r1 < r2 := by nlinarith [hr1mem.2, hr2mem.1]
  intro x
  constructor
  · intro hx
    by_cases hx1 : x = r1
    · exact Or.inl hx1
    by_cases hx2 : x = r2
    · exact Or.inr hx2
    rcases lt_or_gt_of_ne hx1 with hxr1 | hr1x
    · exact (no_three_zeros_of_strictConcaveOn f3_strictConcave
        (mem_univ _) (mem_univ _) (mem_univ _) hxr1 hr12 hx hr1 hr2).elim
    · rcases lt_or_gt_of_ne hx2 with hxr2 | hr2x
      · exact (no_three_zeros_of_strictConcaveOn f3_strictConcave
          (mem_univ _) (mem_univ _) (mem_univ _) hr1x hxr2 hr1 hx hr2).elim
      · exact (no_three_zeros_of_strictConcaveOn f3_strictConcave
          (mem_univ _) (mem_univ _) (mem_univ _) hr12 hr2x hr1 hr2 hx).elim
  · rintro (rfl | rfl) <;> assumption

end

end ChemotaxisBifurcation.TwoRootExhaustion

end
