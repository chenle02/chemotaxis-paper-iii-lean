module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib

@[expose] public section

/-!
# Absolutely summable cosine series and interval projections

This file isolates the analytic interchange used by the current infinite
Fourier version of Paper III, Lemma 2.1.  It does not perform the subsequent
integer-constraint reindexing and therefore does not claim the four displayed
convolution formulas.
-/

namespace ChemotaxisBifurcation.InfiniteCosineProjection

open MeasureTheory Set
open scoped Interval

noncomputable section

/-- A coefficient, a uniformly bounded phase, and a bounded kernel. -/
def boundedPhaseTerm {ι : Type*} (c : ι → ℝ) (phase : ι → ℝ → ℝ)
    (kernel : ℝ → ℝ) (i : ι) (x : ℝ) : ℝ :=
  c i * phase i x * kernel x

/-- Absolute coefficient summability controls the pointwise series whenever
the phase has norm at most one and the kernel has a uniform bound. -/
theorem summable_boundedPhaseTerm {ι : Type*} (c : ι → ℝ)
    (phase : ι → ℝ → ℝ) (kernel : ℝ → ℝ) (C : ℝ)
    (hc : Summable fun i => ‖c i‖)
    (hphase : ∀ i x, ‖phase i x‖ ≤ 1)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (_hC : 0 ≤ C) (x : ℝ) :
    Summable fun i => boundedPhaseTerm c phase kernel i x := by
  apply (hc.mul_right C).of_norm_bounded
  intro i
  rw [boundedPhaseTerm, norm_mul, norm_mul]
  calc
    ‖c i‖ * ‖phase i x‖ * ‖kernel x‖ ≤
        (‖c i‖ * 1) * ‖kernel x‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hphase i x) (norm_nonneg _))
        (norm_nonneg _)
    _ ≤ (‖c i‖ * 1) * C :=
      mul_le_mul_of_nonneg_left (hkernel x)
        (mul_nonneg (norm_nonneg _) (by norm_num))
    _ = ‖c i‖ * C := by ring

/-- A dominated-convergence bridge from absolute coefficient summability to
termwise interval integration against a bounded continuous kernel.

The conclusion is a `HasSum`, so consumers retain both summability and the
actual sum rather than merely an equality of default `tsum` values. -/
theorem hasSum_intervalIntegral_boundedPhase {ι : Type*} [Countable ι]
    (a b : ℝ) (c : ι → ℝ) (phase : ι → ℝ → ℝ)
    (kernel : ℝ → ℝ) (C : ℝ)
    (hc : Summable fun i => ‖c i‖)
    (hphase_cont : ∀ i, Continuous (phase i))
    (hphase : ∀ i x, ‖phase i x‖ ≤ 1)
    (hkernel_cont : Continuous kernel)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum
      (fun i => ∫ x in a..b, boundedPhaseTerm c phase kernel i x)
      (∫ x in a..b, ∑' i, boundedPhaseTerm c phase kernel i x) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun i (_x : ℝ) => ‖c i‖ * C)
  · intro i
    exact ((continuous_const.mul (hphase_cont i)).mul
      hkernel_cont).aestronglyMeasurable
  · intro i
    filter_upwards with x
    intro _hx
    rw [boundedPhaseTerm, norm_mul, norm_mul]
    calc
      ‖c i‖ * ‖phase i x‖ * ‖kernel x‖ ≤
          (‖c i‖ * 1) * ‖kernel x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hphase i x) (norm_nonneg _))
          (norm_nonneg _)
      _ ≤ (‖c i‖ * 1) * C :=
        mul_le_mul_of_nonneg_left (hkernel x)
          (mul_nonneg (norm_nonneg _) (by norm_num))
      _ = ‖c i‖ * C := by ring
  · filter_upwards with x
    intro _hx
    exact hc.mul_right C
  · exact intervalIntegrable_const
  · filter_upwards with x
    intro _hx
    exact (summable_boundedPhaseTerm c phase kernel C hc hphase
      hkernel hC x).hasSum

/-- The unnormalized Neumann cosine phase used in the manuscript. -/
def cosinePhase (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos ((n : ℝ) * Real.pi * x / L)

theorem continuous_cosinePhase (L : ℝ) (n : ℕ) :
    Continuous (cosinePhase L n) := by
  unfold cosinePhase
  fun_prop

theorem norm_cosinePhase_le_one (L : ℝ) (n : ℕ) (x : ℝ) :
    ‖cosinePhase L n x‖ ≤ 1 := by
  simpa only [cosinePhase, Real.norm_eq_abs] using
    Real.abs_cos_le_one ((n : ℝ) * Real.pi * x / L)

/-- The one-series termwise-integration bridge needed by the first identity
of the current Lemma 2.1. The trigonometric kernel may, for example, be the
product of the two fixed sine modes. -/
theorem hasSum_intervalIntegral_cosine (a b L : ℝ) (u : ℕ → ℝ)
    (kernel : ℝ → ℝ) (C : ℝ)
    (hu : Summable fun n => ‖u n‖)
    (hkernel_cont : Continuous kernel)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum
      (fun n => ∫ x in a..b,
        u n * cosinePhase L n x * kernel x)
      (∫ x in a..b, ∑' n,
        u n * cosinePhase L n x * kernel x) := by
  simpa only [boundedPhaseTerm] using
    hasSum_intervalIntegral_boundedPhase a b u (cosinePhase L)
      kernel C hu (continuous_cosinePhase L)
      (norm_cosinePhase_le_one L) hkernel_cont hkernel hC

/-- Product coefficients of two absolutely summable sequences are absolutely
summable on the product index. -/
theorem summable_norm_pairCoefficient (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖)
    (hv : Summable fun j => ‖v j‖) :
    Summable fun p : ℕ × ℕ => ‖u p.1 * v p.2‖ :=
  hu.mul_norm hv

/-- Product of two cosine phases, indexed before any convolution reindexing. -/
def pairCosinePhase (L : ℝ) (p : ℕ × ℕ) (x : ℝ) : ℝ :=
  cosinePhase L p.1 x * cosinePhase L p.2 x

theorem continuous_pairCosinePhase (L : ℝ) (p : ℕ × ℕ) :
    Continuous (pairCosinePhase L p) :=
  (continuous_cosinePhase L p.1).mul (continuous_cosinePhase L p.2)

theorem norm_pairCosinePhase_le_one (L : ℝ) (p : ℕ × ℕ) (x : ℝ) :
    ‖pairCosinePhase L p x‖ ≤ 1 := by
  rw [pairCosinePhase, norm_mul]
  simpa only [one_mul] using mul_le_mul
    (norm_cosinePhase_le_one L p.1 x)
    (norm_cosinePhase_le_one L p.2 x)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- Pair-series interval interchange. This is the analytic half of the
two-series identities in Lemma 2.1; signed-index collection is deliberately
left to a separate finite/combinatorial layer. -/
theorem hasSum_intervalIntegral_cosinePair (a b L : ℝ)
    (u v : ℕ → ℝ) (kernel : ℝ → ℝ) (C : ℝ)
    (hu : Summable fun i => ‖u i‖)
    (hv : Summable fun j => ‖v j‖)
    (hkernel_cont : Continuous kernel)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum
      (fun p : ℕ × ℕ => ∫ x in a..b,
        (u p.1 * v p.2) * pairCosinePhase L p x * kernel x)
      (∫ x in a..b, ∑' p : ℕ × ℕ,
        (u p.1 * v p.2) * pairCosinePhase L p x * kernel x) := by
  simpa only [boundedPhaseTerm] using
    hasSum_intervalIntegral_boundedPhase a b
      (fun p : ℕ × ℕ => u p.1 * v p.2) (pairCosinePhase L)
      kernel C (summable_norm_pairCoefficient u v hu hv)
      (continuous_pairCosinePhase L) (norm_pairCosinePhase_le_one L)
      hkernel_cont hkernel hC

/-- Association chosen for a triple series before constrained reindexing. -/
abbrev TripleIndex := (ℕ × ℕ) × ℕ

def tripleCoefficient (u v w : ℕ → ℝ) (p : TripleIndex) : ℝ :=
  u p.1.1 * v p.1.2 * w p.2

theorem summable_norm_tripleCoefficient (u v w : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖)
    (hv : Summable fun j => ‖v j‖)
    (hw : Summable fun l => ‖w l‖) :
    Summable fun p : TripleIndex => ‖tripleCoefficient u v w p‖ := by
  have huv : Summable fun p : ℕ × ℕ => ‖u p.1 * v p.2‖ := hu.mul_norm hv
  simpa only [tripleCoefficient, mul_assoc] using huv.mul_norm hw

def tripleCosinePhase (L : ℝ) (p : TripleIndex) (x : ℝ) : ℝ :=
  pairCosinePhase L p.1 x * cosinePhase L p.2 x

theorem continuous_tripleCosinePhase (L : ℝ) (p : TripleIndex) :
    Continuous (tripleCosinePhase L p) :=
  (continuous_pairCosinePhase L p.1).mul (continuous_cosinePhase L p.2)

theorem norm_tripleCosinePhase_le_one (L : ℝ) (p : TripleIndex) (x : ℝ) :
    ‖tripleCosinePhase L p x‖ ≤ 1 := by
  rw [tripleCosinePhase, norm_mul]
  simpa only [one_mul] using mul_le_mul
    (norm_pairCosinePhase_le_one L p.1 x)
    (norm_cosinePhase_le_one L p.2 x)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- Triple-series interval interchange, the analytic half of the four-cosine
identity in the current Lemma 2.1. -/
theorem hasSum_intervalIntegral_cosineTriple (a b L : ℝ)
    (u v w : ℕ → ℝ) (kernel : ℝ → ℝ) (C : ℝ)
    (hu : Summable fun i => ‖u i‖)
    (hv : Summable fun j => ‖v j‖)
    (hw : Summable fun l => ‖w l‖)
    (hkernel_cont : Continuous kernel)
    (hkernel : ∀ x, ‖kernel x‖ ≤ C) (hC : 0 ≤ C) :
    HasSum
      (fun p : TripleIndex => ∫ x in a..b,
        tripleCoefficient u v w p * tripleCosinePhase L p x * kernel x)
      (∫ x in a..b, ∑' p : TripleIndex,
        tripleCoefficient u v w p * tripleCosinePhase L p x * kernel x) := by
  simpa only [boundedPhaseTerm] using
    hasSum_intervalIntegral_boundedPhase a b
      (tripleCoefficient u v w) (tripleCosinePhase L)
      kernel C (summable_norm_tripleCoefficient u v w hu hv hw)
      (continuous_tripleCosinePhase L) (norm_tripleCosinePhase_le_one L)
      hkernel_cont hkernel hC

end

end ChemotaxisBifurcation.InfiniteCosineProjection
