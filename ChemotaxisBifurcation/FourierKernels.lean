module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import ChemotaxisBifurcation.InfiniteCosineProjection
public import ChemotaxisBifurcation.NeumannProjection

@[expose] public section

/-!
# Finite Fourier kernel integrals for Lemma 2.1 (`L:trig-integrals`)

The four identities of the current Paper III Lemma 2.1 (`L:trig-integrals`,
displays `E:cosine-sine-sine`, `E:two-cosines-two-sines`, `E:cos-cos-cos`,
`E:cos-cos-cos-cos`) reduce, after termwise integration, to the following
single kernel integrals over `[0,L]` of products of the Neumann modes
`cos (i π x / L)` and the sine modes `sin (n π x / L)`:

* one cosine against two sines, `∫ cos_i sin_n sin_k`;
* three cosines, `∫ cos_i cos_j cos_k`;
* two cosines against two sines, `∫ cos_i cos_j sin_n sin_k`;
* four cosines, `∫ cos_i cos_j cos_l cos_k`.

Each is evaluated exactly as a finite sum of indicator terms, first in a
*signed* form valid for all natural indices (one indicator per product-to-sum
term, conditions `i ± j ± ... = 0` over `ℤ`), and then in the manuscript form,
where every constraint is an equation between integer casts of the natural
indices and the zero-mode multiplicity is an explicit extra indicator.

The product-of-series identification and the reindexing of product-indexed
sums to the manuscript's constrained sums are *not* done here.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.FourierKernels

open ChemotaxisBifurcation.InfiniteCosineProjection

noncomputable section

/-- The sine phase `sin (n π x / L)` (the derivative profile of the Neumann
cosine mode, up to the factor `-n π / L`). -/
def sinePhase (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n : ℝ) * Real.pi * x / L)

/-- Cosine phase with an integer (signed) frequency, `cos (m π x / L)`. -/
def intCosPhase (L : ℝ) (m : ℤ) (x : ℝ) : ℝ :=
  Real.cos ((m : ℝ) * Real.pi * x / L)

/-- Real-valued indicator of a decidable proposition. -/
def ind (P : Prop) [Decidable P] : ℝ :=
  if P then 1 else 0

theorem continuous_intCosPhase (L : ℝ) (m : ℤ) :
    Continuous (intCosPhase L m) := by
  unfold intCosPhase
  fun_prop

/-- Basic kernel: `∫₀ᴸ cos (m π x / L) dx = L · 1_{m = 0}` for `m ∈ ℤ`. -/
theorem integral_intCosPhase (L : ℝ) (hL : 0 < L) (m : ℤ) :
    (∫ x in (0 : ℝ)..L, intCosPhase L m x) = L * ind (m = 0) := by
  have h : ∀ x : ℝ, intCosPhase L m x =
      Real.cos (((m : ℝ) * Real.pi / L) * x) := by
    intro x
    unfold intCosPhase
    congr 1
    ring
  simp only [h]
  rw [ChemotaxisBifurcation.integral_cos_mode_int L hL m, ind]
  split_ifs <;> ring

private theorem integral_term (L : ℝ) (hL : 0 < L) (c : ℝ) (m : ℤ) :
    (∫ x in (0 : ℝ)..L, c * intCosPhase L m x) = c * (L * ind (m = 0)) := by
  rw [intervalIntegral.integral_const_mul, integral_intCosPhase L hL]

private theorem integral_add_term (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ)
    (hf : Continuous f) (c : ℝ) (m : ℤ) :
    (∫ x in (0 : ℝ)..L, (f x + c * intCosPhase L m x)) =
      (∫ x in (0 : ℝ)..L, f x) + c * (L * ind (m = 0)) := by
  rw [intervalIntegral.integral_add (f := f)
    (g := fun x => c * intCosPhase L m x) (hf.intervalIntegrable _ _)
    ((continuous_const.mul (continuous_intCosPhase L m)).intervalIntegrable _ _),
    integral_term L hL]

/-- Integral of a four-term signed cosine combination. -/
theorem integral_four_intCosPhase (L : ℝ) (hL : 0 < L)
    (c₁ c₂ c₃ c₄ : ℝ) (m₁ m₂ m₃ m₄ : ℤ) :
    (∫ x in (0 : ℝ)..L,
      (c₁ * intCosPhase L m₁ x + c₂ * intCosPhase L m₂ x +
        c₃ * intCosPhase L m₃ x + c₄ * intCosPhase L m₄ x)) =
      L * (c₁ * ind (m₁ = 0) + c₂ * ind (m₂ = 0) +
        c₃ * ind (m₃ = 0) + c₄ * ind (m₄ = 0)) := by
  rw [integral_add_term L hL, integral_add_term L hL, integral_add_term L hL,
    integral_term L hL]
  · ring
  all_goals
    unfold intCosPhase
    fun_prop

/-- Integral of an eight-term signed cosine combination. -/
theorem integral_eight_intCosPhase (L : ℝ) (hL : 0 < L)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℝ) (m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ : ℤ) :
    (∫ x in (0 : ℝ)..L,
      (c₁ * intCosPhase L m₁ x + c₂ * intCosPhase L m₂ x +
        c₃ * intCosPhase L m₃ x + c₄ * intCosPhase L m₄ x +
        c₅ * intCosPhase L m₅ x + c₆ * intCosPhase L m₆ x +
        c₇ * intCosPhase L m₇ x + c₈ * intCosPhase L m₈ x)) =
      L * (c₁ * ind (m₁ = 0) + c₂ * ind (m₂ = 0) +
        c₃ * ind (m₃ = 0) + c₄ * ind (m₄ = 0) +
        c₅ * ind (m₅ = 0) + c₆ * ind (m₆ = 0) +
        c₇ * ind (m₇ = 0) + c₈ * ind (m₈ = 0)) := by
  rw [integral_add_term L hL, integral_add_term L hL, integral_add_term L hL,
    integral_add_term L hL, integral_add_term L hL, integral_add_term L hL,
    integral_add_term L hL, integral_term L hL]
  · ring
  all_goals
    unfold intCosPhase
    fun_prop

/-! ### Pointwise product-to-sum identities -/

private theorem phase_mul (L x a : ℝ) :
    a * Real.pi * x / L = a * (Real.pi * x / L) := by
  ring

/-- `cos_i sin_n sin_k` as a signed four-term cosine combination. -/
theorem cos_sin_sin_eq (L : ℝ) (i n k : ℕ) (x : ℝ) :
    cosinePhase L i x * sinePhase L n x * sinePhase L k x =
      (1 / 4) * intCosPhase L ((i : ℤ) + n - k) x +
        (1 / 4) * intCosPhase L ((i : ℤ) - n + k) x +
        (-1 / 4) * intCosPhase L ((i : ℤ) + n + k) x +
        (-1 / 4) * intCosPhase L ((i : ℤ) - n - k) x := by
  unfold cosinePhase sinePhase intCosPhase
  push_cast
  simp only [phase_mul L x]
  generalize Real.pi * x / L = t
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add,
    Real.sin_sub]
  ring

/-- `cos_i cos_j cos_k` as a signed four-term cosine combination. -/
theorem cos_cos_cos_eq (L : ℝ) (i j k : ℕ) (x : ℝ) :
    cosinePhase L i x * cosinePhase L j x * cosinePhase L k x =
      (1 / 4) * intCosPhase L ((i : ℤ) + j + k) x +
        (1 / 4) * intCosPhase L ((i : ℤ) + j - k) x +
        (1 / 4) * intCosPhase L ((i : ℤ) - j + k) x +
        (1 / 4) * intCosPhase L ((i : ℤ) - j - k) x := by
  unfold cosinePhase intCosPhase
  push_cast
  simp only [phase_mul L x]
  generalize Real.pi * x / L = t
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add,
    Real.sin_sub]
  ring

/-- `cos_i cos_j sin_n sin_k` as a signed eight-term cosine combination. -/
theorem cos_cos_sin_sin_eq (L : ℝ) (i j n k : ℕ) (x : ℝ) :
    cosinePhase L i x * cosinePhase L j x * sinePhase L n x *
        sinePhase L k x =
      (1 / 8) * intCosPhase L ((i : ℤ) + j + n - k) x +
        (1 / 8) * intCosPhase L ((i : ℤ) + j - n + k) x +
        (1 / 8) * intCosPhase L ((i : ℤ) - j + n - k) x +
        (1 / 8) * intCosPhase L ((i : ℤ) - j - n + k) x +
        (-1 / 8) * intCosPhase L ((i : ℤ) + j + n + k) x +
        (-1 / 8) * intCosPhase L ((i : ℤ) + j - n - k) x +
        (-1 / 8) * intCosPhase L ((i : ℤ) - j + n + k) x +
        (-1 / 8) * intCosPhase L ((i : ℤ) - j - n - k) x := by
  unfold cosinePhase sinePhase intCosPhase
  push_cast
  simp only [phase_mul L x]
  generalize Real.pi * x / L = t
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add,
    Real.sin_sub]
  ring

/-- `cos_i cos_j cos_l cos_k` as a signed eight-term cosine combination. -/
theorem cos_cos_cos_cos_eq (L : ℝ) (i j l k : ℕ) (x : ℝ) :
    cosinePhase L i x * cosinePhase L j x * cosinePhase L l x *
        cosinePhase L k x =
      (1 / 8) * intCosPhase L ((i : ℤ) + j + l + k) x +
        (1 / 8) * intCosPhase L ((i : ℤ) + j + l - k) x +
        (1 / 8) * intCosPhase L ((i : ℤ) + j - l + k) x +
        (1 / 8) * intCosPhase L ((i : ℤ) + j - l - k) x +
        (1 / 8) * intCosPhase L ((i : ℤ) - j + l + k) x +
        (1 / 8) * intCosPhase L ((i : ℤ) - j + l - k) x +
        (1 / 8) * intCosPhase L ((i : ℤ) - j - l + k) x +
        (1 / 8) * intCosPhase L ((i : ℤ) - j - l - k) x := by
  unfold cosinePhase intCosPhase
  push_cast
  simp only [phase_mul L x]
  generalize Real.pi * x / L = t
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add,
    Real.sin_sub]
  ring

/-! ### Signed kernel integrals (all natural indices, including zero modes) -/

/-- Signed form of the one-cosine/two-sine kernel; valid for all `i n k`. -/
theorem integral_cos_sin_sin_signed (L : ℝ) (hL : 0 < L) (i n k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L i x * sinePhase L n x * sinePhase L k x) =
      L / 4 * (ind ((i : ℤ) + n - k = 0) + ind ((i : ℤ) - n + k = 0) -
        ind ((i : ℤ) + n + k = 0) - ind ((i : ℤ) - n - k = 0)) := by
  rw [intervalIntegral.integral_congr (fun x _ => cos_sin_sin_eq L i n k x),
    integral_four_intCosPhase L hL]
  ring

/-- Signed form of the three-cosine kernel; valid for all `i j k`. -/
theorem integral_cos_cos_cos_signed (L : ℝ) (hL : 0 < L) (i j k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L i x * cosinePhase L j x * cosinePhase L k x) =
      L / 4 * (ind ((i : ℤ) + j + k = 0) + ind ((i : ℤ) + j - k = 0) +
        ind ((i : ℤ) - j + k = 0) + ind ((i : ℤ) - j - k = 0)) := by
  rw [intervalIntegral.integral_congr (fun x _ => cos_cos_cos_eq L i j k x),
    integral_four_intCosPhase L hL]
  ring

/-- Signed form of the two-cosine/two-sine kernel; valid for all `i j n k`. -/
theorem integral_cos_cos_sin_sin_signed (L : ℝ) (hL : 0 < L) (i j n k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L i x * cosinePhase L j x * sinePhase L n x *
        sinePhase L k x) =
      L / 8 * (ind ((i : ℤ) + j + n - k = 0) + ind ((i : ℤ) + j - n + k = 0) +
        ind ((i : ℤ) - j + n - k = 0) + ind ((i : ℤ) - j - n + k = 0) -
        ind ((i : ℤ) + j + n + k = 0) - ind ((i : ℤ) + j - n - k = 0) -
        ind ((i : ℤ) - j + n + k = 0) - ind ((i : ℤ) - j - n - k = 0)) := by
  rw [intervalIntegral.integral_congr
      (fun x _ => cos_cos_sin_sin_eq L i j n k x),
    integral_eight_intCosPhase L hL]
  ring

/-- Signed form of the four-cosine kernel; valid for all `i j l k`. -/
theorem integral_cos_cos_cos_cos_signed (L : ℝ) (hL : 0 < L) (i j l k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L i x * cosinePhase L j x * cosinePhase L l x *
        cosinePhase L k x) =
      L / 8 * (ind ((i : ℤ) + j + l + k = 0) + ind ((i : ℤ) + j + l - k = 0) +
        ind ((i : ℤ) + j - l + k = 0) + ind ((i : ℤ) + j - l - k = 0) +
        ind ((i : ℤ) - j + l + k = 0) + ind ((i : ℤ) - j + l - k = 0) +
        ind ((i : ℤ) - j - l + k = 0) + ind ((i : ℤ) - j - l - k = 0)) := by
  rw [intervalIntegral.integral_congr
      (fun x _ => cos_cos_cos_cos_eq L i j l k x),
    integral_eight_intCosPhase L hL]
  ring

/-! ### Manuscript-form kernel integrals -/

private theorem ind_congr {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) : ind P = ind Q := by
  unfold ind
  by_cases hQ : Q
  · simp [hQ, h.mpr hQ]
  · simp [hQ, mt h.mp hQ]

private theorem ind_false {P : Prop} [Decidable P] (h : ¬P) : ind P = 0 := by
  unfold ind
  simp [h]

/-- Kernel of `E:cosine-sine-sine` (TeX line 1179): for `n, k ≥ 1`, the
coefficient of `u_i` is `(L/4)(1_{i=|n-k|} - 1_{i=n+k} + δ_{nk} 1_{i=0})`. -/
theorem integral_cos_sin_sin (L : ℝ) (hL : 0 < L) (i n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L i x * sinePhase L n x * sinePhase L k x) =
      L / 4 * (ind (i = Int.natAbs ((n : ℤ) - k)) - ind (i = n + k) +
        ind (n = k ∧ i = 0)) := by
  rw [integral_cos_sin_sin_signed L hL i n k,
    ind_false (P := (i : ℤ) + n + k = 0) (by omega),
    ind_congr (P := (i : ℤ) - n - k = 0) (Q := i = n + k) (by omega)]
  have key : ind ((i : ℤ) + n - k = 0) + ind ((i : ℤ) - n + k = 0) =
      ind (i = Int.natAbs ((n : ℤ) - k)) + ind (n = k ∧ i = 0) := by
    have habs := Int.natAbs_eq ((n : ℤ) - k)
    unfold ind
    generalize Int.natAbs ((n : ℤ) - k) = a at habs ⊢
    split_ifs <;> first | (exfalso; omega) | norm_num
  rw [show ind ((i : ℤ) + n - k = 0) + ind ((i : ℤ) - n + k = 0) - 0 -
      ind (i = n + k) =
      (ind ((i : ℤ) + n - k = 0) + ind ((i : ℤ) - n + k = 0)) -
        ind (i = n + k) by ring, key]
  ring

/-- Kernel of `E:cos-cos-cos` (TeX line 1204): for all `k ≥ 0`, the
coefficient of `u_i v_j` is
`(L/4)(1_{i-j=k} + 1_{i-j=-k} + 1_{i+j=k}) + (L/4) 1_{k=0} 1_{i=0} 1_{j=0}`. -/
theorem integral_cos_cos_cos (L : ℝ) (hL : 0 < L) (i j k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L i x * cosinePhase L j x * cosinePhase L k x) =
      L / 4 * (ind ((i : ℤ) - j = k) + ind ((i : ℤ) - j = -k) +
        ind ((i : ℤ) + j = k)) +
        L / 4 * ind (k = 0 ∧ i = 0 ∧ j = 0) := by
  rw [integral_cos_cos_cos_signed L hL i j k,
    ind_congr (P := (i : ℤ) + j + k = 0) (Q := k = 0 ∧ i = 0 ∧ j = 0)
      (by omega),
    ind_congr (P := (i : ℤ) + j - k = 0) (Q := (i : ℤ) + j = k) (by omega),
    ind_congr (P := (i : ℤ) - j + k = 0) (Q := (i : ℤ) - j = -k) (by omega),
    ind_congr (P := (i : ℤ) - j - k = 0) (Q := (i : ℤ) - j = k) (by omega)]
  ring

/-- Kernel of `E:two-cosines-two-sines` (TeX line 1190): for `n, k ≥ 1`, the
coefficient of `u_i v_j` is `(L/8)` times the seven signed indicators of the
manuscript display. The eighth product-to-sum term `i+j = -(n+k)` vanishes
because `n + k ≥ 2`. -/
theorem integral_cos_cos_sin_sin (L : ℝ) (hL : 0 < L) (i j n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L i x * cosinePhase L j x * sinePhase L n x *
        sinePhase L k x) =
      L / 8 * (ind ((i : ℤ) - j = (n : ℤ) - k) +
        ind ((i : ℤ) - j = -((n : ℤ) - k)) +
        ind ((i : ℤ) + j = (n : ℤ) - k) +
        ind ((i : ℤ) + j = -((n : ℤ) - k)) -
        ind ((i : ℤ) - j = (n : ℤ) + k) -
        ind ((i : ℤ) - j = -((n : ℤ) + k)) -
        ind ((i : ℤ) + j = (n : ℤ) + k)) := by
  rw [integral_cos_cos_sin_sin_signed L hL i j n k,
    ind_congr (P := (i : ℤ) + j + n - k = 0)
      (Q := (i : ℤ) + j = -((n : ℤ) - k)) (by omega),
    ind_congr (P := (i : ℤ) + j - n + k = 0)
      (Q := (i : ℤ) + j = (n : ℤ) - k) (by omega),
    ind_congr (P := (i : ℤ) - j + n - k = 0)
      (Q := (i : ℤ) - j = -((n : ℤ) - k)) (by omega),
    ind_congr (P := (i : ℤ) - j - n + k = 0)
      (Q := (i : ℤ) - j = (n : ℤ) - k) (by omega),
    ind_false (P := (i : ℤ) + j + n + k = 0) (by omega),
    ind_congr (P := (i : ℤ) + j - n - k = 0)
      (Q := (i : ℤ) + j = (n : ℤ) + k) (by omega),
    ind_congr (P := (i : ℤ) - j + n + k = 0)
      (Q := (i : ℤ) - j = -((n : ℤ) + k)) (by omega),
    ind_congr (P := (i : ℤ) - j - n - k = 0)
      (Q := (i : ℤ) - j = (n : ℤ) + k) (by omega)]
  ring

/-- Kernel of `E:cos-cos-cos-cos` (TeX line 1220): for all `k ≥ 0`, the
coefficient of `u_i v_j w_l` is `(L/8)` times the seven signed indicators of
the manuscript display plus `(L/8) 1_{k=0} 1_{i=j=l=0}`. -/
theorem integral_cos_cos_cos_cos (L : ℝ) (hL : 0 < L) (i j l k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L i x * cosinePhase L j x * cosinePhase L l x *
        cosinePhase L k x) =
      L / 8 * (ind ((i : ℤ) + j + l = k) + ind ((i : ℤ) + j - l = k) +
        ind ((i : ℤ) + j - l = -k) + ind ((i : ℤ) - j + l = k) +
        ind ((i : ℤ) - j + l = -k) + ind ((i : ℤ) - j - l = k) +
        ind ((i : ℤ) - j - l = -k)) +
        L / 8 * ind (k = 0 ∧ i = 0 ∧ j = 0 ∧ l = 0) := by
  rw [integral_cos_cos_cos_cos_signed L hL i j l k,
    ind_congr (P := (i : ℤ) + j + l + k = 0)
      (Q := k = 0 ∧ i = 0 ∧ j = 0 ∧ l = 0) (by omega),
    ind_congr (P := (i : ℤ) + j + l - k = 0)
      (Q := (i : ℤ) + j + l = k) (by omega),
    ind_congr (P := (i : ℤ) + j - l + k = 0)
      (Q := (i : ℤ) + j - l = -k) (by omega),
    ind_congr (P := (i : ℤ) + j - l - k = 0)
      (Q := (i : ℤ) + j - l = k) (by omega),
    ind_congr (P := (i : ℤ) - j + l + k = 0)
      (Q := (i : ℤ) - j + l = -k) (by omega),
    ind_congr (P := (i : ℤ) - j + l - k = 0)
      (Q := (i : ℤ) - j + l = k) (by omega),
    ind_congr (P := (i : ℤ) - j - l + k = 0)
      (Q := (i : ℤ) - j - l = -k) (by omega),
    ind_congr (P := (i : ℤ) - j - l - k = 0)
      (Q := (i : ℤ) - j - l = k) (by omega)]
  ring

/-! ### Zero-mode negative controls

Dropping the explicit zero-mode term from each manuscript formula gives a
false value at the smallest instance. -/

/-- Without `δ_{nk} u_0`, the `E:cosine-sine-sine` kernel at `i = 0`,
`n = k = 1` would be `L/4`; the true value is `L/2`. -/
theorem cos_sin_sin_zero_mode_control (L : ℝ) (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L 0 x * sinePhase L 1 x * sinePhase L 1 x) = L / 2 ∧
    (∫ x in (0 : ℝ)..L,
      cosinePhase L 0 x * sinePhase L 1 x * sinePhase L 1 x) ≠ L / 4 := by
  rw [integral_cos_sin_sin L hL 0 1 1 le_rfl le_rfl]
  simp only [ind]
  norm_num
  constructor
  · ring
  · intro h
    linarith

/-- Without `1_{k=0} u_0 v_0`, the `E:cos-cos-cos` kernel at `i = j = k = 0`
would be `3L/4`; the true value is `L`. -/
theorem cos_cos_cos_zero_mode_control (L : ℝ) (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L 0 x * cosinePhase L 0 x * cosinePhase L 0 x) = L ∧
    (∫ x in (0 : ℝ)..L,
      cosinePhase L 0 x * cosinePhase L 0 x * cosinePhase L 0 x) ≠
      3 * L / 4 := by
  rw [integral_cos_cos_cos L hL 0 0 0]
  simp only [ind]
  norm_num
  constructor
  · ring
  · intro h
    linarith

/-- Without `1_{k=0} u_0 v_0 w_0`, the `E:cos-cos-cos-cos` kernel at
`i = j = l = k = 0` would be `7L/8`; the true value is `L`. -/
theorem cos_cos_cos_cos_zero_mode_control (L : ℝ) (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L,
      cosinePhase L 0 x * cosinePhase L 0 x * cosinePhase L 0 x *
        cosinePhase L 0 x) = L ∧
    (∫ x in (0 : ℝ)..L,
      cosinePhase L 0 x * cosinePhase L 0 x * cosinePhase L 0 x *
        cosinePhase L 0 x) ≠ 7 * L / 8 := by
  rw [integral_cos_cos_cos_cos L hL 0 0 0 0]
  simp only [ind]
  norm_num
  constructor
  · ring
  · intro h
    linarith

end

end ChemotaxisBifurcation.FourierKernels
