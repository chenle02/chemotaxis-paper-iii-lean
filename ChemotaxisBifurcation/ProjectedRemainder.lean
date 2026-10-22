module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# Cosine projection of a source-plus-flux remainder

The revised manuscript (the 2026-10-16 compact revision of arXiv:2610.20976, p. 14 after
(2.11), and p. 17 before (2.22)) writes the fourth-order remainder of the projected equation
as `R₄ = R₄⁽⁰⁾ + ∂ₓR₄⁽¹⁾`, with pointwise bounds on `R₄⁽⁰⁾` and `R₄⁽¹⁾` and `R₄⁽¹⁾ = 0` at
`x = 0, L` (because `ṽₓ = 0` there). Projecting against `cos(kπx/L)` and integrating the flux
part by parts, with no boundary term, gives the bound `C_k ‖u‖⁴`. This module checks that
deduction on `[0, L]`.

* `projected_remainder_bound`: if `R₁` is continuous on `[0, L]`, has derivative `dR₁` on
  `(0, L)`, `dR₁` is interval integrable, `R₁ 0 = R₁ L = 0`, and `|R₀|, |R₁| ≤ B` on `[0, L]`,
  then `|∫₀ᴸ (R₀ + dR₁) cos(kπx/L) dx| ≤ (L + kπ) B`.
* `projected_remainder_bound_of_absolutelyContinuous`: the same with `R₁` absolutely
  continuous on `[0, L]` and `deriv R₁` (defined almost everywhere) in place of `dR₁`.
* `projected_remainder_bound_quartic`: with the paper's pointwise bounds
  `|R₀| ≤ C|U|⁴`, `|R₁| ≤ C(|U| + |V|)³|Vₓ|`, `Vₓ(0) = Vₓ(L) = 0` and
  `|U| + |V| + |Vₓ| ≤ M` on `[0, L]`, the projection is at most `(L + kπ) C M⁴`.
* `projected_remainder_bound_norm`: if moreover `M = K N` (`N` a norm of the solution, for
  instance `‖u‖_{ℓ¹}`), the projection is at most `C_k N⁴` with `C_k = (L + kπ) C K⁴`.

The bound `(L + kπ) B` is the one the argument gives: `L B` from the source part and
`(kπ/L) · L B` from the flux part after integration by parts.

Not claimed here: the decomposition `R₄ = R₄⁽⁰⁾ + ∂ₓR₄⁽¹⁾` itself, the pointwise bounds on
`R₄⁽⁰⁾`, `R₄⁽¹⁾`, and the embeddings `X_θ ↪ C¹` and `X_θ ↪ ℓ¹` that bound `M` by a multiple
of `‖ũ‖_{X_θ}`. They are hypotheses.
-/

namespace ChemotaxisBifurcation.ProjectedRemainder

open Real Set MeasureTheory intervalIntegral

/-- The frequency `kπ/L` of the `k`th Neumann cosine mode on `[0, L]`. -/
noncomputable def freq (L : ℝ) (k : ℕ) : ℝ := k * π / L

theorem freq_nonneg {L : ℝ} (hL : 0 < L) (k : ℕ) : 0 ≤ freq L k := by
  unfold freq; positivity

theorem freq_mul_L {L : ℝ} (hL : 0 < L) (k : ℕ) : freq L k * L = k * π := by
  unfold freq; field_simp

/-- The cosine mode written as `cos (freq L k * x)` agrees with `cos (kπx/L)`. -/
theorem cos_freq (L : ℝ) (k : ℕ) (x : ℝ) : cos (freq L k * x) = cos (k * π * x / L) := by
  unfold freq; ring_nf

/-- Integration by parts against the cosine mode, with vanishing boundary values:
`∫₀ᴸ dR₁ cos(ωx) dx = ω ∫₀ᴸ R₁ sin(ωx) dx`, `ω = kπ/L`. -/
theorem integral_deriv_mul_cos {L : ℝ} (hL : 0 < L) (k : ℕ) {R1 dR1 : ℝ → ℝ}
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0) :
    ∫ x in (0 : ℝ)..L, dR1 x * cos (freq L k * x) =
      freq L k * ∫ x in (0 : ℝ)..L, R1 x * sin (freq L k * x) := by
  set ω := freq L k
  have hle : (0 : ℝ) ≤ L := hL.le
  have hcos_cont : ContinuousOn (fun x => cos (ω * x)) (uIcc 0 L) := by fun_prop
  have hR1c' : ContinuousOn R1 (uIcc 0 L) := by rwa [uIcc_of_le hle]
  have hcos_d : ∀ x ∈ Ioo (min 0 L) (max 0 L),
      HasDerivAt (fun x => cos (ω * x)) (-sin (ω * x) * ω) x := by
    intro x _
    have := ((hasDerivAt_id x).const_mul ω).cos
    simpa [mul_comm] using this
  have hR1d' : ∀ x ∈ Ioo (min 0 L) (max 0 L), HasDerivAt R1 (dR1 x) x := by
    intro x hx
    rw [min_eq_left hle, max_eq_right hle] at hx
    exact hR1d x hx
  have hsin_int : IntervalIntegrable (fun x => -sin (ω * x) * ω) volume 0 L :=
    (by fun_prop : Continuous fun x => -sin (ω * x) * ω).intervalIntegrable 0 L
  -- `∫ cos · dR₁ = cos L R₁ L - cos 0 R₁ 0 - ∫ (-ω sin) R₁`.
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcos_cont hR1c' hcos_d hR1d'
    hsin_int hdR1
  have hswap : ∫ x in (0 : ℝ)..L, dR1 x * cos (ω * x) =
      ∫ x in (0 : ℝ)..L, cos (ω * x) * dR1 x := by
    congr 1; ext x; ring
  rw [hswap, hibp, h0, hL0]
  have : ∫ x in (0 : ℝ)..L, -sin (ω * x) * ω * R1 x =
      -(ω * ∫ x in (0 : ℝ)..L, R1 x * sin (ω * x)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; ext x; ring
  rw [this]; ring

/-- `|∫₀ᴸ f| ≤ L B` when `|f| ≤ B` on `[0, L]`. -/
theorem abs_integral_le_of_abs_le {L B : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 L, |f x| ≤ B) : |∫ x in (0 : ℝ)..L, f x| ≤ L * B := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L) (C := B)
    (f := f) (fun x hx => by
      rw [uIoc_of_le hL.le] at hx
      simpa [Real.norm_eq_abs] using hf x (Ioc_subset_Icc_self hx))
  simpa [Real.norm_eq_abs, abs_of_pos hL, mul_comm] using h

/-- The estimate shared by the two integration-by-parts forms: once
`∫₀ᴸ dR₁ cos = ω ∫₀ᴸ R₁ sin`, the projection is at most `(L + kπ) B`. -/
theorem projected_bound_of_ibp {L B : ℝ} (hL : 0 < L) (k : ℕ) {R0 R1 dR1 : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L) (hdR1 : IntervalIntegrable dR1 volume 0 L)
    (hibp : ∫ x in (0 : ℝ)..L, dR1 x * cos (freq L k * x) =
      freq L k * ∫ x in (0 : ℝ)..L, R1 x * sin (freq L k * x))
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B := by
  set ω := freq L k with hω
  have hcosc : Continuous fun x => cos (ω * x) := by fun_prop
  have hsplit : ∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L) =
      (∫ x in (0 : ℝ)..L, R0 x * cos (ω * x)) + ∫ x in (0 : ℝ)..L, dR1 x * cos (ω * x) := by
    rw [← intervalIntegral.integral_add (hR0.mul_continuousOn hcosc.continuousOn)
      (hdR1.mul_continuousOn hcosc.continuousOn)]
    congr 1; ext x; rw [hω, cos_freq]; ring
  rw [hsplit, hibp]
  have h1 : |∫ x in (0 : ℝ)..L, R0 x * cos (ω * x)| ≤ L * B :=
    abs_integral_le_of_abs_le hL fun x hx => by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)).trans (hB0 x hx)
  have h2 : |∫ x in (0 : ℝ)..L, R1 x * sin (ω * x)| ≤ L * B :=
    abs_integral_le_of_abs_le hL fun x hx => by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)).trans (hB1 x hx)
  have hω0 : 0 ≤ ω := freq_nonneg hL k
  calc |(∫ x in (0 : ℝ)..L, R0 x * cos (ω * x)) + ω * ∫ x in (0 : ℝ)..L, R1 x * sin (ω * x)|
      ≤ |∫ x in (0 : ℝ)..L, R0 x * cos (ω * x)| + ω * |∫ x in (0 : ℝ)..L, R1 x * sin (ω * x)| := by
        rw [← abs_of_nonneg hω0, ← abs_mul, abs_of_nonneg hω0]; exact abs_add_le _ _
    _ ≤ L * B + ω * (L * B) := by gcongr
    _ = (L + k * π) * B := by rw [← freq_mul_L hL k]; ring

/-- **Projected remainder bound** (differentiable flux). For `L > 0` and `k : ℕ`, let `R₁` be
continuous on `[0, L]` with derivative `dR₁` on `(0, L)`, `dR₁` interval integrable,
`R₁ 0 = R₁ L = 0`, and let `R₀` be interval integrable, with `|R₀|, |R₁| ≤ B` on `[0, L]`. Then
`|∫₀ᴸ (R₀ + dR₁) cos(kπx/L) dx| ≤ (L + kπ) B`. -/
theorem projected_remainder_bound {L B : ℝ} (hL : 0 < L) (k : ℕ) {R0 R1 dR1 : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B :=
  projected_bound_of_ibp hL k hR0 hdR1 (integral_deriv_mul_cos hL k hR1c hR1d hdR1 h0 hL0)
    hB0 hB1

/-- **Projected remainder bound** (`deriv` form). As `projected_remainder_bound`, with
`R₁` differentiable on `(0, L)` and the flux derivative written `deriv R₁`. -/
theorem projected_remainder_bound_deriv {L B : ℝ} (hL : 0 < L) (k : ℕ) {R0 R1 : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ R1 x)
    (hdR1 : IntervalIntegrable (deriv R1) volume 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + deriv R1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B :=
  projected_remainder_bound hL k hR0 hR1c (fun x hx => (hR1d x hx).hasDerivAt) hdR1 h0 hL0
    hB0 hB1

/-- **Projected remainder bound** (absolutely continuous flux). As `projected_remainder_bound`,
with `R₁` absolutely continuous on `[0, L]` and the flux derivative `deriv R₁`, which exists
almost everywhere and is integrable (Mathlib's `AbsolutelyContinuousOnInterval`). -/
theorem projected_remainder_bound_of_absolutelyContinuous {L B : ℝ} (hL : 0 < L) (k : ℕ)
    {R0 R1 : ℝ → ℝ} (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1 : AbsolutelyContinuousOnInterval R1 0 L) (h0 : R1 0 = 0) (hL0 : R1 L = 0)
    (hB0 : ∀ x ∈ Icc 0 L, |R0 x| ≤ B) (hB1 : ∀ x ∈ Icc 0 L, |R1 x| ≤ B) :
    |∫ x in (0 : ℝ)..L, (R0 x + deriv R1 x) * cos (k * π * x / L)| ≤ (L + k * π) * B := by
  set ω := freq L k
  have hcos : AbsolutelyContinuousOnInterval (fun x => cos (ω * x)) 0 L :=
    ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
  have hibp : ∫ x in (0 : ℝ)..L, deriv R1 x * cos (ω * x) =
      ω * ∫ x in (0 : ℝ)..L, R1 x * sin (ω * x) := by
    have h := hcos.integral_mul_deriv_eq_deriv_mul hR1
    have hd : ∀ x, deriv (fun x => cos (ω * x)) x = -sin (ω * x) * ω := by
      intro x
      have := ((hasDerivAt_id x).const_mul ω).cos
      simp [mul_comm]
    simp_rw [hd, h0, hL0] at h
    have hswap : ∫ x in (0 : ℝ)..L, deriv R1 x * cos (ω * x) =
        ∫ x in (0 : ℝ)..L, cos (ω * x) * deriv R1 x := by
      congr 1; ext x; ring
    rw [hswap, h]
    have : ∫ x in (0 : ℝ)..L, -sin (ω * x) * ω * R1 x =
        -(ω * ∫ x in (0 : ℝ)..L, R1 x * sin (ω * x)) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      congr 1; ext x; ring
    rw [this]; ring
  exact projected_bound_of_ibp hL k hR0 hR1.intervalIntegrable_deriv hibp hB0 hB1

/-- **Quartic form** (the paper's `C_k ‖u‖⁴` shape). With `|R₀| ≤ C|U|⁴`,
`|R₁| ≤ C(|U| + |V|)³|Vₓ|`, `Vₓ(0) = Vₓ(L) = 0` (so `R₁` vanishes at `0` and `L`), and
`|U| + |V| + |Vₓ| ≤ M` on `[0, L]`, the projection is at most `(L + kπ) C M⁴`. Here `U`, `V`,
`Vₓ` stand for `ũ`, `ṽ`, `ṽₓ`; `Vₓ` is any function, not required to be the derivative of
`V`. -/
theorem projected_remainder_bound_quartic {L C M : ℝ} (hL : 0 < L) (k : ℕ) (hC : 0 ≤ C)
    {R0 R1 dR1 U V Vx : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L)
    (hR0b : ∀ x ∈ Icc 0 L, |R0 x| ≤ C * |U x| ^ 4)
    (hR1b : ∀ x ∈ Icc 0 L, |R1 x| ≤ C * (|U x| + |V x|) ^ 3 * |Vx x|)
    (hVx0 : Vx 0 = 0) (hVxL : Vx L = 0)
    (hM : ∀ x ∈ Icc 0 L, |U x| + |V x| + |Vx x| ≤ M) :
    |∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L)| ≤ (L + k * π) * (C * M ^ 4) := by
  have hzero : ∀ x ∈ Icc 0 L, Vx x = 0 → R1 x = 0 := fun x hx h0 => by
    have := hR1b x hx; rw [h0, abs_zero, mul_zero] at this
    exact abs_nonpos_iff.mp this
  have h0 : R1 0 = 0 := hzero 0 ⟨le_rfl, hL.le⟩ hVx0
  have hL0 : R1 L = 0 := hzero L ⟨hL.le, le_rfl⟩ hVxL
  refine projected_remainder_bound hL k hR0 hR1c hR1d hdR1 h0 hL0 (fun x hx => ?_)
    (fun x hx => ?_)
  · have hu : |U x| ≤ M := by
      have := hM x hx; linarith [abs_nonneg (V x), abs_nonneg (Vx x)]
    calc |R0 x| ≤ C * |U x| ^ 4 := hR0b x hx
      _ ≤ C * M ^ 4 := by gcongr
  · have huv : |U x| + |V x| ≤ M := by
      have := hM x hx; linarith [abs_nonneg (Vx x)]
    have hvx : |Vx x| ≤ M := by
      have := hM x hx; linarith [abs_nonneg (U x), abs_nonneg (V x)]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hvx
    calc |R1 x| ≤ C * (|U x| + |V x|) ^ 3 * |Vx x| := hR1b x hx
      _ ≤ C * M ^ 3 * M := by gcongr
      _ = C * M ^ 4 := by ring

/-- **Norm form**: if moreover `M = K N` (for instance `N = ‖u‖_{ℓ¹}` and `K` the constant of
`‖ṽ‖_{C¹} ≤ C‖ũ‖_{L∞} ≤ C‖u‖_{ℓ¹}`), the projection is at most `C_k N⁴` with
`C_k = (L + kπ) C K⁴`. -/
theorem projected_remainder_bound_norm {L C K N : ℝ} (hL : 0 < L) (k : ℕ) (hC : 0 ≤ C)
    {R0 R1 dR1 U V Vx : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L)) (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L)
    (hR0b : ∀ x ∈ Icc 0 L, |R0 x| ≤ C * |U x| ^ 4)
    (hR1b : ∀ x ∈ Icc 0 L, |R1 x| ≤ C * (|U x| + |V x|) ^ 3 * |Vx x|)
    (hVx0 : Vx 0 = 0) (hVxL : Vx L = 0)
    (hM : ∀ x ∈ Icc 0 L, |U x| + |V x| + |Vx x| ≤ K * N) :
    |∫ x in (0 : ℝ)..L, (R0 x + dR1 x) * cos (k * π * x / L)| ≤
      ((L + k * π) * C * K ^ 4) * N ^ 4 := by
  have h := projected_remainder_bound_quartic hL k hC hR0 hR1c hR1d hdR1 hR0b hR1b hVx0 hVxL hM
  calc _ ≤ (L + k * π) * (C * (K * N) ^ 4) := h
    _ = ((L + k * π) * C * K ^ 4) * N ^ 4 := by ring

/-- Non-vacuity: the hypotheses of `projected_remainder_bound` hold for `R₀ = 1`,
`R₁ x = sin(πx/L)` (vanishing at `0` and `L`) with `B = 1`, so the bound is not vacuous. -/
theorem projected_remainder_bound_example {L : ℝ} (hL : 0 < L) (k : ℕ) :
    |∫ x in (0 : ℝ)..L, ((fun _ => (1 : ℝ)) x + (fun x => π / L * cos (π / L * x)) x) *
        cos (k * π * x / L)| ≤ (L + k * π) * 1 := by
  refine projected_remainder_bound (R1 := fun x => sin (π / L * x)) hL k
    (by simp) (by fun_prop) (fun x _ => ?_)
    ((by fun_prop : Continuous fun x => π / L * cos (π / L * x)).intervalIntegrable 0 L)
    (by simp) ?_ (fun x _ => by simp)
    (fun x _ => abs_sin_le_one _)
  · have := ((hasDerivAt_id x).const_mul (π / L)).sin
    simpa [mul_comm] using this
  · show sin (π / L * L) = 0
    rw [div_mul_cancel₀ π hL.ne', sin_pi]

end ChemotaxisBifurcation.ProjectedRemainder
