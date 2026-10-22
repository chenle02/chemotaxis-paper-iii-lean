module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
public import ChemotaxisBifurcation.ProjectedRemainder
public import ChemotaxisBifurcation.CosineCoefficients

@[expose] public section

/-!
# Normalized modal remainders (Paper III v2)

The signal remainder is the cosine coefficient of its Taylor source divided by
`μ + (kπ/L)²`. This gives exactly the factors `1/(μL)` at zero and
`2/[L(μ+λ_k)]` at positive modes in the manuscript. A bounded source suffices
for summability; no derivative bound on that source is used.

The population remainder is a normalized cosine coefficient of a source plus
a flux derivative. Its estimate consumes `ProjectedRemainder`'s integration
by parts result. Taylor decomposition, elliptic estimates, and identification
with an actual PDE solution remain explicit analytic inputs, not conclusions.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.ModalRemainder

open Real Set MeasureTheory
open CosineCoefficients ProjectedRemainder

noncomputable section

/-- The resolvent applied to the actual normalized cosine coefficient of a source. -/
def signalRemainder (L mu : ℝ) (R : ℝ → ℝ) (k : ℕ) : ℝ :=
  cosineCoeff L R k / (mu + (k * Real.pi / L) ^ 2)

theorem signalRemainder_zero (L mu : ℝ) (R : ℝ → ℝ) :
    signalRemainder L mu R 0 = (mu * L)⁻¹ * ∫ x in (0 : ℝ)..L, R x := by
  simp only [signalRemainder, Nat.cast_zero, zero_mul, zero_div, zero_pow (by decide : 2 ≠ 0),
    add_zero, cosineCoeff_zero]
  simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
  ring

theorem signalRemainder_pos (L mu : ℝ) (R : ℝ → ℝ) {k : ℕ} (hk : k ≠ 0) :
    signalRemainder L mu R k = 2 * (L * (mu + (k * Real.pi / L) ^ 2))⁻¹ *
      ∫ x in (0 : ℝ)..L, R x * cos (k * Real.pi * x / L) := by
  rw [signalRemainder, cosineCoeff_of_ne_zero L R hk]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Projected signal balance uniquely determines this normalization. -/
theorem signalRemainder_eq_of_balance {L mu q : ℝ} {R : ℝ → ℝ} {k : ℕ}
    (hd : mu + (k * Real.pi / L) ^ 2 ≠ 0)
    (h : (mu + (k * Real.pi / L) ^ 2) * q = cosineCoeff L R k) :
    q = signalRemainder L mu R k := by
  apply (eq_div_iff hd).2
  simpa [mul_comm] using h

theorem cosineCoeff_zero_bound {L B : ℝ} (hL : 0 < L) {R : ℝ → ℝ}
    (hB : ∀ x ∈ Icc 0 L, |R x| ≤ B) : |cosineCoeff L R 0| ≤ B := by
  rw [cosineCoeff_zero, abs_mul, abs_of_pos (one_div_pos.mpr hL)]
  calc 1 / L * |∫ x in (0 : ℝ)..L, R x| ≤ 1 / L * (L * B) :=
      mul_le_mul_of_nonneg_left (abs_integral_le_of_abs_le hL hB) (by positivity)
    _ = B := by field_simp

theorem cosineCoeff_pos_bound {L B : ℝ} (hL : 0 < L) {R : ℝ → ℝ}
    (hB : ∀ x ∈ Icc 0 L, |R x| ≤ B) {k : ℕ} (hk : k ≠ 0) :
    |cosineCoeff L R k| ≤ 2 * B := by
  rw [cosineCoeff_of_ne_zero L R hk, abs_mul, abs_of_pos (div_pos (by norm_num) hL)]
  have hb : |∫ x in (0 : ℝ)..L, R x * cos (k * Real.pi * x / L)| ≤ L * B :=
    abs_integral_le_of_abs_le hL fun x hx => by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)).trans (hB x hx)
  calc 2 / L * |∫ x in (0 : ℝ)..L, R x * cos (k * Real.pi * x / L)| ≤
      2 / L * (L * B) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 * B := by field_simp

theorem signalRemainder_zero_bound {L mu B : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    {R : ℝ → ℝ} (hB : ∀ x ∈ Icc 0 L, |R x| ≤ B) :
    |signalRemainder L mu R 0| ≤ B / mu := by
  simp only [signalRemainder, Nat.cast_zero, zero_mul, zero_div,
    zero_pow (by decide : 2 ≠ 0), add_zero, abs_div, abs_of_pos hmu]
  exact div_le_div_of_nonneg_right (cosineCoeff_zero_bound hL hB) hmu.le

theorem signalRemainder_pos_bound {L mu B : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    {R : ℝ → ℝ} (hB : ∀ x ∈ Icc 0 L, |R x| ≤ B) {k : ℕ} (hk : k ≠ 0) :
    |signalRemainder L mu R k| ≤ 2 * B / (mu + (k * Real.pi / L) ^ 2) := by
  rw [signalRemainder, abs_div, abs_of_pos (by positivity : 0 < mu + (k * Real.pi / L) ^ 2)]
  exact div_le_div_of_nonneg_right (cosineCoeff_pos_bound hL hB hk) (by positivity)

/-- Fourth-order signal estimates in the manuscript's norm variable `N`. -/
theorem signalRemainder_quartic {L mu C N : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    {R : ℝ → ℝ} (hR : ∀ x ∈ Icc 0 L, |R x| ≤ C * N ^ 4) :
    |signalRemainder L mu R 0| ≤ C * N ^ 4 / mu ∧
      ∀ k : ℕ, k ≠ 0 → |signalRemainder L mu R k| ≤
        2 * (C * N ^ 4) / (mu + (k * Real.pi / L) ^ 2) :=
  ⟨signalRemainder_zero_bound hL hmu hR, fun _ hk => signalRemainder_pos_bound hL hmu hR hk⟩

/-- The resolvent denominator makes the signal remainder sequence summable. -/
theorem summable_norm_signalRemainder {L mu B : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (hB0 : 0 ≤ B) {R : ℝ → ℝ} (hB : ∀ x ∈ Icc 0 L, |R x| ≤ B) :
    Summable fun k => ‖signalRemainder L mu R k‖ := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left (2 * B * (L / Real.pi) ^ 2))
  rw [Real.norm_eq_abs]
  have hk : (k + 1 : ℕ) ≠ 0 := by omega
  have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hf : 0 < ((k + 1 : ℕ) * Real.pi / L) ^ 2 := by positivity
  calc |signalRemainder L mu R (k + 1)| ≤
      2 * B / (mu + ((k + 1 : ℕ) * Real.pi / L) ^ 2) :=
        signalRemainder_pos_bound hL hmu hB hk
    _ ≤ 2 * B / (((k + 1 : ℕ) * Real.pi / L) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hf (by linarith)
    _ = (2 * B * (L / Real.pi) ^ 2) * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
      field_simp

/-- Normalization of any population projection estimate, including zero mode. -/
theorem population_normalized_bound {L B : ℝ} (hL : 0 < L) {R : ℝ → ℝ} (k : ℕ)
    (h : |∫ x in (0 : ℝ)..L, R x * cos (k * Real.pi * x / L)| ≤ B) :
    |cosineCoeff L R k| ≤ (if k = 0 then 1 / L else 2 / L) * B := by
  unfold cosineCoeff
  rw [abs_mul, abs_of_nonneg (by split_ifs <;> positivity)]
  exact mul_le_mul_of_nonneg_left h (by split_ifs <;> positivity)

/-- Norm-form population estimate after division by the cosine mode norm.
The source and flux hypotheses are exactly those of the existing IBP consumer. -/
theorem population_remainder_quartic {L C K N : ℝ} (hL : 0 < L) (k : ℕ) (hC : 0 ≤ C)
    {R0 R1 dR1 U V Vx : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L))
    (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L)
    (hR0b : ∀ x ∈ Icc 0 L, |R0 x| ≤ C * |U x| ^ 4)
    (hR1b : ∀ x ∈ Icc 0 L, |R1 x| ≤ C * (|U x| + |V x|) ^ 3 * |Vx x|)
    (hVx0 : Vx 0 = 0) (hVxL : Vx L = 0)
    (hM : ∀ x ∈ Icc 0 L, |U x| + |V x| + |Vx x| ≤ K * N) :
    |cosineCoeff L (fun x => R0 x + dR1 x) k| ≤
      (if k = 0 then 1 / L else 2 / L) * (((L + k * Real.pi) * C * K ^ 4) * N ^ 4) :=
  population_normalized_bound hL k
    (projected_remainder_bound_norm hL k hC hR0 hR1c hR1d hdR1 hR0b hR1b hVx0 hVxL hM)

end
end ChemotaxisBifurcation.ModalRemainder
