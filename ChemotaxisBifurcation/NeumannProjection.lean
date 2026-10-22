module
/-
Adapted from the MIT-licensed Paper III Lean package published at
chenle02/Chemataxis_Numerics, commit 5c7ef67e3c39e13daeef9321069e459b7444d04d.
-/

public import ChemotaxisBifurcation.FiniteProjection

@[expose] public section

/-!
# Actual normalized Neumann projections

This module connects the pointwise harmonic decompositions to the manuscript
projection `Π_n f = (2/L) ∫₀ᴸ f φ_n` for positive modes.
-/

namespace ChemotaxisBifurcation

open Real

noncomputable section

/-- Neumann wave number `n π / L`. -/
noncomputable def waveNumber (L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.pi / L

/-- Unnormalized Neumann cosine mode used by the manuscript. -/
noncomputable def neumannMode (L : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  Real.cos (waveNumber L n * y)

lemma integral_cos_linear (c L : ℝ) (hc : c ≠ 0) :
    (∫ y in (0 : ℝ)..L, Real.cos (c * y)) = Real.sin (c * L) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun y => Real.cos y) hc,
    integral_cos]
  simp
  ring

lemma integral_cos_mode_int (L : ℝ) (hL : 0 < L) (j : ℤ) :
    (∫ y in (0 : ℝ)..L,
      Real.cos (((j : ℝ) * Real.pi / L) * y)) =
        if j = 0 then L else 0 := by
  by_cases hj : j = 0
  · subst hj
    simp
  · rw [if_neg hj]
    have hj' : (j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
    have hc : (j : ℝ) * Real.pi / L ≠ 0 :=
      div_ne_zero (mul_ne_zero hj' (ne_of_gt Real.pi_pos)) (ne_of_gt hL)
    rw [integral_cos_linear _ _ hc]
    have hstep : (j : ℝ) * Real.pi / L * L = (j : ℝ) * Real.pi := by
      field_simp
    rw [hstep, Real.sin_int_mul_pi]
    simp

/-- Exact orthogonality and normalization of the unnormalized modes. -/
theorem integral_neumannMode_mul
    (L : ℝ) (hL : 0 < L) (m n : ℕ) :
    (∫ y in (0 : ℝ)..L, neumannMode L m y * neumannMode L n y) =
      if m = n then (if m = 0 then L else L / 2) else 0 := by
  have key : ∀ y : ℝ, neumannMode L m y * neumannMode L n y =
      (Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * Real.pi / L * y) +
        Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * Real.pi / L * y)) / 2 := by
    intro y
    unfold neumannMode waveNumber
    have c1 : ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) =
        (m : ℝ) - (n : ℝ) := by push_cast; ring
    have c2 : ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ)) =
        (m : ℝ) + (n : ℝ) := by push_cast; ring
    rw [c1, c2]
    have e1 : ((m : ℝ) - (n : ℝ)) * Real.pi / L * y =
        (m : ℝ) * Real.pi / L * y - (n : ℝ) * Real.pi / L * y := by
      field_simp
    have e2 : ((m : ℝ) + (n : ℝ)) * Real.pi / L * y =
        (m : ℝ) * Real.pi / L * y + (n : ℝ) * Real.pi / L * y := by
      field_simp
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    ring
  have hcont1 : Continuous fun y : ℝ =>
      Real.cos (((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) * Real.pi / L * y) := by
    continuity
  have hcont2 : Continuous fun y : ℝ =>
      Real.cos (((((m : ℤ) + (n : ℤ) : ℤ) : ℝ)) * Real.pi / L * y) := by
    continuity
  rw [intervalIntegral.integral_congr (g := fun y =>
        (Real.cos (((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) * Real.pi / L * y) +
          Real.cos (((((m : ℤ) + (n : ℤ) : ℤ) : ℝ)) * Real.pi / L * y)) / 2)
        (fun y _ => key y)]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add
      (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _),
    integral_cos_mode_int L hL, integral_cos_mode_int L hL]
  by_cases hmn : m = n
  · subst hmn
    by_cases hm : m = 0
    · subst hm
      norm_num
    · have hsum : ((m : ℤ) + (m : ℤ)) ≠ 0 := by
        have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hm
        omega
      simp [hsum, hm]
  · have hdiff : ((m : ℤ) - (n : ℤ)) ≠ 0 := by
      intro h
      exact hmn (by exact_mod_cast sub_eq_zero.mp h)
    have hsum : ((m : ℤ) + (n : ℤ)) ≠ 0 := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · rcases Nat.eq_zero_or_pos n with hn | hn
        · exact absurd (hm.trans hn.symm) hmn
        · omega
      · omega
    simp [hdiff, hsum, hmn]

/-- Normalized positive-mode self projection. -/
theorem normalized_neumann_self
    (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      neumannMode L n y * neumannMode L n y) = 1 := by
  rw [integral_neumannMode_mul L hL]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  simp [hn0, ne_of_gt hL]

/-- The third harmonic is killed by the normalized critical projection. -/
theorem normalized_neumann_third_zero
    (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      neumannMode L (3 * n) y * neumannMode L n y) = 0 := by
  rw [integral_neumannMode_mul L hL]
  have h3n : 3 * n ≠ n := by omega
  simp [h3n]

/-- Constant plus second-harmonic quadratic graph profile. -/
noncomputable def quadraticJetProfile
    (a0 a2 L : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  a0 + a2 * neumannMode L (2 * n) y

/-- The normalized constant projection of the quadratic graph profile is
exactly `a0`. -/
theorem average_quadraticJetProfile
    (a0 a2 L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    1 / L * (∫ y in (0 : ℝ)..L, quadraticJetProfile a0 a2 L n y) = a0 := by
  have hcont : Continuous (neumannMode L (2 * n)) := by
    unfold neumannMode waveNumber
    continuity
  rw [show (fun y : ℝ => quadraticJetProfile a0 a2 L n y) =
      fun y => a0 + a2 * neumannMode L (2 * n) y by rfl]
  rw [intervalIntegral.integral_add
      (f := fun y : ℝ => a0)
      (g := fun y => a2 * neumannMode L (2 * n) y)
      (continuous_const.intervalIntegrable (0 : ℝ) L)
      ((continuous_const.mul hcont).intervalIntegrable (0 : ℝ) L),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  have hmode :
      (∫ y in (0 : ℝ)..L, neumannMode L (2 * n) y) = 0 := by
    unfold neumannMode waveNumber
    have h2n : (2 * (n : ℤ)) ≠ 0 := by omega
    have h := integral_cos_mode_int L hL (2 * (n : ℤ))
    rw [if_neg h2n] at h
    convert h using 1 <;> push_cast <;> ring
  rw [hmode]
  simp only [zero_mul, add_zero, sub_zero, smul_eq_mul]
  field_simp [ne_of_gt hL]
  ring

/-- A fixed-mass mean-zero quadratic graph has no constant population mode. -/
theorem a0_eq_zero_of_mean_zero
    (a0 a2 L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n)
    (hmean : 1 / L *
      (∫ y in (0 : ℝ)..L, quadraticJetProfile a0 a2 L n y) = 0) :
    a0 = 0 := by
  rw [average_quadraticJetProfile a0 a2 L n hL hn] at hmean
  exact hmean

/-- Cubic-order contribution of the squared center-graph state. -/
noncomputable def quadraticCenterCubic
    (a0 a2 theta : ℝ) : ℝ :=
  2 * a0 * Real.cos theta +
    2 * a2 * (Real.cos theta * Real.cos (2 * theta))

theorem quadraticCenterCubic_decomposition
    (a0 a2 theta : ℝ) :
    quadraticCenterCubic a0 a2 theta =
      (2 * a0 + a2) * Real.cos theta +
        a2 * Real.cos (3 * theta) := by
  unfold quadraticCenterCubic
  rw [cos_mul_cos_two]
  ring_nf

/-- Actual normalized critical projection of the quadratic logistic channel. -/
theorem normalized_quadratic_logistic_projection
    (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) (a0 a2 : ℝ) :
    2 / L * (∫ y in (0 : ℝ)..L,
      quadraticCenterCubic a0 a2 (waveNumber L n * y) *
        neumannMode L n y) = 2 * a0 + a2 := by
  rw [show (fun y : ℝ =>
      quadraticCenterCubic a0 a2 (waveNumber L n * y) * neumannMode L n y) =
      fun y => (2 * a0 + a2) *
          (neumannMode L n y * neumannMode L n y) +
        a2 * (neumannMode L (3 * n) y * neumannMode L n y) by
      funext y
      rw [quadraticCenterCubic_decomposition]
      unfold neumannMode waveNumber
      push_cast
      ring_nf]
  have hcont : ∀ m : ℕ, Continuous (neumannMode L m) := by
    intro m
    unfold neumannMode waveNumber
    continuity
  rw [intervalIntegral.integral_add
      (f := fun y => (2 * a0 + a2) *
        (neumannMode L n y * neumannMode L n y))
      (g := fun y => a2 *
        (neumannMode L (3 * n) y * neumannMode L n y))
      ((continuous_const.mul ((hcont n).mul (hcont n))).intervalIntegrable _ _)
      ((continuous_const.mul ((hcont (3 * n)).mul (hcont n))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_neumannMode_mul L hL,
    integral_neumannMode_mul L hL]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have h3n : 3 * n ≠ n := by omega
  simp [hn0, h3n]
  field_simp [ne_of_gt hL]

/-- Actual normalized critical projection of the bare cubic state. -/
theorem normalized_cubic_logistic_projection
    (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      neumannMode L n y ^ 3 * neumannMode L n y) = 3 / 4 := by
  rw [show (fun y : ℝ => neumannMode L n y ^ 3 * neumannMode L n y) =
      fun y => (3 / 4 : ℝ) *
          (neumannMode L n y * neumannMode L n y) +
        (1 / 4 : ℝ) *
          (neumannMode L (3 * n) y * neumannMode L n y) by
      funext y
      unfold neumannMode waveNumber
      rw [cos_cube]
      push_cast
      ring_nf]
  have hcont : ∀ m : ℕ, Continuous (neumannMode L m) := by
    intro m
    unfold neumannMode waveNumber
    continuity
  rw [intervalIntegral.integral_add
      (f := fun y => (3 / 4 : ℝ) *
        (neumannMode L n y * neumannMode L n y))
      (g := fun y => (1 / 4 : ℝ) *
        (neumannMode L (3 * n) y * neumannMode L n y))
      ((continuous_const.mul ((hcont n).mul (hcont n))).intervalIntegrable _ _)
      ((continuous_const.mul ((hcont (3 * n)).mul (hcont n))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_neumannMode_mul L hL,
    integral_neumannMode_mul L hL]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have h3n : 3 * n ≠ n := by omega
  simp [hn0, h3n]
  field_simp [ne_of_gt hL]

/-- Actual normalized projection of the quadratic density onto mode `2n`. -/
theorem normalized_quadratic_density_projection
    (d : QuadraticProjectionData) (L : ℝ) (n : ℕ)
    (hL : 0 < L) (hn : 0 < n) :
    let k := waveNumber L n
    2 / L * (∫ y in (0 : ℝ)..L,
      d.density k y * neumannMode L (2 * n) y) = k ^ 2 * d.bracket := by
  dsimp only
  have hmode : (fun y : ℝ => Real.cos (2 * (waveNumber L n * y))) =
      neumannMode L (2 * n) := by
    funext y
    unfold neumannMode waveNumber
    congr 1
    push_cast
    ring
  rw [show (fun y : ℝ => d.density (waveNumber L n) y *
        neumannMode L (2 * n) y) = fun y =>
      (waveNumber L n ^ 2 * d.bracket) *
        (neumannMode L (2 * n) y * neumannMode L (2 * n) y) by
      funext y
      unfold QuadraticProjectionData.density
      rw [show Real.cos (2 * (waveNumber L n * y)) =
        neumannMode L (2 * n) y from congrFun hmode y]
      ring_nf]
  rw [intervalIntegral.integral_const_mul,
    integral_neumannMode_mul L hL]
  have h2n : 2 * n ≠ 0 := by omega
  simp [h2n]
  field_simp [ne_of_gt hL]

/-- Actual normalized projection of the four-channel cubic density. -/
theorem normalized_cubic_density_projection
    (d : RawCubicProjectionData) (L : ℝ) (n : ℕ)
    (hL : 0 < L) (hn : 0 < n) :
    let k := waveNumber L n
    2 / L * (∫ y in (0 : ℝ)..L,
      d.density k y * neumannMode L n y) = k ^ 2 * d.criticalBracket := by
  dsimp only
  have hmode1 : (fun y : ℝ => Real.cos (waveNumber L n * y)) =
      neumannMode L n := by
    funext y
    rfl
  have hmode3 : (fun y : ℝ => Real.cos (3 * (waveNumber L n * y))) =
      neumannMode L (3 * n) := by
    funext y
    unfold neumannMode waveNumber
    congr 1
    push_cast
    ring
  rw [show (fun y : ℝ => d.density (waveNumber L n) y * neumannMode L n y) =
      fun y =>
        (waveNumber L n ^ 2 * d.criticalBracket) *
          (neumannMode L n y * neumannMode L n y) +
        (3 * waveNumber L n ^ 2 * d.thirdBracket) *
          (neumannMode L (3 * n) y * neumannMode L n y) by
      funext y
      unfold RawCubicProjectionData.density
      rw [show Real.cos (waveNumber L n * y) = neumannMode L n y from
        congrFun hmode1 y]
      rw [show Real.cos (3 * (waveNumber L n * y)) =
        neumannMode L (3 * n) y from congrFun hmode3 y]
      ring_nf]
  have hcont : ∀ m : ℕ, Continuous (neumannMode L m) := by
    intro m
    unfold neumannMode waveNumber
    continuity
  rw [intervalIntegral.integral_add
      (f := fun y => (waveNumber L n ^ 2 * d.criticalBracket) *
        (neumannMode L n y * neumannMode L n y))
      (g := fun y => (3 * waveNumber L n ^ 2 * d.thirdBracket) *
        (neumannMode L (3 * n) y * neumannMode L n y))
      ((continuous_const.mul ((hcont n).mul (hcont n))).intervalIntegrable _ _)
      ((continuous_const.mul ((hcont (3 * n)).mul (hcont n))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_neumannMode_mul L hL,
    integral_neumannMode_mul L hL]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have h3n : 3 * n ≠ n := by omega
  simp [hn0, h3n]
  field_simp [ne_of_gt hL]

end

end ChemotaxisBifurcation
