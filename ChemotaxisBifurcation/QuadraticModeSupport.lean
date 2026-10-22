module
public import ChemotaxisBifurcation.NeumannProjection
public import ChemotaxisBifurcation.QuadraticJet

@[expose] public section

/-!
# Quadratic forcing support

The current paper's quadratic forcing contains only the constant and doubled
critical modes.  This module proves the resulting zero projection for every
other positive Neumann mode and the conditional vanishing of its graph
coefficient.
-/

namespace ChemotaxisBifurcation

noncomputable def quadraticForcingProfile
    (c0 c2 L : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  c0 + c2 * neumannMode L (2 * n) y

theorem integral_neumannMode_positive_zero
    (L : ℝ) (k : ℕ) (hL : 0 < L) (hk : 0 < k) :
    (∫ y in (0 : ℝ)..L, neumannMode L k y) = 0 := by
  unfold neumannMode waveNumber
  have hk0 : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.ne_of_gt hk)
  have h := integral_cos_mode_int L hL (k : ℤ)
  rw [if_neg hk0] at h
  simpa using h

/-- A constant-plus-doubled-mode forcing has zero normalized projection onto
every other positive mode. -/
theorem quadraticForcing_other_mode_projection_zero
    (c0 c2 L : ℝ) (n k : ℕ)
    (hL : 0 < L) (hk : 0 < k) (hne : k ≠ 2 * n) :
    2 / L * (∫ y in (0 : ℝ)..L,
      quadraticForcingProfile c0 c2 L n y * neumannMode L k y) = 0 := by
  rw [show (fun y : ℝ =>
      quadraticForcingProfile c0 c2 L n y * neumannMode L k y) =
      fun y => c0 * neumannMode L k y +
        c2 * (neumannMode L (2 * n) y * neumannMode L k y) by
      funext y
      unfold quadraticForcingProfile
      ring]
  have hcont : ∀ j : ℕ, Continuous (neumannMode L j) := by
    intro j
    unfold neumannMode waveNumber
    continuity
  rw [intervalIntegral.integral_add
      (f := fun y => c0 * neumannMode L k y)
      (g := fun y => c2 *
        (neumannMode L (2 * n) y * neumannMode L k y))
      ((continuous_const.mul (hcont k)).intervalIntegrable _ _)
      ((continuous_const.mul ((hcont (2 * n)).mul (hcont k))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_neumannMode_positive_zero L k hL hk,
    integral_neumannMode_mul L hL]
  have hne' : 2 * n ≠ k := fun h => hne h.symm
  simp [hne']

/-- If the stable modal eigenvalue is nonzero, the zero quadratic forcing
forces the corresponding graph coefficient to vanish. -/
theorem other_mode_quadratic_coefficient_zero
    (sigma ak : ℝ) (hsigma : sigma ≠ 0)
    (hresidual : sigma * ak + 0 = 0) :
    ak = 0 := by
  exact (mul_eq_zero.mp (by simpa using hresidual)).resolve_left hsigma

end ChemotaxisBifurcation
