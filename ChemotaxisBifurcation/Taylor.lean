module
/-
Adapted from the MIT-licensed Paper III Lean package published at
chenle02/Chemataxis_Numerics, commit 5c7ef67e3c39e13daeef9321069e459b7444d04d.
-/

public import ChemotaxisBifurcation.Model

@[expose] public section

/-!
# Primitive Taylor coefficients

This module derives the scalar real-power derivatives behind current
Equations 2.7--2.10.  It does not formalize the function-valued remainder
estimates used by the PDE argument.
-/

namespace ChemotaxisBifurcation

/-- First derivative of a real power. -/
theorem rpow_first (r x : ℝ) :
    deriv (fun y : ℝ => y ^ r) x = r * x ^ (r - 1) := by
  exact Real.deriv_rpow_const x r

/-- Second derivative of a real power in falling-factorial form. -/
theorem rpow_second (r x : ℝ) :
    deriv^[2] (fun y : ℝ => y ^ r) x =
      r * (r - 1) * x ^ (r - 2) := by
  rw [Real.iter_deriv_rpow_const]
  have hpoch : (descPochhammer ℝ 2).eval r = r * (r - 1) := by
    norm_num [descPochhammer]
  rw [hpoch]
  norm_num

/-- Third derivative of a real power in falling-factorial form. -/
theorem rpow_third (r x : ℝ) :
    deriv^[3] (fun y : ℝ => y ^ r) x =
      r * (r - 1) * (r - 2) * x ^ (r - 3) := by
  rw [Real.iter_deriv_rpow_const]
  have hpoch :
      (descPochhammer ℝ 3).eval r = r * (r - 1) * (r - 2) := by
    norm_num [descPochhammer]
    ring
  rw [hpoch]
  norm_num

/-- Derivatives of the sensitivity weight `y^(-beta)`. -/
theorem sensitivity_weight_derivatives (beta w : ℝ) :
    deriv (fun y : ℝ => y ^ (-beta)) w =
        -beta * w ^ (-beta - 1) ∧
    deriv^[2] (fun y : ℝ => y ^ (-beta)) w =
        beta * (beta + 1) * w ^ (-beta - 2) ∧
    deriv^[3] (fun y : ℝ => y ^ (-beta)) w =
        -beta * (beta + 1) * (beta + 2) * w ^ (-beta - 3) := by
  constructor
  · simpa using rpow_first (-beta) w
  constructor
  · rw [rpow_second]
    ring
  · rw [rpow_third]
    ring

/-- Derivatives of the density mobility `u^m`. -/
theorem mobility_density_derivatives (m u : ℝ) :
    deriv (fun y : ℝ => y ^ m) u = m * u ^ (m - 1) ∧
    deriv^[2] (fun y : ℝ => y ^ m) u =
        m * (m - 1) * u ^ (m - 2) ∧
    deriv^[3] (fun y : ℝ => y ^ m) u =
        m * (m - 1) * (m - 2) * u ^ (m - 3) := by
  exact ⟨rpow_first m u, rpow_second m u, rpow_third m u⟩

/-- Derivatives of the signal production `ν u^γ`. -/
theorem signal_derivatives (gamma u : ℝ) :
    deriv (fun y : ℝ => y ^ gamma) u = gamma * u ^ (gamma - 1) ∧
    deriv^[2] (fun y : ℝ => y ^ gamma) u =
        gamma * (gamma - 1) * u ^ (gamma - 2) ∧
    deriv^[3] (fun y : ℝ => y ^ gamma) u =
        gamma * (gamma - 1) * (gamma - 2) * u ^ (gamma - 3) := by
  exact ⟨rpow_first gamma u, rpow_second gamma u, rpow_third gamma u⟩

/-- Derivatives of the logistic power `u^(1+alpha)`. -/
theorem logistic_derivatives (alpha u : ℝ) :
    deriv (fun y : ℝ => y ^ (1 + alpha)) u =
        (1 + alpha) * u ^ alpha ∧
    deriv^[2] (fun y : ℝ => y ^ (1 + alpha)) u =
        (1 + alpha) * alpha * u ^ (alpha - 1) ∧
    deriv^[3] (fun y : ℝ => y ^ (1 + alpha)) u =
        (1 + alpha) * alpha * (alpha - 1) * u ^ (alpha - 2) := by
  constructor
  · rw [rpow_first]
    ring_nf
  constructor
  · rw [rpow_second]
    ring_nf
  · rw [rpow_third]
    ring_nf

/-- The factorial divisions used by the displayed Taylor polynomials. -/
theorem taylor_factorial_normalization (c1 c2 c3 : ℝ) :
    c1 + c2 / (2 : ℝ) + c3 / (6 : ℝ) =
      c1 + (1 / 2 : ℝ) * c2 + (1 / 6 : ℝ) * c3 := by
  ring

/-- Current Equations 2.7--2.10 collected as raw Taylor data. -/
noncomputable def rawTaylorData
    (p : PhysicalParams) (beta : ℝ) : RawTaylorData where
  B0 := p.uStar ^ p.m / p.signalOffset ^ beta
  Bu := p.m * p.uStar ^ (p.m - 1) / p.signalOffset ^ beta
  Bv := -beta * p.uStar ^ p.m / p.signalOffset ^ (beta + 1)
  Buu := p.m * (p.m - 1) * p.uStar ^ (p.m - 2) /
    (2 * p.signalOffset ^ beta)
  Buv := -(p.m * beta) * p.uStar ^ (p.m - 1) /
    p.signalOffset ^ (beta + 1)
  Bvv := beta * (beta + 1) * p.uStar ^ p.m /
    (2 * p.signalOffset ^ (beta + 2))
  Aprime := p.alpha * p.uStar ^ p.alpha
  Asecond :=
    (1 + p.alpha) * p.alpha * p.uStar ^ (p.alpha - 1) / 2
  Athird :=
    (1 + p.alpha) * p.alpha * (p.alpha - 1) *
      p.uStar ^ (p.alpha - 2) / 6
  Cprime := p.nu * p.gamma * p.uStar ^ (p.gamma - 1)
  Csecond :=
    p.nu * p.gamma * (p.gamma - 1) *
      p.uStar ^ (p.gamma - 2) / 2
  Cthird :=
    p.nu * p.gamma * (p.gamma - 1) * (p.gamma - 2) *
      p.uStar ^ (p.gamma - 3) / 6

/-- The physical first mobility derivative equals `B₀ (m/u*)`. -/
theorem raw_Bu_eq_scaled
    (p : PhysicalParams) (beta : ℝ) (hu : 0 < p.uStar) :
    (rawTaylorData p beta).Bu =
      (rawTaylorData p beta).B0 * (mobilityScaledTaylor p beta).BuOverB0 := by
  simp only [rawTaylorData, mobilityScaledTaylor]
  rw [Real.rpow_sub hu, Real.rpow_one]
  field_simp [hu.ne']

/-- The physical signal derivative of mobility equals `B₀ (-β/(1+v*))`. -/
theorem raw_Bv_eq_scaled
    (p : PhysicalParams) (beta : ℝ) (hw : 0 < p.signalOffset) :
    (rawTaylorData p beta).Bv =
      (rawTaylorData p beta).B0 * (mobilityScaledTaylor p beta).BvOverB0 := by
  simp only [rawTaylorData, mobilityScaledTaylor]
  rw [Real.rpow_add hw, Real.rpow_one]
  field_simp [hw.ne']

/-- The physical quadratic density-mobility coefficient equals its scaled
counterpart times `B₀`. -/
theorem raw_Buu_eq_scaled
    (p : PhysicalParams) (beta : ℝ) (hu : 0 < p.uStar) :
    (rawTaylorData p beta).Buu =
      (rawTaylorData p beta).B0 * (mobilityScaledTaylor p beta).BuuOverB0 := by
  simp only [rawTaylorData, mobilityScaledTaylor]
  rw [Real.rpow_sub hu, Real.rpow_ofNat]
  field_simp [hu.ne']

/-- The physical mixed mobility coefficient equals its scaled counterpart
times `B₀`. -/
theorem raw_Buv_eq_scaled
    (p : PhysicalParams) (beta : ℝ)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) :
    (rawTaylorData p beta).Buv =
      (rawTaylorData p beta).B0 * (mobilityScaledTaylor p beta).BuvOverB0 := by
  simp only [rawTaylorData, mobilityScaledTaylor]
  rw [Real.rpow_sub hu, Real.rpow_one, Real.rpow_add hw, Real.rpow_one]
  field_simp [hu.ne', hw.ne']

/-- The physical quadratic signal-mobility coefficient equals its scaled
counterpart times `B₀`. -/
theorem raw_Bvv_eq_scaled
    (p : PhysicalParams) (beta : ℝ) (hw : 0 < p.signalOffset) :
    (rawTaylorData p beta).Bvv =
      (rawTaylorData p beta).B0 * (mobilityScaledTaylor p beta).BvvOverB0 := by
  simp only [rawTaylorData, mobilityScaledTaylor]
  rw [Real.rpow_add hw, Real.rpow_ofNat]
  field_simp [hw.ne']

/-- The logistic equilibrium relation converts `b A''` to the rational
coefficient used by the field-algebra layer. -/
theorem bAsecond_eq_scaled
    (p : PhysicalParams) (hu : 0 < p.uStar)
    (hlog : p.LogisticEquilibrium) :
    p.b * (rawTaylorData p 0).Asecond =
      (mobilityScaledTaylor p 0).bAsecond := by
  simp only [rawTaylorData, mobilityScaledTaylor]
  rw [Real.rpow_sub hu, Real.rpow_one]
  unfold PhysicalParams.LogisticEquilibrium at hlog
  rw [hlog]
  field_simp [hu.ne']

/-- The logistic equilibrium relation converts `b A'''` to the rational
coefficient used by the field-algebra layer. -/
theorem bAthird_eq_scaled
    (p : PhysicalParams) (hu : 0 < p.uStar)
    (hlog : p.LogisticEquilibrium) :
    p.b * (rawTaylorData p 0).Athird =
      (mobilityScaledTaylor p 0).bAthird := by
  simp only [rawTaylorData, mobilityScaledTaylor]
  rw [Real.rpow_sub hu, Real.rpow_ofNat]
  unfold PhysicalParams.LogisticEquilibrium at hlog
  rw [hlog]
  field_simp [hu.ne']

/-- The signal equilibrium relation converts `C'` to `μγv*/u*`. -/
theorem Cprime_eq_scaled
    (p : PhysicalParams) (hu : 0 < p.uStar)
    (hsig : p.SignalEquilibrium) :
    (rawTaylorData p 0).Cprime = (mobilityScaledTaylor p 0).Cprime := by
  simp only [rawTaylorData, mobilityScaledTaylor]
  rw [Real.rpow_sub hu, Real.rpow_one]
  unfold PhysicalParams.SignalEquilibrium at hsig
  have hmul := congrArg (fun z : ℝ => p.gamma * z) hsig
  field_simp [hu.ne']
  ring_nf at hmul ⊢
  exact hmul.symm

/-- The signal equilibrium relation converts `C''` to its rational form. -/
theorem Csecond_eq_scaled
    (p : PhysicalParams) (hu : 0 < p.uStar)
    (hsig : p.SignalEquilibrium) :
    (rawTaylorData p 0).Csecond = (mobilityScaledTaylor p 0).Csecond := by
  simp only [rawTaylorData, mobilityScaledTaylor]
  rw [Real.rpow_sub hu, Real.rpow_ofNat]
  unfold PhysicalParams.SignalEquilibrium at hsig
  have hmul := congrArg
    (fun z : ℝ => p.gamma * (p.gamma - 1) * z) hsig
  field_simp [hu.ne']
  ring_nf at hmul ⊢
  exact hmul.symm

/-- The signal equilibrium relation converts `C'''` to its rational form. -/
theorem Cthird_eq_scaled
    (p : PhysicalParams) (hu : 0 < p.uStar)
    (hsig : p.SignalEquilibrium) :
    (rawTaylorData p 0).Cthird = (mobilityScaledTaylor p 0).Cthird := by
  simp only [rawTaylorData, mobilityScaledTaylor]
  rw [Real.rpow_sub hu, Real.rpow_ofNat]
  unfold PhysicalParams.SignalEquilibrium at hsig
  have hmul := congrArg
    (fun z : ℝ => p.gamma * (p.gamma - 1) * (p.gamma - 2) * z) hsig
  field_simp [hu.ne']
  ring_nf at hmul ⊢
  exact hmul.symm

/-- The physical threshold times `B₀` equals the rational scaled threshold.

All canceled quantities are required nonzero through primitive positivity.
-/
theorem chiStar_mul_B0_eq_scaled
    (p : PhysicalParams) (x beta : ℝ)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset)
    (hnu : 0 < p.nu) (hgamma : 0 < p.gamma)
    (hx : x ≠ 0) (hsig : p.SignalEquilibrium) :
    p.chiStar x beta * p.mobilityB0 beta = chiStarTimesB0 p x := by
  have hB0 : p.mobilityB0 beta ≠ 0 := by
    unfold PhysicalParams.mobilityB0
    exact div_ne_zero (Real.rpow_pos_of_pos hu _).ne'
      (Real.rpow_pos_of_pos hw _).ne'
  have hCphys : p.signalC1Physical ≠ 0 := by
    unfold PhysicalParams.signalC1Physical
    exact mul_ne_zero (mul_ne_zero hnu.ne' hgamma.ne')
      (Real.rpow_pos_of_pos hu _).ne'
  have hCeq :
      p.signalC1Physical = (mobilityScaledTaylor p 0).Cprime := by
    change (rawTaylorData p 0).Cprime =
      (mobilityScaledTaylor p 0).Cprime
    exact Cprime_eq_scaled p hu hsig
  have hCscaled : (mobilityScaledTaylor p 0).Cprime ≠ 0 := by
    rw [← hCeq]
    exact hCphys
  unfold PhysicalParams.chiStar PhysicalParams.thresholdK chiStarTimesB0
  rw [hCeq]
  field_simp [hB0, hCscaled, hx]

end ChemotaxisBifurcation
