module
public import ChemotaxisBifurcation.ModalRemainder

@[expose] public section

/-!
# Deriving the projected elliptic balance

The input is the actual interval equation `v'' - mu*v + R = 0`,
with Neumann data and absolutely continuous first derivative. The modal
balance is proved, rather than assumed. No existence theorem or Taylor
estimate for the source is asserted.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.EllipticProjection

open Real Set MeasureTheory CosineCoefficients

noncomputable section

theorem cosineCoeff_secondDeriv {L : ℝ} (hL : 0 < L) {v dv : ℝ → ℝ}
    (hv : NeumannW21 L v dv) (k : ℕ) :
    cosineCoeff L (deriv dv) k = -(k * Real.pi / L) ^ 2 * cosineCoeff L v k := by
  by_cases hk : k = 0
  · subst k
    simp only [cosineCoeff_zero]
    rw [hv.ac_deriv.integral_deriv_eq_sub, hv.neumann_left, hv.neumann_right]
    simp
  · have h := cosineCoeff_eq_neg_mul_secondDeriv L hL hv hk
    rw [← cosineCoeff_of_ne_zero L (deriv dv) hk] at h
    have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hcancel : (k * Real.pi / L) ^ 2 * (L / (k * Real.pi)) ^ 2 = 1 := by
      field_simp
    calc cosineCoeff L (deriv dv) k =
        ((k * Real.pi / L) ^ 2 * (L / (k * Real.pi)) ^ 2) *
          cosineCoeff L (deriv dv) k := by rw [hcancel, one_mul]
      _ = -(k * Real.pi / L) ^ 2 * cosineCoeff L v k := by rw [h]; ring

/-- Both zero and positive mode balances follow from the interval equation. -/
theorem projected_balance {L mu : ℝ} (hL : 0 < L) {v dv R : ℝ → ℝ}
    (hv : NeumannW21 L v dv)
    (heq : ∀ x ∈ Ioo 0 L, deriv dv x - mu * v x + R x = 0) (k : ℕ) :
    (mu + (k * Real.pi / L) ^ 2) * cosineCoeff L v k = cosineCoeff L R k := by
  have hvc : ContinuousOn v (Icc 0 L) := by
    simpa [uIcc_of_le hL.le] using hv.ac.continuousOn
  have hc : Continuous (fun x : ℝ => cos (k * Real.pi * x / L)) := by fun_prop
  have hiV : IntervalIntegrable (fun x => v x * cos (k * Real.pi * x / L)) volume 0 L :=
    (hvc.intervalIntegrable_of_Icc hL.le).mul_continuousOn hc.continuousOn
  have hiD := hv.ac_deriv.intervalIntegrable_deriv.mul_continuousOn hc.continuousOn
  have hpoint : ∫ x in (0 : ℝ)..L, R x * cos (k * Real.pi * x / L) =
      ∫ x in (0 : ℝ)..L, (mu * v x - deriv dv x) * cos (k * Real.pi * x / L) :=
    intervalIntegral.integral_congr_Ioo_of_le hL.le fun x hx => by rw [show R x =
      mu * v x - deriv dv x by linarith [heq x hx]]
  have hlin : cosineCoeff L R k = mu * cosineCoeff L v k -
      cosineCoeff L (deriv dv) k := by
    unfold cosineCoeff
    rw [hpoint]
    rw [show (fun x => (mu * v x - deriv dv x) * cos (k * Real.pi * x / L)) =
      (fun x => mu * (v x * cos (k * Real.pi * x / L)) -
        deriv dv x * cos (k * Real.pi * x / L)) by funext x; ring]
    rw [intervalIntegral.integral_sub (hiV.const_mul mu) hiD,
      intervalIntegral.integral_const_mul]
    ring
  rw [cosineCoeff_secondDeriv hL hv k] at hlin
  linarith

/-- The actual signal coefficient equals the normalized resolvent coefficient;
the projected balance is no longer an application hypothesis. -/
theorem coefficient_eq_resolvent {L mu : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    {v dv R : ℝ → ℝ} (hv : NeumannW21 L v dv)
    (heq : ∀ x ∈ Ioo 0 L, deriv dv x - mu * v x + R x = 0) (k : ℕ) :
    cosineCoeff L v k = ModalRemainder.signalRemainder L mu R k :=
  ModalRemainder.signalRemainder_eq_of_balance (by positivity)
    (projected_balance hL hv heq k)

/-- Quartic estimates for the actual signal coefficients, from an interval
source bound and the original elliptic equation. -/
theorem signal_coefficients_quartic {L mu C N : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    {v dv R : ℝ → ℝ} (hv : NeumannW21 L v dv)
    (heq : ∀ x ∈ Ioo 0 L, deriv dv x - mu * v x + R x = 0)
    (hbound : ∀ x ∈ Icc 0 L, |R x| ≤ C * N ^ 4) :
    |cosineCoeff L v 0| ≤ C * N ^ 4 / mu ∧
      ∀ k : ℕ, k ≠ 0 → |cosineCoeff L v k| ≤
        2 * (C * N ^ 4) / (mu + (k * Real.pi / L) ^ 2) := by
  simp_rw [coefficient_eq_resolvent hL hmu hv heq]
  exact ModalRemainder.signalRemainder_quartic hL hmu hbound

/-- A bounded source yields summability for its actual Neumann resolvent
response. This does not assert the source is the full physical signal. -/
theorem summable_signal_coefficients {L mu B : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (hB : 0 ≤ B) {v dv R : ℝ → ℝ} (hv : NeumannW21 L v dv)
    (heq : ∀ x ∈ Ioo 0 L, deriv dv x - mu * v x + R x = 0)
    (hbound : ∀ x ∈ Icc 0 L, |R x| ≤ B) :
    Summable fun k => ‖cosineCoeff L v k‖ := by
  simp_rw [coefficient_eq_resolvent hL hmu hv heq]
  exact ModalRemainder.summable_norm_signalRemainder hL hmu hB hbound

end
end ChemotaxisBifurcation.EllipticProjection
