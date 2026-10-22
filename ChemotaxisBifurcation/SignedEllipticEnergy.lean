module
public import ChemotaxisBifurcation.SpikeEstimatesLogistic

@[expose] public section

/-! Signed one-dimensional Neumann resolvent estimates from the actual
linear differential equation. No positivity of the response or source is
assumed. These provide reusable energies for local uniqueness and C1 bounds. -/
set_option autoImplicit false
namespace ChemotaxisBifurcation.SignedEllipticEnergy
open Set MeasureTheory
noncomputable section

/-- Classical interval data for V''-mu*V+F=0. The differential equation is
expressed through the actual derivative of dV, not an energy assumption. -/
structure Profile (L mu : ℝ) (F : ℝ → ℝ) where
  V : ℝ → ℝ
  dV : ℝ → ℝ
  continuous_V : ContinuousOn V (Icc 0 L)
  continuous_dV : ContinuousOn dV (Icc 0 L)
  derivative_V : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x
  equation : ∀ x ∈ Ioo 0 L, HasDerivAt dV (mu * V x - F x) x
  neumann_left : dV 0 = 0
  neumann_right : dV L = 0

namespace Profile
variable {L mu : ℝ} {F : ℝ → ℝ}

theorem energy (p : Profile L mu F) (hL : 0 ≤ L)
    (hF : ContinuousOn F (Icc 0 L)) :
    (∫ x in (0 : ℝ)..L, p.dV x ^ 2) + mu * (∫ x in (0 : ℝ)..L, p.V x ^ 2) =
      ∫ x in (0 : ℝ)..L, F x * p.V x := by
  have hc : ContinuousOn (fun x => p.dV x ^ 2 + mu * p.V x ^ 2 - F x * p.V x)
      (Icc 0 L) := (p.continuous_dV.pow 2).add
      (continuousOn_const.mul (p.continuous_V.pow 2)) |>.sub (hF.mul p.continuous_V)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL
    (f := fun x => p.V x * p.dV x) (p.continuous_V.mul p.continuous_dV)
    (f' := fun x => p.dV x ^ 2 + mu * p.V x ^ 2 - F x * p.V x)
    (fun x hx => by
      convert (p.derivative_V x hx).mul (p.equation x hx) using 1; ring)
    (hc.intervalIntegrable_of_Icc hL)
  rw [p.neumann_left, p.neumann_right] at hi
  have hD : IntervalIntegrable (fun x => p.dV x ^ 2) volume 0 L :=
    (p.continuous_dV.pow 2).intervalIntegrable_of_Icc hL
  have hV : IntervalIntegrable (fun x => p.V x ^ 2) volume 0 L :=
    (p.continuous_V.pow 2).intervalIntegrable_of_Icc hL
  have hFV : IntervalIntegrable (fun x => F x * p.V x) volume 0 L :=
    (hF.mul p.continuous_V).intervalIntegrable_of_Icc hL
  rw [intervalIntegral.integral_sub (hD.add (hV.const_mul mu)) hFV,
    intervalIntegral.integral_add hD (hV.const_mul mu), intervalIntegral.integral_const_mul] at hi
  simpa using sub_eq_zero.mp (by simpa using hi)

/-- The signed L2 resolvent estimate follows from its energy and Young's
inequality. Both source and solution may change sign. -/
theorem l2_bound (p : Profile L mu F) (hL : 0 ≤ L) (hmu : 0 < mu)
    (hF : ContinuousOn F (Icc 0 L)) :
    mu ^ 2 * (∫ x in (0 : ℝ)..L, p.V x ^ 2) ≤ ∫ x in (0 : ℝ)..L, F x ^ 2 := by
  have hD : 0 ≤ ∫ x in (0 : ℝ)..L, p.dV x ^ 2 := intervalIntegral.integral_nonneg hL (fun x _ => sq_nonneg (p.dV x))
  have hE := p.energy hL hF
  have hF2 : IntervalIntegrable (fun x => F x ^ 2) volume 0 L :=
    (hF.pow 2).intervalIntegrable_of_Icc hL
  have hV2 : IntervalIntegrable (fun x => p.V x ^ 2) volume 0 L :=
    (p.continuous_V.pow 2).intervalIntegrable_of_Icc hL
  have hFV : IntervalIntegrable (fun x => F x * p.V x) volume 0 L :=
    (hF.mul p.continuous_V).intervalIntegrable_of_Icc hL
  have hY : 2 * mu * (∫ x in (0 : ℝ)..L, F x * p.V x) ≤
      (∫ x in (0 : ℝ)..L, F x ^ 2) + mu ^ 2 * (∫ x in (0 : ℝ)..L, p.V x ^ 2) := by
    have h := intervalIntegral.integral_mono_on hL (hFV.const_mul (2 * mu))
      (hF2.add (hV2.const_mul (mu ^ 2))) (fun x _ => by nlinarith [sq_nonneg (F x - mu * p.V x)])
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hF2
      (hV2.const_mul (mu ^ 2)), intervalIntegral.integral_const_mul] at h
    exact h
  nlinarith [mul_nonneg hmu.le hD]


/-- A bounded signed source gives a signed-response L1 estimate. -/
theorem l1_bound (p : Profile L mu F) (hL : 0 < L) (hmu : 0 < mu)
    (hF : ContinuousOn F (Icc 0 L)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Icc 0 L, |F x| ≤ B) :
    (∫ x in (0 : ℝ)..L, |p.V x|) ≤ L * B / mu := by
  have hF2 : (∫ x in (0 : ℝ)..L, F x ^ 2) ≤ L * B ^ 2 := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hL.le
      ((hF.pow 2).intervalIntegrable_of_Icc hL.le) (intervalIntegrable_const (c := B ^ 2))
      (fun x hx => by
        change F x ^ 2 ≤ B ^ 2
        nlinarith [hbound x hx, sq_abs (F x), abs_nonneg (F x)])
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm, Pi.pow_apply] using h
  have hV := (p.l2_bound hL.le hmu hF).trans hF2
  have hcs := SpikeEstimates.integral_abs_sq_le hL p.continuous_V
  have hI0 : 0 ≤ ∫ x in (0 : ℝ)..L, |p.V x| :=
    intervalIntegral.integral_nonneg hL.le fun x _ => abs_nonneg _
  have hsq : (mu * (∫ x in (0 : ℝ)..L, |p.V x|)) ^ 2 ≤ (L * B) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcs (sq_nonneg mu),
      mul_le_mul_of_nonneg_left hV hL.le]
  apply (le_div_iff₀ hmu).2
  nlinarith [mul_nonneg hmu.le hI0, mul_nonneg hL.le hB]

/-- The derivative is bounded uniformly, by FTC and the L1 estimate. -/
theorem derivative_bound (p : Profile L mu F) (hL : 0 < L) (hmu : 0 < mu)
    (hF : ContinuousOn F (Icc 0 L)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Icc 0 L, |F x| ≤ B) :
    ∀ x ∈ Icc 0 L, |p.dV x| ≤ 2 * L * B := by
  have hw : ContinuousOn (fun x => mu * |p.V x| + B) (Icc 0 L) :=
    (continuousOn_const.mul p.continuous_V.abs).add continuousOn_const
  have hw0 : ∀ x ∈ Icc 0 L, 0 ≤ mu * |p.V x| + B := fun x _ =>
    add_nonneg (mul_nonneg hmu.le (abs_nonneg _)) hB
  have hdb : ∀ x ∈ Ioo 0 L, |mu * p.V x - F x| ≤ mu * |p.V x| + B := by
    intro x hx
    calc |mu * p.V x - F x| ≤ |mu * p.V x| + |F x| := by simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (mu * p.V x) 0 (F x))
      _ ≤ mu * |p.V x| + B := by
        rw [abs_mul, abs_of_pos hmu]
        exact add_le_add le_rfl (hbound x (Ioo_subset_Icc_self hx))
  have hi : (∫ x in (0 : ℝ)..L, mu * |p.V x| + B) ≤ 2 * L * B := by
    rw [intervalIntegral.integral_add
      ((p.continuous_V.abs.intervalIntegrable_of_Icc hL.le).const_mul mu)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    have hI := mul_le_mul_of_nonneg_left (p.l1_bound hL hmu hF hB hbound) hmu.le
    have hcancel : mu * (L * B / mu) = L * B := by field_simp
    rw [hcancel] at hI
    linarith
  intro x hx
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have hupper := SpikeEstimates.le_add_integral_of_abs_deriv_le
    p.continuous_dV p.equation hw hw0 hdb x hx 0 h0
  have hlower := SpikeEstimates.le_add_integral_of_abs_deriv_le
    p.continuous_dV p.equation hw hw0 hdb 0 h0 x hx
  rw [p.neumann_left] at hupper hlower
  exact abs_le.mpr ⟨by linarith, by linarith⟩


/-- A coarse uniform response bound, sufficient for perturbation estimates.
It uses a point at or below the average absolute value and the FTC bound. -/
theorem value_bound (p : Profile L mu F) (hL : 0 < L) (hmu : 0 < mu)
    (hF : ContinuousOn F (Icc 0 L)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Icc 0 L, |F x| ≤ B) :
    ∀ x ∈ Icc 0 L, |p.V x| ≤ B / mu + 2 * L ^ 2 * B := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le)
    p.continuous_V.abs
  have hlow := IntervalMoments.le_integral_of_le hL.le p.continuous_V.abs
    (fun z hz => hmin hz)
  have hsmall : |p.V y| ≤ B / mu := by
    apply le_of_mul_le_mul_left (a := L) _ hL
    calc L * |p.V y| ≤ ∫ x in (0 : ℝ)..L, |p.V x| := hlow
      _ ≤ L * (B / mu) := by simpa only [mul_div_assoc] using p.l1_bound hL hmu hF hB hbound
  have hdb := p.derivative_bound hL hmu hF hB hbound
  have hW0 : ∀ x ∈ Icc 0 L, 0 ≤ 2 * L * B := fun _ _ => by positivity
  intro x hx
  have hu := SpikeEstimates.le_add_integral_of_abs_deriv_le p.continuous_V p.derivative_V
    (continuousOn_const (c := 2 * L * B)) hW0
    (fun z hz => hdb z (Ioo_subset_Icc_self hz)) x hx y hy
  have hl := SpikeEstimates.le_add_integral_of_abs_deriv_le p.continuous_V p.derivative_V
    (continuousOn_const (c := 2 * L * B)) hW0
    (fun z hz => hdb z (Ioo_subset_Icc_self hz)) y hy x hx
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hu hl
  exact abs_le.mpr ⟨by nlinarith [neg_abs_le (p.V y)], by nlinarith [le_abs_self (p.V y)]⟩

/-- A source amplitude controls the actual response and its first derivative
in the physical interval coordinate. -/
theorem c1_bound (p : Profile L mu F) (hL : 0 < L) (hmu : 0 < mu)
    (hF : ContinuousOn F (Icc 0 L)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Icc 0 L, |F x| ≤ B) :
    ∀ x ∈ Icc 0 L, |p.V x| + |p.dV x| ≤ (1 / mu + 2 * L ^ 2 + 2 * L) * B := by
  intro x hx
  have h0 := p.value_bound hL hmu hF hB hbound x hx
  have h1 := p.derivative_bound hL hmu hF hB hbound x hx
  calc |p.V x| + |p.dV x| ≤ B / mu + 2 * L ^ 2 * B + 2 * L * B := add_le_add h0 h1
    _ = (1 / mu + 2 * L ^ 2 + 2 * L) * B := by ring

end Profile
end
end ChemotaxisBifurcation.SignedEllipticEnergy
