module
public import ChemotaxisBifurcation.SignalWeakTesting

/-!
# Polynomial source tests from the actual signal equation

The classical signal equation, Neumann data and uniform constant C1 limits
yield all polynomial-weighted source limits through integration by parts.
-/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
namespace ChemotaxisBifurcation.SignalPolynomialTesting
noncomputable section

/-- Multiplication by a fixed continuous weight preserves uniform convergence
on the compact interval. -/
theorem uniform_mul_fixed {L : ℝ} {f : ℕ → ℝ → ℝ} {F w : ℝ → ℝ}
    (_hL : 0 ≤ L) (hw : ContinuousOn w (Icc 0 L))
    (hf : TendstoUniformlyOn f F atTop (Icc 0 L)) :
    TendstoUniformlyOn (fun n x => f n x * w x) (fun x => F x * w x) atTop (Icc 0 L) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro e he
  have hden : 0 < |C| + 1 := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf (e / (|C| + 1)) (div_pos he hden)]
    with n hn
  intro x hx
  have hnx := hn x hx
  have hwb : |w x| ≤ |C| := (hC x hx).trans (le_abs_self C)
  rw [Real.dist_eq] at hnx ⊢
  rw [← sub_mul, abs_mul]
  calc |F x - f n x| * |w x| ≤ |F x - f n x| * |C| :=
        mul_le_mul_of_nonneg_left hwb (abs_nonneg _)
    _ ≤ |F x - f n x| * (|C| + 1) := by nlinarith [abs_nonneg (F x - f n x)]
    _ < e := (lt_div_iff₀ hden).mp hnx

/-- Actual signal equation tested against a polynomial, including Neumann
boundary cancellation. -/
theorem signal_polynomial_identity (L mu nu gamma : ℝ) (u v dv ddv : ℝ → ℝ)
    (P : Polynomial ℝ) (hL : 0 ≤ L) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hdv : ContinuousOn dv (Icc 0 L))
    (hderiv2 : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (heq : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0) :
    nu * (∫ x in (0 : ℝ)..L, u x ^ gamma * P.eval x) =
      mu * (∫ x in (0 : ℝ)..L, v x * P.eval x) +
        ∫ x in (0 : ℝ)..L, dv x * P.derivative.eval x := by
  have hP : Continuous (fun x : ℝ => P.eval x) := P.continuous
  have hDP : Continuous (fun x : ℝ => P.derivative.eval x) := P.derivative.continuous
  have hcu := hu.rpow_const (p := gamma) (fun _ _ => Or.inr hgamma)
  have hcvP : ContinuousOn (fun x => v x * P.eval x) (Icc 0 L) := hv.mul hP.continuousOn
  have hcuP : ContinuousOn (fun x => u x ^ gamma * P.eval x) (Icc 0 L) := hcu.mul hP.continuousOn
  have hcdP : ContinuousOn (fun x => dv x * P.derivative.eval x) (Icc 0 L) := hdv.mul hDP.continuousOn
  have hci : ContinuousOn (fun x =>
      (mu * (v x * P.eval x) - nu * (u x ^ gamma * P.eval x)) + dv x * P.derivative.eval x)
      (Icc 0 L) := ((hcvP.const_smul mu).sub (hcuP.const_smul nu)).add hcdP
  have ht : (∫ x in (0 : ℝ)..L,
      ((mu * (v x * P.eval x) - nu * (u x ^ gamma * P.eval x)) + dv x * P.derivative.eval x)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL
      (f := fun x => dv x * P.eval x) (hdv.mul hP.continuousOn)
      (fun x hx => ?_) (hci.intervalIntegrable_of_Icc hL)]
    · simp only [hbc0, hbcL, zero_mul, sub_self]
    · convert (hderiv2 x hx).mul (P.hasDerivAt x) using 1
      linear_combination -(P.eval x) * heq x hx
  rw [intervalIntegral.integral_add
      (((hcvP.intervalIntegrable_of_Icc hL).const_mul mu).sub
        ((hcuP.intervalIntegrable_of_Icc hL).const_mul nu))
      (hcdP.intervalIntegrable_of_Icc hL),
    intervalIntegral.integral_sub ((hcvP.intervalIntegrable_of_Icc hL).const_mul mu)
      ((hcuP.intervalIntegrable_of_Icc hL).const_mul nu),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at ht
  linarith

/-- Constant C1 signal convergence implies every polynomial-tested source
limit directly from the actual signal equation. -/
theorem polynomial_source_test_tendsto (L mu nu gamma c : ℝ)
    (u v dv ddv : ℕ → ℝ → ℝ) (hL : 0 ≤ L) (hnu : nu ≠ 0) (hgamma : 0 ≤ gamma)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (heq : ∀ n x, x ∈ Ioo 0 L → ddv n x - mu * v n x + nu * u n x ^ gamma = 0)
    (hbc0 : ∀ n, dv n 0 = 0) (hbcL : ∀ n, dv n L = 0)
    (hvlim : TendstoUniformlyOn v (fun _ => nu / mu * c) atTop (Icc 0 L))
    (hdvlim : TendstoUniformlyOn dv (fun _ => 0) atTop (Icc 0 L)) (hmu : mu ≠ 0) :
    ∀ P : Polynomial ℝ,
      Tendsto (fun n => ∫ x in (0 : ℝ)..L, u n x ^ gamma * P.eval x) atTop
        (𝓝 (∫ x in (0 : ℝ)..L, c * P.eval x)) := by
  intro P
  have hPv := uniform_mul_fixed hL P.continuous.continuousOn hvlim
  have hPd := uniform_mul_fixed hL P.derivative.continuous.continuousOn hdvlim
  rw [← uIcc_of_le hL] at hPv hPd
  have hlimv := hPv.tendsto_intervalIntegral_of_continuousOn (μ := volume)
    (Eventually.of_forall fun n => by
      rw [uIcc_of_le hL]
      exact (hv n).mul P.continuous.continuousOn)
  have hlimd := hPd.tendsto_intervalIntegral_of_continuousOn (μ := volume)
    (Eventually.of_forall fun n => by
      rw [uIcc_of_le hL]
      exact (hdv n).mul P.derivative.continuous.continuousOn)
  have hlim := (((tendsto_const_nhds (x := mu)).mul hlimv).add hlimd).div_const nu
  have he : (fun n => ∫ x in (0 : ℝ)..L, u n x ^ gamma * P.eval x) =
      (fun n => (mu * (∫ x in (0 : ℝ)..L, v n x * P.eval x) +
        ∫ x in (0 : ℝ)..L, dv n x * P.derivative.eval x) / nu) := by
    funext n
    apply (eq_div_iff hnu).mpr
    have hh := signal_polynomial_identity L mu nu gamma (u n) (v n) (dv n) (ddv n) P
      hL hgamma (hu n) (hv n) (hdv n) (hderiv2 n) (heq n) (hbc0 n) (hbcL n)
    linarith
  rw [he]
  have htarget : (mu * (∫ x in (0 : ℝ)..L, nu / mu * c * P.eval x) +
      ∫ x in (0 : ℝ)..L, (0 : ℝ) * P.derivative.eval x) / nu =
      ∫ x in (0 : ℝ)..L, c * P.eval x := by
    simp only [zero_mul, intervalIntegral.integral_zero, add_zero]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    field_simp
  rwa [htarget] at hlim
end
end ChemotaxisBifurcation.SignalPolynomialTesting
