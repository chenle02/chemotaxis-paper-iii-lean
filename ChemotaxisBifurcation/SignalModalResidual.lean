module
public import ChemotaxisBifurcation.EllipticProjection
public import ChemotaxisBifurcation.SignalTaylorRemainder

@[expose] public section

/-!
# The actual nonlinear signal's modal Taylor residual

The modal residual is the coefficient of the actual signal perturbation minus
the linear/quadratic/cubic population-source coefficients divided by the
elliptic denominator. The elliptic equation and the actual real-power Taylor
theorem identify and bound this residual; neither a projected balance nor a
Taylor-source bound is assumed. This is a result about given classical
profiles, independent of center-manifold existence.
-/

set_option autoImplicit false
namespace ChemotaxisBifurcation.SignalModalResidual
open Real Set MeasureTheory CosineCoefficients
noncomputable section

def sourceRemainder (p : PhysicalParams) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  p.nu * (p.uStar + U x) ^ p.gamma - p.nu * p.uStar ^ p.gamma -
    (rawTaylorData p 0).Cprime * U x -
    (rawTaylorData p 0).Csecond * U x ^ 2 -
    (rawTaylorData p 0).Cthird * U x ^ 3

def modalResidual (p : PhysicalParams) (L : ℝ) (U V : ℝ → ℝ) (k : ℕ) : ℝ :=
  cosineCoeff L V k -
    ((rawTaylorData p 0).Cprime * cosineCoeff L U k +
      (rawTaylorData p 0).Csecond * cosineCoeff L (fun x => U x ^ 2) k +
      (rawTaylorData p 0).Cthird * cosineCoeff L (fun x => U x ^ 3) k) /
        (p.mu + (k * Real.pi / L) ^ 2)

/-- Linearity restricted to actual integrable functions, avoiding any use of
linearity of totalized integrals without their integrability hypotheses. -/
theorem cosineCoeff_add {L : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 L) (hg : IntervalIntegrable g volume 0 L)
    (k : ℕ) : cosineCoeff L (fun x => f x + g x) k =
      cosineCoeff L f k + cosineCoeff L g k := by
  have hc : Continuous (fun x : ℝ => cos (k * Real.pi * x / L)) := by fun_prop
  unfold cosineCoeff
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add (hf.mul_continuousOn hc.continuousOn)
    (hg.mul_continuousOn hc.continuousOn)]
  ring

theorem cosineCoeff_const_mul (L c : ℝ) (f : ℝ → ℝ) (k : ℕ) :
    cosineCoeff L (fun x => c * f x) k = c * cosineCoeff L f k := by
  unfold cosineCoeff
  rw [show (fun x => c * f x * cos (k * Real.pi * x / L)) =
      (fun x => c * (f x * cos (k * Real.pi * x / L))) by funext x; ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Identification of the actual modal residual with the resolvent of its
actual real-power source residual. -/
theorem modalResidual_eq_resolvent (p : PhysicalParams) {L : ℝ}
    (hL : 0 < L) (hmu : 0 < p.mu) {U V dV : ℝ → ℝ}
    (hU : ContinuousOn U (Icc 0 L)) (hV : NeumannW21 L V dV)
    (hbase : ∀ x ∈ Icc 0 L, 0 < p.uStar + U x)
    (heq : ∀ x ∈ Ioo 0 L,
      deriv dV x - p.mu * V x +
        (p.nu * (p.uStar + U x) ^ p.gamma - p.nu * p.uStar ^ p.gamma) = 0)
    (k : ℕ) :
    modalResidual p L U V k =
      ModalRemainder.signalRemainder L p.mu (sourceRemainder p U) k := by
  let F := fun x => p.nu * (p.uStar + U x) ^ p.gamma - p.nu * p.uStar ^ p.gamma
  let P := fun x => (rawTaylorData p 0).Cprime * U x +
    (rawTaylorData p 0).Csecond * U x ^ 2 + (rawTaylorData p 0).Cthird * U x ^ 3
  have hFc : ContinuousOn F (Icc 0 L) :=
    (continuousOn_const.mul ((continuousOn_const.add hU).rpow_const
      (fun x hx => Or.inl (hbase x hx).ne'))).sub continuousOn_const
  have hPc : ContinuousOn P (Icc 0 L) :=
    ((continuousOn_const.mul hU).add (continuousOn_const.mul (hU.pow 2))).add
      (continuousOn_const.mul (hU.pow 3))
  have hRc : ContinuousOn (sourceRemainder p U) (Icc 0 L) := by
    apply (hFc.sub hPc).congr
    intro x _
    dsimp [F, P, sourceRemainder]
    ring
  have hfun : F = fun x => P x + sourceRemainder p U x := by
    funext x; dsimp [F, P, sourceRemainder]; ring
  have hcoeff := EllipticProjection.projected_balance hL hV heq k
  change (p.mu + (k * Real.pi / L) ^ 2) * cosineCoeff L V k = cosineCoeff L F k at hcoeff
  rw [hfun, cosineCoeff_add (hPc.intervalIntegrable_of_Icc hL.le)
    (hRc.intervalIntegrable_of_Icc hL.le)] at hcoeff
  have hi1 : IntervalIntegrable U volume 0 L := hU.intervalIntegrable_of_Icc hL.le
  have hi2 : IntervalIntegrable (fun x => U x ^ 2) volume 0 L :=
    (hU.pow 2).intervalIntegrable_of_Icc hL.le
  have hi3 : IntervalIntegrable (fun x => U x ^ 3) volume 0 L :=
    (hU.pow 3).intervalIntegrable_of_Icc hL.le
  have hp : cosineCoeff L P k =
      (rawTaylorData p 0).Cprime * cosineCoeff L U k +
        (rawTaylorData p 0).Csecond * cosineCoeff L (fun x => U x ^ 2) k +
        (rawTaylorData p 0).Cthird * cosineCoeff L (fun x => U x ^ 3) k := by
    dsimp only [P]
    rw [cosineCoeff_add ((hi1.const_mul _).add (hi2.const_mul _)) (hi3.const_mul _),
      cosineCoeff_add (hi1.const_mul _) (hi2.const_mul _),
      cosineCoeff_const_mul, cosineCoeff_const_mul, cosineCoeff_const_mul]
  rw [hp] at hcoeff
  unfold modalResidual ModalRemainder.signalRemainder
  have hd : p.mu + (k * Real.pi / L) ^ 2 ≠ 0 := by positivity
  apply (eq_div_iff hd).2
  rw [sub_mul, div_mul_cancel₀ _ hd]
  linarith

/-- Actual all-mode quartic residual bounds for the nonlinear elliptic
signal equation. The constant is chosen before the domain, profiles and norm
variable, and depends only on the fixed physical source parameters. -/
theorem modalResidual_quartic (p : PhysicalParams) (hu : 0 < p.uStar)
    (hmu : 0 < p.mu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L N : ℝ) (U V dV : ℝ → ℝ),
      0 < L → N ≤ p.uStar / 2 → (∀ x ∈ Icc 0 L, |U x| ≤ N) →
      ContinuousOn U (Icc 0 L) → NeumannW21 L V dV →
      (∀ x ∈ Ioo 0 L, deriv dV x - p.mu * V x +
        (p.nu * (p.uStar + U x) ^ p.gamma - p.nu * p.uStar ^ p.gamma) = 0) →
      |modalResidual p L U V 0| ≤ C * N ^ 4 / p.mu ∧
        ∀ k : ℕ, k ≠ 0 → |modalResidual p L U V k| ≤
          2 * (C * N ^ 4) / (p.mu + (k * Real.pi / L) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := signalSource_field_quartic_bound p hu
  refine ⟨C, hC, ?_⟩
  intro L N U V dV hL hN hUN hUc hV heq
  have hbase : ∀ x ∈ Icc 0 L, 0 < p.uStar + U x := by
    intro x hx
    have h := (abs_le.mp (hUN x hx)).1
    linarith
  simp_rw [modalResidual_eq_resolvent p hL hmu hUc hV hbase heq]
  exact ModalRemainder.signalRemainder_quartic hL hmu (hbound L N U hN hUN)

/-- The actual nonlinear signal's modal residual sequence is summable;
the common source bound is derived from the real-power Taylor theorem. -/
theorem summable_modalResidual (p : PhysicalParams) (hu : 0 < p.uStar)
    {L N : ℝ} (hL : 0 < L) (hmu : 0 < p.mu) {U V dV : ℝ → ℝ}
    (hN : N ≤ p.uStar / 2) (hUN : ∀ x ∈ Icc 0 L, |U x| ≤ N)
    (hUc : ContinuousOn U (Icc 0 L)) (hV : NeumannW21 L V dV)
    (heq : ∀ x ∈ Ioo 0 L, deriv dV x - p.mu * V x +
      (p.nu * (p.uStar + U x) ^ p.gamma - p.nu * p.uStar ^ p.gamma) = 0) :
    Summable fun k => ‖modalResidual p L U V k‖ := by
  obtain ⟨C, hC, hbound⟩ := signalSource_field_quartic_bound p hu
  have hbase : ∀ x ∈ Icc 0 L, 0 < p.uStar + U x := by
    intro x hx
    have h := (abs_le.mp (hUN x hx)).1
    linarith
  simp_rw [modalResidual_eq_resolvent p hL hmu hUc hV hbase heq]
  exact ModalRemainder.summable_norm_signalRemainder hL hmu (by positivity)
    (hbound L N U hN hUN)

/-- Physical equilibrium cancellation derives the perturbed equation from
the full signal equation, retaining the actual physical fields. -/
theorem modalResidual_eq_of_physical_signal (p : PhysicalParams)
    (hsig : p.SignalEquilibrium) {L : ℝ} (hL : 0 < L) (hmu : 0 < p.mu)
    {U V dV : ℝ → ℝ} (hUc : ContinuousOn U (Icc 0 L)) (hV : NeumannW21 L V dV)
    (hbase : ∀ x ∈ Icc 0 L, 0 < p.uStar + U x)
    (heq : ∀ x ∈ Ioo 0 L, deriv dV x - p.mu * (p.vStar + V x) +
      p.nu * (p.uStar + U x) ^ p.gamma = 0) (k : ℕ) :
    modalResidual p L U V k =
      ModalRemainder.signalRemainder L p.mu (sourceRemainder p U) k := by
  apply modalResidual_eq_resolvent p hL hmu hUc hV hbase
  intro x hx
  unfold PhysicalParams.SignalEquilibrium at hsig
  linarith [heq x hx]

end
end ChemotaxisBifurcation.SignalModalResidual
