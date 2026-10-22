module
public import ChemotaxisBifurcation.PrimitiveDerivatives
public import ChemotaxisBifurcation.QuadraticJet

@[expose] public section

/-!
# Signal-source derivatives and elliptic modal coefficients

This module supplies actual positive-base derivative witnesses for Equation
2.10 and denominator-aware scalar residuals for Equation 2.11.  Full elliptic
regularity is outside this finite modal layer.
-/

namespace ChemotaxisBifurcation

open Filter
open scoped Topology

noncomputable def signalSourceFirst (nu gamma x : ℝ) : ℝ :=
  nu * gamma * x ^ (gamma - 1)

noncomputable def signalSourceSecond (nu gamma x : ℝ) : ℝ :=
  nu * gamma * (gamma - 1) * x ^ (gamma - 2)

theorem signalSourceFirst_hasDerivAt
    (nu gamma u : ℝ) (hu : 0 < u) :
    HasDerivAt (signalSourceFirst nu gamma)
      (nu * gamma * (gamma - 1) * u ^ (gamma - 2)) u := by
  have hexp : gamma - 1 - 1 = gamma - 2 := by ring
  have h := (rpow_hasDerivAt (gamma - 1) u hu).const_mul (nu * gamma)
  rw [hexp] at h
  have hfun :
      (fun _ : ℝ => nu * gamma) * (fun y => y ^ (gamma - 1)) =
        signalSourceFirst nu gamma := by
    funext y
    simp [signalSourceFirst]
  rw [← hfun]
  have hv : (nu * gamma) * ((gamma - 1) * u ^ (gamma - 2)) =
      nu * gamma * (gamma - 1) * u ^ (gamma - 2) := by ring
  rw [← hv]
  exact h

theorem signalSourceSecond_hasDerivAt
    (nu gamma u : ℝ) (hu : 0 < u) :
    HasDerivAt (signalSourceSecond nu gamma)
      (nu * gamma * (gamma - 1) * (gamma - 2) *
        u ^ (gamma - 3)) u := by
  have hexp : gamma - 2 - 1 = gamma - 3 := by ring
  have h := (rpow_hasDerivAt (gamma - 2) u hu).const_mul
    (nu * gamma * (gamma - 1))
  rw [hexp] at h
  have hfun :
      (fun _ : ℝ => nu * gamma * (gamma - 1)) *
          (fun y => y ^ (gamma - 2)) =
        signalSourceSecond nu gamma := by
    funext y
    simp [signalSourceSecond]
  rw [← hfun]
  have hv : (nu * gamma * (gamma - 1)) *
      ((gamma - 2) * u ^ (gamma - 3)) =
      nu * gamma * (gamma - 1) * (gamma - 2) * u ^ (gamma - 3) := by ring
  rw [← hv]
  exact h

theorem signalSource_deriv_eq_first
    (nu gamma x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => nu * y ^ gamma) x = signalSourceFirst nu gamma x := by
  rw [(signal_source_hasDerivAt nu gamma x hx).deriv]
  rfl

/-- Equation 2.10 coefficients are the first three derivative values with
factorials `1`, `1/2`, and `1/6`. -/
theorem rawTaylor_signal_coefficients
    (p : PhysicalParams) (hu : 0 < p.uStar) :
    (rawTaylorData p 0).Cprime = signalSourceFirst p.nu p.gamma p.uStar ∧
    2 * (rawTaylorData p 0).Csecond =
      signalSourceSecond p.nu p.gamma p.uStar ∧
    6 * (rawTaylorData p 0).Cthird =
      p.nu * p.gamma * (p.gamma - 1) * (p.gamma - 2) *
        p.uStar ^ (p.gamma - 3) := by
  refine ⟨rfl, ?_, ?_⟩ <;>
    simp [rawTaylorData, signalSourceFirst, signalSourceSecond] <;> ring

theorem signalMode1_residual
    (p : PhysicalParams) (x : ℝ) (hden : p.mu + x ≠ 0) :
    (p.mu + x) * signalMode1 p x =
      (mobilityScaledTaylor p 0).Cprime := by
  unfold signalMode1
  field_simp [hden]

theorem signalMode2_residual
    (p : PhysicalParams) (x : ℝ) (hden : p.mu + x ≠ 0) :
    2 * (p.mu + x) * signalMode2 p x =
      (mobilityScaledTaylor p 0).Csecond := by
  unfold signalMode2
  field_simp [hden]

theorem signalMode3_residual
    (p : PhysicalParams) (x : ℝ) (hden : p.mu + x ≠ 0) :
    4 * (p.mu + x) * signalMode3 p x =
      (mobilityScaledTaylor p 0).Cthird := by
  unfold signalMode3
  field_simp [hden]

end ChemotaxisBifurcation
