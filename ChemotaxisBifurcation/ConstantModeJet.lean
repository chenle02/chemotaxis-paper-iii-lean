module
public import ChemotaxisBifurcation.QuadraticJet

@[expose] public section

/-!
# Constant-mode quadratic graph coefficients (Eq. 2.33, label `E:a_0,i`)

In the non-minimal model the manuscript compares two expressions for `du₀/dt`
and concludes
`a_{0,1} = -bA''/(2aα) = -(1+α)/(4u*)` and `a_{0,2} = 0`.
The comparison is the vanishing of the degree-two residual
`(-aα)(a_{0,1} A² + a_{0,2} η A + a_{0,3} η²) - (bA''/2) A²` for all amplitudes
`A` and sensitivities `η`; that invariance identity is the analytic input and
stays a hypothesis here.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.ConstantModeJet

noncomputable section

/-- The residual identity forces `a_{0,1} = logisticA0 = -bA''/(2aα)` (scaled
coefficient) and `a_{0,2} = a_{0,3} = 0`. -/
theorem constantMode_coefficients (p : PhysicalParams) (hd : p.logisticSlope ≠ 0)
    (a01 a02 a03 : ℝ)
    (hres : ∀ amplitude eta : ℝ,
      quadraticJetResidual (-p.logisticSlope) ((mobilityScaledTaylor p 0).bAsecond / 2)
        a01 a02 a03 amplitude eta = 0) :
    a01 = logisticA0 p ∧ a02 = 0 ∧ a03 = 0 := by
  obtain ⟨h1, h2, h3⟩ :=
    coefficients_of_quadratic_jet_residual _ _ a01 a02 a03 (neg_ne_zero.mpr hd) hres
  refine ⟨?_, h2, h3⟩
  rw [h1, logisticA0]
  field_simp

/-- The second equality of Eq. 2.33: `-bA''/(2aα) = -(1+α)/(4u*)`. -/
theorem logisticA0_eq_explicit (p : PhysicalParams)
    (ha : 0 < p.a) (halpha : 0 < p.alpha) (hu : 0 < p.uStar) :
    logisticA0 p = -(1 + p.alpha) / (4 * p.uStar) := by
  unfold logisticA0 PhysicalParams.logisticSlope
  simp only [mobilityScaledTaylor]
  field_simp
  ring

/-- Eq. 2.33 in the non-minimal model, stated with the physical `b A''`: any
constant-mode coefficients satisfying the invariance identity are
`a_{0,1} = -bA''/(2aα) = -(1+α)/(4u*)` and `a_{0,2} = 0`. -/
theorem a_0_display (p : PhysicalParams) (hp : p.LogisticAdmissible)
    (a01 a02 a03 : ℝ)
    (hres : ∀ amplitude eta : ℝ,
      quadraticJetResidual (-(p.a * p.alpha)) (p.b * (rawTaylorData p 0).Asecond / 2)
        a01 a02 a03 amplitude eta = 0) :
    a01 = -(p.b * (rawTaylorData p 0).Asecond) / (2 * (p.a * p.alpha)) ∧
      a01 = -(1 + p.alpha) / (4 * p.uStar) ∧ a02 = 0 := by
  obtain ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, hlog, hsig⟩ := hp
  have hd : p.logisticSlope ≠ 0 := by
    unfold PhysicalParams.logisticSlope
    positivity
  have hscaled := bAsecond_eq_scaled p hu hlog
  have hres' : ∀ amplitude eta : ℝ,
      quadraticJetResidual (-p.logisticSlope) ((mobilityScaledTaylor p 0).bAsecond / 2)
        a01 a02 a03 amplitude eta = 0 := by
    intro A e
    rw [← hscaled]
    simpa [PhysicalParams.logisticSlope] using hres A e
  obtain ⟨h1, h2, -⟩ := constantMode_coefficients p hd a01 a02 a03 hres'
  have hexp := logisticA0_eq_explicit p ha halpha hu
  refine ⟨?_, h1.trans hexp, h2⟩
  rw [h1, logisticA0, ← hscaled, PhysicalParams.logisticSlope]

end

end ChemotaxisBifurcation.ConstantModeJet
