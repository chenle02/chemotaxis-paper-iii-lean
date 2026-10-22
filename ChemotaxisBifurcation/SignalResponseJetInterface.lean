module
public import ChemotaxisBifurcation.SignalResponseJet

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.SignalResponseJetInterface
open Real Set MeasureTheory Filter Topology
noncomputable section

/-- The actual normalized modal derivative of a nonlinear Neumann response,
in Mathlib-only vocabulary. Response differentiability is a conclusion. -/
theorem actual_modal_derivative (L mu nu gamma uStar vStar : ℝ)
    (hL : 0 < L) (hu : 0 < uStar) (hmu : 0 < mu)
    (hsig : mu*vStar=nu*uStar^gamma)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc 0 L)) (k : ℕ)
    (V dV : ℝ → ℝ → ℝ)
    (hsol : ∀ᶠ t in 𝓝 (0 : ℝ),
      AbsolutelyContinuousOnInterval (V t) 0 L ∧
      (∀ x ∈ Ioo 0 L, HasDerivAt (V t) (dV t x) x) ∧
      AbsolutelyContinuousOnInterval (dV t) 0 L ∧ dV t 0=0 ∧ dV t L=0 ∧
      ∀ x ∈ Ioo 0 L, deriv (dV t) x-mu*(vStar+V t x)+nu*(uStar+t*w x)^gamma=0) :
    let coeff := fun f : ℝ → ℝ =>
      (if k=0 then 1/L else 2/L)*(∫ x in (0 : ℝ)..L, f x*cos ((k:ℝ)*Real.pi*x/L))
    HasDerivAt (fun t => coeff (V t))
      ((mu*gamma*vStar/uStar)/(mu+(k*Real.pi/L)^2)*coeff w) 0 := by
  let p : PhysicalParams := {
    a := 0, b := 0, alpha := 1, m := 1, gamma := gamma, nu := nu, mu := mu,
    uStar := uStar, vStar := vStar }
  have hp : p.SignalEquilibrium := hsig
  have hs : ∀ᶠ t in 𝓝 (0 : ℝ), CosineCoefficients.NeumannW21 L (V t) (dV t) ∧
      ∀ x ∈ Ioo 0 L, deriv (dV t) x-p.mu*(p.vStar+V t x)+p.nu*(p.uStar+t*w x)^p.gamma=0 := by
    filter_upwards [hsol] with t ht
    exact ⟨⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2.1⟩,ht.2.2.2.2.2⟩
  have h := SignalResponseJet.actual_response_hasDerivAt p hL hu hmu hp w hw k V dV hs
  simpa only [signalMode1,mobilityScaledTaylor,p,CosineCoefficients.cosineCoeff] using h

end
end ChemotaxisBifurcation.SignalResponseJetInterface
