module
public import ChemotaxisBifurcation.SignalModalResidual
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.SignalResponseJet
open Real Set Filter Topology MeasureTheory CosineCoefficients Asymptotics
noncomputable section

/-- The three modal coefficients in the actual response to U=t*w. The
factors two and four convert the manuscript convolution convention back to
actual coefficients of the functions w squared and w cubed. -/
def responsePolynomial (p : PhysicalParams) (L : ℝ) (w : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  t * (signalMode1 p ((k*Real.pi/L)^2) * cosineCoeff L w k) +
  t^2 * (2*signalMode2 p ((k*Real.pi/L)^2) * cosineCoeff L (fun x => w x^2) k) +
  t^3 * (4*signalMode3 p ((k*Real.pi/L)^2) * cosineCoeff L (fun x => w x^3) k)

/-- Actual nonlinear elliptic response has this cubic jet, with a derived
quartic bound. No projected balance or response Taylor estimate is assumed. -/
theorem actual_response_quartic (p : PhysicalParams) {L : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hsig : p.SignalEquilibrium)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc 0 L)) (k : ℕ) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t : ℝ) (V dV : ℝ → ℝ), |t| ≤ radius → NeumannW21 L V dV →
      (∀ x ∈ Ioo 0 L, deriv dV x-p.mu*(p.vStar+V x)+p.nu*(p.uStar+t*w x)^p.gamma=0) →
      |cosineCoeff L V k-responsePolynomial p L w k t| ≤ C*|t|^4 := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  let D := max B 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨C,hC,hrem⟩ := SignalModalResidual.modalResidual_quartic p hu hmu
  have hden : 0 < p.mu+(k*Real.pi/L)^2 := by positivity
  refine ⟨p.uStar/(2*D),by positivity,2*C*D^4/(p.mu+(k*Real.pi/L)^2),by positivity,?_⟩
  intro t V dV ht hV heq
  have hN : |t| *D ≤ p.uStar/2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2*D)).mp ht
    nlinarith
  have hbound : ∀ x ∈ Icc 0 L, |t*w x| ≤ |t| *D := by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hB x hx).trans (le_max_left B 1)) (abs_nonneg _)
  have heq' : ∀ x ∈ Ioo 0 L, deriv dV x-p.mu*V x+
      (p.nu*(p.uStar+t*w x)^p.gamma-p.nu*p.uStar^p.gamma)=0 := by
    intro x hx
    unfold PhysicalParams.SignalEquilibrium at hsig
    linarith [heq x hx]
  have h := hrem L (|t| *D) (fun x => t*w x) V dV hL hN hbound
    (continuousOn_const.mul hw) hV heq'
  have he : SignalModalResidual.modalResidual p L (fun x => t*w x) V k =
      cosineCoeff L V k-responsePolynomial p L w k t := by
    have h2 : (fun x => (t*w x)^2) = (fun x => t^2*w x^2) := by funext x; ring
    have h3 : (fun x => (t*w x)^3) = (fun x => t^3*w x^3) := by funext x; ring
    unfold SignalModalResidual.modalResidual responsePolynomial
    rw [h2,h3,SignalModalResidual.cosineCoeff_const_mul,
      SignalModalResidual.cosineCoeff_const_mul,SignalModalResidual.cosineCoeff_const_mul,
      Cprime_eq_scaled p hu hsig,Csecond_eq_scaled p hu hsig,Cthird_eq_scaled p hu hsig]
    unfold signalMode1 signalMode2 signalMode3
    field_simp
  by_cases hk : k=0
  · subst k
    have hh := h.1
    rw [he] at hh
    norm_num only [Nat.cast_zero,zero_mul,zero_div,zero_pow,add_zero]
    calc |cosineCoeff L V 0-responsePolynomial p L w 0 t| ≤ C*(|t| *D)^4/p.mu := hh
      _ = C*D^4/p.mu*|t|^4 := by ring
      _ ≤ 2*(C*D^4/p.mu*|t|^4) := by nlinarith [show 0 ≤ C*D^4/p.mu*|t|^4 by positivity]
      _ = 2*C*D^4/p.mu*|t|^4 := by ring
  · have hh := h.2 k hk
    rw [he] at hh
    calc |cosineCoeff L V k-responsePolynomial p L w k t| ≤
        2*(C*(|t| *D)^4)/(p.mu+(k*Real.pi/L)^2) := hh
      _ = _ := by ring

/-- The first modal response derivative is derived from the actual nonlinear
elliptic equation. No differentiability of the response in t is a premise. -/
theorem actual_response_hasDerivAt (p : PhysicalParams) {L : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hsig : p.SignalEquilibrium)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc 0 L)) (k : ℕ)
    (V dV : ℝ → ℝ → ℝ)
    (hsol : ∀ᶠ t in 𝓝 (0 : ℝ), NeumannW21 L (V t) (dV t) ∧
      ∀ x ∈ Ioo 0 L, deriv (dV t) x-p.mu*(p.vStar+V t x)+p.nu*(p.uStar+t*w x)^p.gamma=0) :
    HasDerivAt (fun t => cosineCoeff L (V t) k)
      (signalMode1 p ((k*Real.pi/L)^2)*cosineCoeff L w k) 0 := by
  obtain ⟨radius,hr,C,hC,hjet⟩ := actual_response_quartic p hL hu hmu hsig w hw k
  let P := responsePolynomial p L w k
  let E := fun t => cosineCoeff L (V t) k-P t
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < radius :=
    (continuous_abs.tendsto (0 : ℝ)).eventually (Iio_mem_nhds (by simpa using hr))
  have hbound : ∀ᶠ t in 𝓝 (0 : ℝ), |E t| ≤ C*|t|^4 := by
    filter_upwards [hsmall,hsol] with t ht hs
    exact hjet t (V t) (dV t) ht.le hs.1 hs.2
  have he0 : E 0=0 := abs_eq_zero.mp (le_antisymm
    (by simpa using hbound.self_of_nhds) (abs_nonneg _))
  have hO : E =O[𝓝 (0 : ℝ)] (fun t : ℝ => t^4) :=
    IsBigO.of_bound C (by simpa only [Real.norm_eq_abs,abs_pow] using hbound)
  have ho : E =o[𝓝 (0 : ℝ)] (fun t : ℝ => t) :=
    hO.trans_isLittleO (isLittleO_pow_id (by norm_num : 1 < 4))
  have hdE : HasDerivAt E 0 0 := HasDerivAt.of_isLittleO (by simpa [he0] using ho)
  let A := signalMode1 p ((k*Real.pi/L)^2)*cosineCoeff L w k
  let B := 2*signalMode2 p ((k*Real.pi/L)^2)*cosineCoeff L (fun x => w x^2) k
  let D := 4*signalMode3 p ((k*Real.pi/L)^2)*cosineCoeff L (fun x => w x^3) k
  have hdP : HasDerivAt P A 0 := by
    have h1 := (hasDerivAt_id (0 : ℝ)).mul_const A
    have h2 := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const B
    have h3 := ((hasDerivAt_id (0 : ℝ)).pow 3).mul_const D
    have hh := (h1.add h2).add h3
    change HasDerivAt (((fun t : ℝ => t*A)+(fun t => t^2*B))+(fun t => t^3*D)) _ _ at hh
    have hf : (((fun t : ℝ => t*A)+(fun t => t^2*B))+(fun t => t^3*D))=P := by
      funext t
      rfl
    rw [hf] at hh
    simpa using hh
  have hsum := hdE.add hdP
  have heqfun : (fun t => E t+P t) = (fun t => cosineCoeff L (V t) k) := by
    funext t
    dsimp [E]
    ring
  change HasDerivAt (fun t => E t+P t) (0+A) 0 at hsum
  rw [heqfun,zero_add] at hsum
  exact hsum

/-- The actual modal response has the displayed third-order Peano jet.
This does not assume third parameter derivatives of the response. -/
theorem actual_response_cubic_jet (p : PhysicalParams) {L : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hsig : p.SignalEquilibrium)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc 0 L)) (k : ℕ)
    (V dV : ℝ → ℝ → ℝ)
    (hsol : ∀ᶠ t in 𝓝 (0 : ℝ), NeumannW21 L (V t) (dV t) ∧
      ∀ x ∈ Ioo 0 L, deriv (dV t) x-p.mu*(p.vStar+V t x)+p.nu*(p.uStar+t*w x)^p.gamma=0) :
    (fun t => cosineCoeff L (V t) k-responsePolynomial p L w k t)
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
  obtain ⟨radius,hr,C,_,hjet⟩ := actual_response_quartic p hL hu hmu hsig w hw k
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < radius :=
    (continuous_abs.tendsto (0 : ℝ)).eventually (Iio_mem_nhds (by simpa using hr))
  have hO : (fun t => cosineCoeff L (V t) k-responsePolynomial p L w k t)
      =O[𝓝 (0 : ℝ)] (fun t : ℝ => t^4) := by
    apply IsBigO.of_bound C
    filter_upwards [hsmall,hsol] with t ht hs
    simpa only [Real.norm_eq_abs,abs_pow] using hjet t (V t) (dV t) ht.le hs.1 hs.2
  exact hO.trans_isLittleO (isLittleO_pow_pow (by norm_num : 3 < 4))

end
end ChemotaxisBifurcation.SignalResponseJet
