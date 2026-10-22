module
public import ChemotaxisBifurcation.SignalTaylorRemainder
public import ChemotaxisBifurcation.LogisticDerivatives

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation
open Set

/-- The actual equilibrium-subtracted logistic nonlinearity has a derived
quartic remainder with exactly the manuscript's normalized A coefficients. -/
theorem normalizedLogistic_quartic_remainder (p : PhysicalParams) (hu : 0 < p.uStar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ p.uStar/2 →
      |normalizedLogistic p.alpha p.uStar (p.uStar+s) -
        (rawTaylorData p 0).Aprime*s - (rawTaylorData p 0).Asecond*s^2 -
        (rawTaylorData p 0).Athird*s^3| ≤ C*|s|^4 := by
  let q : PhysicalParams := { p with nu := 1, gamma := 1+p.alpha }
  obtain ⟨C,hC,hrem⟩ := signalSource_quartic_remainder q hu
  refine ⟨C,hC,?_⟩
  intro s hs
  have h := hrem s hs
  have hpow : p.uStar^(1+p.alpha) = p.uStar * p.uStar^p.alpha := by
    rw [Real.rpow_add hu, Real.rpow_one]
  have hex1 : 1+p.alpha-1 = p.alpha := by ring
  have hex2 : 1+p.alpha-2 = p.alpha-1 := by ring
  have hex3 : 1+p.alpha-3 = p.alpha-2 := by ring
  simp only [q,rawTaylorData,one_mul,hex1,hex2,hex3,hpow] at h
  convert h using 1
  congr 1
  simp only [normalizedLogistic,rawTaylorData]
  ring

/-- Actual logistic source remainder; logistic equilibrium supplies the
constant and linear cancellations, with no assumed Taylor error. -/
theorem logisticSource_quartic_remainder (p : PhysicalParams) (hu : 0 < p.uStar)
    (heq : p.LogisticEquilibrium) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ p.uStar/2 →
      |p.a*(p.uStar+s) - p.b*(p.uStar+s)^(1+p.alpha) + p.a*p.alpha*s +
        p.b*(rawTaylorData p 0).Asecond*s^2 +
        p.b*(rawTaylorData p 0).Athird*s^3| ≤ C*|s|^4 := by
  obtain ⟨C,hC,hrem⟩ := normalizedLogistic_quartic_remainder p hu
  refine ⟨|p.b| *C, by positivity, ?_⟩
  intro s hs
  have hid : p.a*(p.uStar+s) - p.b*(p.uStar+s)^(1+p.alpha) + p.a*p.alpha*s +
      p.b*(rawTaylorData p 0).Asecond*s^2 + p.b*(rawTaylorData p 0).Athird*s^3 =
      -p.b * (normalizedLogistic p.alpha p.uStar (p.uStar+s) -
        (rawTaylorData p 0).Aprime*s - (rawTaylorData p 0).Asecond*s^2 -
        (rawTaylorData p 0).Athird*s^3) := by
    rw [heq]
    simp only [normalizedLogistic,rawTaylorData]
    ring
  rw [hid,abs_mul,abs_neg]
  calc
    _ ≤ |p.b| *(C*|s|^4) := mul_le_mul_of_nonneg_left (hrem s hs) (abs_nonneg _)
    _ = _ := by ring

/-- Uniform actual logistic source error under an interval sup bound. -/
theorem logisticSource_field_quartic_bound (p : PhysicalParams) (hu : 0 < p.uStar)
    (heq : p.LogisticEquilibrium) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L N : ℝ) (U : ℝ → ℝ),
      N ≤ p.uStar/2 → (∀ x ∈ Icc 0 L, |U x| ≤ N) → ∀ x ∈ Icc 0 L,
      |p.a*(p.uStar+U x) - p.b*(p.uStar+U x)^(1+p.alpha) + p.a*p.alpha*U x +
        p.b*(rawTaylorData p 0).Asecond*(U x)^2 +
        p.b*(rawTaylorData p 0).Athird*(U x)^3| ≤ C*N^4 := by
  obtain ⟨C,hC,hrem⟩ := logisticSource_quartic_remainder p hu heq
  refine ⟨C,hC,?_⟩
  intro L N U hN hU x hx
  exact (hrem (U x) ((hU x hx).trans hN)).trans (by gcongr; exact hU x hx)

end ChemotaxisBifurcation
