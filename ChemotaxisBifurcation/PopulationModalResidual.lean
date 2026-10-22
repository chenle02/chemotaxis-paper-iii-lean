module
public import ChemotaxisBifurcation.LogisticTaylorRemainder
public import ChemotaxisBifurcation.MobilityTaylorRemainder
public import ChemotaxisBifurcation.ModalRemainder
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.PopulationModalResidual
open Real Set MeasureTheory
noncomputable section

/-- Actual physical logistic source minus its cubic Taylor polynomial. -/
def sourceRemainder (p : PhysicalParams) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  p.a*(p.uStar+U x) - p.b*(p.uStar+U x)^(1+p.alpha) + p.a*p.alpha*U x +
    p.b*(rawTaylorData p 0).Asecond*(U x)^2 +
    p.b*(rawTaylorData p 0).Athird*(U x)^3

/-- Complete quadratic mobility polynomial with the paper's coefficients. -/
def mobilityPolynomial (p : PhysicalParams) (beta : ℝ) (U V : ℝ → ℝ) (x : ℝ) : ℝ :=
  (rawTaylorData p beta).B0 + (rawTaylorData p beta).Bu*U x +
    (rawTaylorData p beta).Bv*V x + (rawTaylorData p beta).Buu*(U x)^2 +
    (rawTaylorData p beta).Buv*U x*V x + (rawTaylorData p beta).Bvv*(V x)^2

theorem mobilityPolynomial_contDiffOn (p : PhysicalParams) (beta : ℝ)
    {Ω : Set ℝ} {U V : ℝ → ℝ} (hU : ContDiffOn ℝ 1 U Ω) (hV : ContDiffOn ℝ 1 V Ω) :
    ContDiffOn ℝ 1 (mobilityPolynomial p beta U V) Ω :=
  ((((contDiffOn_const.add (contDiffOn_const.mul hU)).add
    (contDiffOn_const.mul hV)).add (contDiffOn_const.mul (hU.pow 2))).add
    ((contDiffOn_const.mul hU).mul hV)).add (contDiffOn_const.mul (hV.pow 2))

/-- Actual mobility minus its complete quadratic Taylor polynomial. -/
def mobilityRemainder (p : PhysicalParams) (beta : ℝ) (U V : ℝ → ℝ) (x : ℝ) : ℝ :=
  (p.uStar+U x)^p.m / (p.signalOffset+V x)^beta -
    mobilityPolynomial p beta U V x

/-- Actual chemotactic flux error, with its physical minus sign. -/
def fluxRemainder (p : PhysicalParams) (beta chi : ℝ) (U V : ℝ → ℝ) (x : ℝ) : ℝ :=
  -chi * (mobilityRemainder p beta U V x * deriv V x)

/-- Ordinary local classical regularity gives regularity of the actual flux.
The open neighborhood avoids treating endpoint within-derivatives as ordinary
ones. Positivity is only required on this neighborhood, not globally. -/
theorem flux_contDiffOn (p : PhysicalParams) (beta chi : ℝ)
    {Ω : Set ℝ} (hΩ : IsOpen Ω) {U V : ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 U Ω) (hV : ContDiffOn ℝ 2 V Ω)
    (hu : ∀ x ∈ Ω, 0 < p.uStar+U x)
    (hv : ∀ x ∈ Ω, 0 < p.signalOffset+V x) :
    ContDiffOn ℝ 1 (fluxRemainder p beta chi U V) Ω := by
  have hV1 : ContDiffOn ℝ 1 V Ω := hV.of_le (by norm_num)
  have hDV : ContDiffOn ℝ 1 (deriv V) Ω := hV.deriv_of_isOpen hΩ (by norm_num)
  have hbu := (contDiffOn_const.add hU).rpow_const_of_ne (p := p.m)
    (fun x hx => (hu x hx).ne')
  have hbV := (contDiffOn_const.add hV1).rpow_const_of_ne (p := beta)
    (fun x hx => (hv x hx).ne')
  have hmob : ContDiffOn ℝ 1
      (fun x => (p.uStar+U x)^p.m/(p.signalOffset+V x)^beta) Ω :=
    hbu.div hbV (fun x hx => (Real.rpow_pos_of_pos (hv x hx) beta).ne')
  have hpoly := mobilityPolynomial_contDiffOn p beta hU hV1
  exact contDiffOn_const.mul ((hmob.sub hpoly).mul hDV)

/-- The actual physical source remainder is continuous under local positivity. -/
theorem source_continuousOn (p : PhysicalParams) {Ω : Set ℝ} {U : ℝ → ℝ}
    (hU : ContinuousOn U Ω) (hu : ∀ x ∈ Ω, 0 < p.uStar+U x) :
    ContinuousOn (sourceRemainder p U) Ω := by
  have hp := (continuousOn_const.add hU).rpow_const
    (p := 1+p.alpha) (fun x hx => Or.inl (hu x hx).ne')
  exact (((((continuousOn_const.mul (continuousOn_const.add hU)).sub
    (continuousOn_const.mul hp)).add (continuousOn_const.mul hU)).add
    (continuousOn_const.mul (hU.pow 2))).add (continuousOn_const.mul (hU.pow 3)))

/-- The source-plus-flux remainder is exactly the difference between the
actual population nonlinear operator and its retained Taylor terms. This
identity includes the spatial derivative of the flux, not only scalar algebra. -/
theorem actual_nonlinear_operator_decomposition (p : PhysicalParams) (beta chi : ℝ)
    {Ω : Set ℝ} (hΩ : IsOpen Ω) {U V : ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 U Ω) (hV : ContDiffOn ℝ 2 V Ω)
    (hu : ∀ x ∈ Ω, 0 < p.uStar+U x) (hv : ∀ x ∈ Ω, 0 < p.signalOffset+V x)
    (x : ℝ) (hx : x ∈ Ω) :
    deriv (fun y => -chi * ((p.uStar+U y)^p.m / (p.signalOffset+V y)^beta * deriv V y)) x +
      p.a*(p.uStar+U x) - p.b*(p.uStar+U x)^(1+p.alpha) -
      (deriv (fun y => -chi * (mobilityPolynomial p beta U V y * deriv V y)) x -
        p.a*p.alpha*U x - p.b*(rawTaylorData p 0).Asecond*(U x)^2 -
        p.b*(rawTaylorData p 0).Athird*(U x)^3) =
      sourceRemainder p U x + deriv (fluxRemainder p beta chi U V) x := by
  let P := fun y => -chi * (mobilityPolynomial p beta U V y * deriv V y)
  have hP : ContDiffOn ℝ 1 P Ω := contDiffOn_const.mul
    ((mobilityPolynomial_contDiffOn p beta hU (hV.of_le (by norm_num))).mul
      (hV.deriv_of_isOpen hΩ (by norm_num)))
  have hR := flux_contDiffOn p beta chi hΩ hU hV hu hv
  have hdP := ((hP x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt_one
  have hdR := ((hR x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt_one
  have hfun : (fun y => -chi * ((p.uStar+U y)^p.m / (p.signalOffset+V y)^beta * deriv V y)) =
      fun y => P y + fluxRemainder p beta chi U V y := by
    funext y; dsimp [P,fluxRemainder,mobilityRemainder]; ring
  rw [hfun,(hdP.hasDerivAt.fun_add hdR.hasDerivAt).deriv]
  dsimp [P,sourceRemainder]
  ring

/-- Actual source-plus-flux population remainder, projected in every mode.
All Taylor bounds, flux regularity/integrable derivative and zero flux endpoint
values are derived from the actual nonlinearities and local classical data. -/
theorem actual_population_projection_quartic_uniform (p : PhysicalParams) (beta X : ℝ)
    (hX : 0 ≤ X)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) (heq : p.LogisticEquilibrium) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ chi : ℝ, |chi| ≤ X → ∀ (L N : ℝ) (Ω : Set ℝ) (U V : ℝ → ℝ),
      0 < L → IsOpen Ω → Icc 0 L ⊆ Ω →
      ContDiffOn ℝ 1 U Ω → ContDiffOn ℝ 2 V Ω →
      (∀ x ∈ Ω, 0 < p.uStar+U x) → (∀ x ∈ Ω, 0 < p.signalOffset+V x) →
      0 ≤ N → N ≤ 1 → N ≤ p.uStar/2 → N ≤ p.signalOffset/2 →
      (∀ x ∈ Icc 0 L, |U x| ≤ N) → (∀ x ∈ Icc 0 L, |V x| ≤ N) →
      (∀ x ∈ Icc 0 L, |deriv V x| ≤ N) → deriv V 0 = 0 → deriv V L = 0 →
      ∀ k : ℕ,
      |CosineCoefficients.cosineCoeff L
        (fun x => sourceRemainder p U x + deriv (fluxRemainder p beta chi U V) x) k| ≤
      (if k = 0 then 1/L else 2/L) * ((L+k*Real.pi)*C*N^4) := by
  obtain ⟨A,hA,hsource⟩ := logisticSource_field_quartic_bound p hu heq
  obtain ⟨B,hB,hflux⟩ := mobility_flux_field_quartic_bound p beta hu hw
  refine ⟨A+X*B, by positivity, ?_⟩
  intro chi hchi L N Ω U V hL hΩ hsub hU hV hposU hposV hN hN1 hNu hNv hUb hVb hDVb hDV0 hDVL k
  have hs : ContinuousOn (sourceRemainder p U) (Icc 0 L) :=
    (source_continuousOn p hU.continuousOn hposU).mono hsub
  have hf : ContDiffOn ℝ 1 (fluxRemainder p beta chi U V) (Icc 0 L) :=
    (flux_contDiffOn p beta chi hΩ hU hV hposU hposV).mono hsub
  have hac : AbsolutelyContinuousOnInterval (fluxRemainder p beta chi U V) 0 L :=
    ContDiffOn.absolutelyContinuousOnInterval (by simpa [uIcc_of_le hL.le] using hf)
  have hz0 : fluxRemainder p beta chi U V 0 = 0 := by simp [fluxRemainder,hDV0]
  have hzL : fluxRemainder p beta chi U V L = 0 := by simp [fluxRemainder,hDVL]
  have hb0 : ∀ x ∈ Icc 0 L, |sourceRemainder p U x| ≤ (A+X*B)*N^4 := by
    intro x hx
    have h : |sourceRemainder p U x| ≤ A*N^4 := hsource L N U hNu hUb x hx
    exact h.trans (by nlinarith [mul_nonneg (mul_nonneg hX hB) (pow_nonneg hN 4)])
  have hb1 : ∀ x ∈ Icc 0 L, |fluxRemainder p beta chi U V x| ≤ (A+X*B)*N^4 := by
    intro x hx
    have h : |mobilityRemainder p beta U V x * deriv V x| ≤ B*N^4 :=
      hflux L N U V hN hN1 hNu hNv hUb hVb hDVb x hx
    rw [fluxRemainder,abs_mul,abs_neg]
    calc
      _ ≤ |chi| *(B*N^4) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ ≤ X*(B*N^4) := mul_le_mul_of_nonneg_right hchi (by positivity)
      _ ≤ (A+X*B)*N^4 := by nlinarith [mul_nonneg hA (pow_nonneg hN 4)]
  have h := ProjectedRemainder.projected_remainder_bound_of_absolutelyContinuous hL k
    (hs.intervalIntegrable_of_Icc hL.le) hac hz0 hzL hb0 hb1
  have hn := ModalRemainder.population_normalized_bound hL k h
  convert hn using 1; ring

/-- Fixed-sensitivity specialization of the uniform projection theorem. -/
theorem actual_population_projection_quartic (p : PhysicalParams) (beta chi : ℝ)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) (heq : p.LogisticEquilibrium) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L N : ℝ) (Ω : Set ℝ) (U V : ℝ → ℝ),
      0 < L → IsOpen Ω → Icc 0 L ⊆ Ω →
      ContDiffOn ℝ 1 U Ω → ContDiffOn ℝ 2 V Ω →
      (∀ x ∈ Ω, 0 < p.uStar+U x) → (∀ x ∈ Ω, 0 < p.signalOffset+V x) →
      0 ≤ N → N ≤ 1 → N ≤ p.uStar/2 → N ≤ p.signalOffset/2 →
      (∀ x ∈ Icc 0 L, |U x| ≤ N) → (∀ x ∈ Icc 0 L, |V x| ≤ N) →
      (∀ x ∈ Icc 0 L, |deriv V x| ≤ N) → deriv V 0 = 0 → deriv V L = 0 →
      ∀ k : ℕ,
      |CosineCoefficients.cosineCoeff L
        (fun x => sourceRemainder p U x + deriv (fluxRemainder p beta chi U V) x) k| ≤
      (if k = 0 then 1/L else 2/L) * ((L+k*Real.pi)*C*N^4) := by
  obtain ⟨C,hC,h⟩ := actual_population_projection_quartic_uniform p beta |chi|
    (abs_nonneg chi) hu hw heq
  exact ⟨C,hC,h chi le_rfl⟩

end
end ChemotaxisBifurcation.PopulationModalResidual
