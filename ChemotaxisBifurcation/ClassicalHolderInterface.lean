module
public import ChemotaxisBifurcation.ClassicalHolderNorm

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalHolderInterface
open Real Set MeasureTheory
noncomputable section

/-- Actual standard C2+theta bounds in Mathlib-only public vocabulary for the
logistic stationary system. Every derivative and equation is literal solution
information; no profile record, bound, compactness or regularity estimate is assumed. -/
theorem logistic_uniform_norm_bound (L a b alpha m beta mu nu gamma X : ℝ)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hg : 0 < gamma) (hg1 : gamma ≤ 1+alpha) :
    ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
      ∀ (chi : ℝ) (u du ddu v dv ddv : ℝ → ℝ),
      (∀ x ∈ Icc 0 L, HasDerivWithinAt u (du x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt du (ddu x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt v (dv x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt dv (ddv x) (Icc 0 L) x) →
      ContinuousOn ddu (Icc 0 L) → ContinuousOn ddv (Icc 0 L) →
      (∀ x ∈ Ioo 0 L,
        ddu x-deriv (fun y => chi*(u y^m/(1+v y)^beta)*dv y) x+a*u x-b*u x^(1+alpha)=0) →
      du 0=0 → du L=0 → (∀ x ∈ Icc 0 L, 0 ≤ v x) → dv 0=0 → dv L=0 →
      (∀ x ∈ Ioo 0 L, ddv x-mu*v x+nu*u x^gamma=0) →
      |chi| ≤ X → (∀ x ∈ Icc 0 L, 0 < u x) → (∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y) →
      let norm := fun f df ddf : ℝ → ℝ =>
        sSup ((fun x => |f x|) '' Icc 0 L)+
        sSup ((fun x => |df x|) '' Icc 0 L)+
        sSup ((fun x => |ddf x|) '' Icc 0 L)+
        sSup {q : ℝ | ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L,
          x ≠ y ∧ q=|ddf y-ddf x|/|y-x|^theta}
      norm u du ddu ≤ C ∧ norm v dv ddv ≤ C := by
  obtain ⟨theta,ht,C,hC,hall⟩ := ClassicalHolderNorm.logistic_uniform_norm_bound
    hL ha hb halpha hm hm1 hbeta hmu hnu hg hg1 (X := X)
  refine ⟨theta,ht,C,hC,?_⟩
  intro chi u du ddu v dv ddv hu hdu hv hdv hc hcv heq hN0 hNL hnn hV0 hVL hsig hchi hp hextra
  let q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta := {
    u := u, du := du, ddu := ddu, v := v, dv := dv, ddv := ddv
    derivative_u := hu, derivative_du := hdu, derivative_v := hv, derivative_dv := hdv
    continuous_ddu := hc, continuous_ddv := hcv
    stationary := by
      intro x hx
      change ddu x-deriv (fun y => chi*(u y^m/(1+v y)^beta)*dv y) x+a*u x-b*u x^(1+alpha)=0
      exact heq x hx
    neumann_left := hN0, neumann_right := hNL }
  exact hall chi q hnn hV0 hVL hsig hchi hp hextra

/-- Actual standard C2+theta bounds in Mathlib-only public vocabulary for the
minimal stationary system. Every derivative and equation is literal solution
information; no profile record, bound, compactness or regularity estimate is assumed. -/
theorem minimal_uniform_norm_bound (L m beta mu nu gamma X uStar : ℝ)
    (hL : 0 < L) (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
      ∀ (chi : ℝ) (u du ddu v dv ddv : ℝ → ℝ),
      (∀ x ∈ Icc 0 L, HasDerivWithinAt u (du x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt du (ddu x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt v (dv x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt dv (ddv x) (Icc 0 L) x) →
      ContinuousOn ddu (Icc 0 L) → ContinuousOn ddv (Icc 0 L) →
      (∀ x ∈ Ioo 0 L,
        ddu x-deriv (fun y => chi*(u y^m/(1+v y)^beta)*dv y) x=0) →
      du 0=0 → du L=0 → (∀ x ∈ Icc 0 L, 0 ≤ v x) → dv 0=0 → dv L=0 →
      (∀ x ∈ Ioo 0 L, ddv x-mu*v x+nu*u x^gamma=0) →
      |chi| ≤ X → (∀ x ∈ Icc 0 L, 0 < u x) → (∫ x in (0 : ℝ)..L, u x) = L*uStar →
      let norm := fun f df ddf : ℝ → ℝ =>
        sSup ((fun x => |f x|) '' Icc 0 L)+
        sSup ((fun x => |df x|) '' Icc 0 L)+
        sSup ((fun x => |ddf x|) '' Icc 0 L)+
        sSup {q : ℝ | ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L,
          x ≠ y ∧ q=|ddf y-ddf x|/|y-x|^theta}
      norm u du ddu ≤ C ∧ norm v dv ddv ≤ C := by
  obtain ⟨theta,ht,C,hC,hall⟩ := ClassicalHolderNorm.minimal_uniform_norm_bound
    hL hm hm1 hbeta hmu hnu hg hg1 (X := X) (uStar := uStar)
  refine ⟨theta,ht,C,hC,?_⟩
  intro chi u du ddu v dv ddv hu hdu hv hdv hc hcv heq hN0 hNL hnn hV0 hVL hsig hchi hp hextra
  let q : PhysicalStrongPositivity.StationaryProfile L 0 0 0 chi m beta := {
    u := u, du := du, ddu := ddu, v := v, dv := dv, ddv := ddv
    derivative_u := hu, derivative_du := hdu, derivative_v := hv, derivative_dv := hdv
    continuous_ddu := hc, continuous_ddv := hcv
    stationary := by
      intro x hx
      change ddu x-deriv (fun y => chi*(u y^m/(1+v y)^beta)*dv y) x+0*u x-0*u x^(1+(0:ℝ))=0
      simpa only [zero_mul, sub_zero, add_zero] using heq x hx
    neumann_left := hN0, neumann_right := hNL }
  exact hall chi q hnn hV0 hVL hsig hchi hp hextra

end
end ChemotaxisBifurcation.ClassicalHolderInterface
