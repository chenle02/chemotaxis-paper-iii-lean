module
public import ChemotaxisBifurcation.WeakH2Compactness
public import ChemotaxisBifurcation.ConstantProfileIdentification

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.AllPositiveLogisticCompactness
open Real Set MeasureTheory Filter Topology WeakH2PhaseSpace WeakH2Compactness
noncomputable section

/-- The actual constant equilibrium solves the literal stationary population
PDE at every sensitivity; its signal equation is supplied separately below. -/
def equilibriumProfile (p : PhysicalParams) {L : ℝ} (chi beta : ℝ)
    (hU : 0 < p.uStar) (hequil : p.LogisticEquilibrium) :
    PhysicalStrongPositivity.StationaryProfile L p.a p.b p.alpha chi p.m beta where
  u := fun _ => p.uStar
  du := fun _ => 0
  ddu := fun _ => 0
  v := fun _ => p.vStar
  dv := fun _ => 0
  ddv := fun _ => 0
  derivative_u := fun x _ => hasDerivWithinAt_const x _ _
  derivative_du := fun x _ => hasDerivWithinAt_const x _ _
  derivative_v := fun x _ => hasDerivWithinAt_const x _ _
  derivative_dv := fun x _ => hasDerivWithinAt_const x _ _
  continuous_ddu := continuousOn_const
  continuous_ddv := continuousOn_const
  stationary := by
    intro x hx
    have hflux : MinimalFlux.flux chi p.m beta (fun _ => p.uStar) (fun _ => p.vStar)
        (fun _ => 0) = (fun _ => (0 : ℝ)) := by funext y; simp [MinimalFlux.flux]
    rw [hflux]
    simp only [deriv_const,sub_zero,zero_add]
    rw [Real.rpow_add hU,Real.rpow_one,hequil]
    ring
  neumann_left := rfl
  neumann_right := rfl

theorem phase_equilibrium {L : ℝ} (hL : 0 < L) (p : PhysicalParams) (chi beta : ℝ)
    (hU : 0 < p.uStar) (hequil : p.LogisticEquilibrium) :
    phaseOfPhysical hL (equilibriumProfile p chi beta hU hequil) = const hL p.uStar := by
  apply profileCLM_injective hL
  rw [profileCLM_const]
  apply ContinuousMap.ext
  intro x
  rw [profile_phaseOfPhysical]
  rfl

/-- Any constant positive actual logistic profile is exactly the known
constant phase point; no externally supplied phase identification is used. -/
theorem phase_eq_const {L beta chi : ℝ} (hL : 0 < L) (p : PhysicalParams)
    (q : PhysicalStrongPositivity.StationaryProfile L p.a p.b p.alpha chi p.m beta)
    (hb : 0 < p.b) (halpha : 0 < p.alpha) (hm : 1 ≤ p.m)
    (hU : 0 < p.uStar) (hequil : p.LogisticEquilibrium)
    (hu : ∀ x ∈ Icc 0 L, 0 < q.u x) (hv : ∀ x ∈ Icc 0 L, 0 ≤ q.v x)
    (hN0 : q.dv 0 = 0) (hNL : q.dv L = 0)
    (hnc : ¬∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, q.u x ≠ q.u y) :
    phaseOfPhysical hL q = const hL p.uStar := by
  have hvalues : ∀ x ∈ Icc 0 L, q.u x=q.u 0 := by
    intro x hx
    by_contra hh
    exact hnc ⟨x,hx,0,⟨le_rfl,hL.le⟩,hh⟩
  have heq := ConstantProfileIdentification.constant_value_eq p q hL hb halpha hm hU hequil
    (hu 0 ⟨le_rfl,hL.le⟩) hvalues (fun x hx => by linarith [hv x hx]) hN0 hNL
  apply profileCLM_injective hL
  rw [profileCLM_const]
  apply ContinuousMap.ext
  intro x
  rw [profile_phaseOfPhysical]
  exact (hvalues x x.property).trans heq

/-- Arbitrary positive bounded-sensitivity actual logistic families, including
constant bifurcation profiles, have genuine parameter/weak-H2 norm subsequences.
No all-nonconstant or compactness assumption is imposed. -/
theorem logistic_all_positive_norm_subsequence {L beta X : ℝ}
    (p : PhysicalParams) (hp : p.LogisticAdmissible)
    (hL : 0 < L) (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2)
    (hgamma1 : p.gamma ≤ 1+p.alpha) (hbeta : 0 ≤ beta)
    (chi : ℕ → ℝ)
    (Q : ∀ n, PhysicalStrongPositivity.StationaryProfile L p.a p.b p.alpha (chi n) p.m beta)
    (hv : ∀ n x, x ∈ Icc 0 L → 0 ≤ (Q n).v x)
    (hN0 : ∀ n, (Q n).dv 0 = 0) (hNL : ∀ n, (Q n).dv L = 0)
    (heq : ∀ n x, x ∈ Ioo 0 L → (Q n).ddv x-p.mu*(Q n).v x+p.nu*(Q n).u x^p.gamma = 0)
    (hchi : ∀ n, |chi n| ≤ X)
    (hu : ∀ n x, x ∈ Icc 0 L → 0 < (Q n).u x) :
    ∃ chiBar : ℝ,
    ∃ q : PhysicalStrongPositivity.StationaryProfile L p.a p.b p.alpha chiBar p.m beta,
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun n => (chi (phi n),phaseOfPhysical hL (Q (phi n))))
        atTop (𝓝 (chiBar,phaseOfPhysical hL q)) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      ∀ x ∈ Ioo 0 L, q.ddv x-p.mu*q.v x+p.nu*q.u x^p.gamma = 0 := by
  rcases hp with ⟨ha,hb,halpha,_,hgamma,hnu,hmu,hU,hV,hequil,hsigequil⟩
  let NC := fun n => ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, (Q n).u x ≠ (Q n).u y
  by_cases hf : ∃ᶠ n in atTop, NC n
  · obtain ⟨phi,hphi,hNC⟩ := extraction_of_frequently_atTop hf
    obtain ⟨chiBar,q,psi,hpsi,hconv,hnn,hqN0,hqNL,hqeq⟩ :=
      logistic_physical_norm_subsequence (fun n => chi (phi n)) (fun n => Q (phi n))
        hL ha hb halpha hm hm1 hbeta hmu hnu.le hgamma hgamma1
        (fun n => hv (phi n)) (fun n => hN0 (phi n)) (fun n => hNL (phi n))
        (fun n => heq (phi n)) (fun n => hchi (phi n)) (fun n => hu (phi n)) hNC
    exact ⟨chiBar,q,fun n => phi (psi n),hphi.comp hpsi,hconv,hnn,hqN0,hqNL,hqeq⟩
  · have hconst : ∀ᶠ n in atTop, phaseOfPhysical hL (Q n)=const hL p.uStar := by
      have hevent : ∀ᶠ n in atTop, ¬NC n := not_frequently.mp hf
      exact hevent.mono (fun n hn => phase_eq_const hL p (Q n) hb halpha hm hU hequil
        (hu n) (hv n) (hN0 n) (hNL n) hn)
    obtain ⟨chiBar,_,phi,hphi,hcl⟩ := isCompact_Icc.tendsto_subseq
      (fun n => (abs_le.mp (hchi n) : chi n ∈ Icc (-X) X))
    let q := equilibriumProfile p (L := L) chiBar beta hU hequil
    have hphase : Tendsto (fun n => phaseOfPhysical hL (Q (phi n))) atTop (𝓝 (const hL p.uStar)) := by
      apply tendsto_const_nhds.congr'
      exact (hphi.tendsto_atTop.eventually hconst).mono (fun n hn => hn.symm)
    have hconv : Tendsto (fun n => (chi (phi n),phaseOfPhysical hL (Q (phi n))))
        atTop (𝓝 (chiBar,phaseOfPhysical hL q)) := by
      rw [phase_equilibrium hL p chiBar beta hU hequil]
      exact hcl.prodMk_nhds hphase
    refine ⟨chiBar,q,phi,hphi,hconv,fun _ _ => ⟨hU.le,hV.le⟩,rfl,rfl,?_⟩
    intro x hx
    change 0-p.mu*p.vStar+p.nu*p.uStar^p.gamma=0
    rw [hsigequil]
    ring

end
end ChemotaxisBifurcation.AllPositiveLogisticCompactness
