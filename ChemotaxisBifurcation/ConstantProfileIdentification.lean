module
public import ChemotaxisBifurcation.ActualSolutionClosure

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ConstantProfileIdentification
open Set Filter Topology MeasureTheory
noncomputable section

/-- A positive constant actual logistic stationary population is the given
positive equilibrium. Mass balance is derived from the literal PDE. -/
theorem constant_value_eq (p : PhysicalParams) {L beta chi U : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L p.a p.b p.alpha chi p.m beta)
    (hL : 0 < L) (hb : 0 < p.b) (halpha : 0 < p.alpha) (hm : 1 ≤ p.m)
    (hu : 0 < p.uStar) (hequil : p.LogisticEquilibrium) (hU : 0 < U)
    (hconst : ∀ x ∈ Icc 0 L, q.u x=U)
    (hbase : ∀ x ∈ Icc 0 L, 0 < 1+q.v x) (hv0 : q.dv 0=0) (hvL : q.dv L=0) :
    U=p.uStar := by
  have hmass := PhysicalAmbientClosure.mass_balance_of_physical_profile q hL.le hm halpha.le hbase hv0 hvL
  have hI : (∫ x in (0 : ℝ)..L, q.u x)=L*U := by
    calc (∫ x in (0 : ℝ)..L, q.u x) = ∫ x in (0 : ℝ)..L, U := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hL.le] at hx
          exact hconst x hx
      _ = _ := by simp
  have hJ : (∫ x in (0 : ℝ)..L, q.u x^(1+p.alpha))=L*U^(1+p.alpha) := by
    calc (∫ x in (0 : ℝ)..L, q.u x^(1+p.alpha)) = ∫ x in (0 : ℝ)..L, U^(1+p.alpha) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hL.le] at hx
          change q.u x^(1+p.alpha)=U^(1+p.alpha)
          rw [hconst x hx]
      _ = _ := by simp
  rw [hI,hJ,Real.rpow_add hU,Real.rpow_one] at hmass
  have hfactor : L*U*(p.a-p.b*U^p.alpha)=0 := by nlinarith [hmass]
  have hlogU : p.a=p.b*U^p.alpha := sub_eq_zero.mp
    ((mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero hL.ne' hU.ne'))
  have hpowers : U^p.alpha=p.uStar^p.alpha :=
    mul_left_cancel₀ hb.ne' (hlogU.symm.trans hequil)
  exact (Real.rpow_left_inj hU.le hu.le halpha.ne').mp hpowers

/-- Distinctness from the known constant phase point forces the actual
positive logistic population profile to be nonconstant. -/
theorem nonconstant_of_phase_ne {E : Type*} (p : PhysicalParams) {L beta chi : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L p.a p.b p.alpha chi p.m beta)
    (hL : 0 < L) (hb : 0 < p.b) (halpha : 0 < p.alpha) (hm : 1 ≤ p.m)
    (hu : 0 < p.uStar) (hequil : p.LogisticEquilibrium)
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {e uStar : E}
    (hInj : Function.Injective prof) (hStar : ∀ x, prof uStar x=p.uStar)
    (hRep : ∀ x : Icc (0 : ℝ) L, q.u x=prof e x)
    (hpos : ∀ x ∈ Icc 0 L, 0 < q.u x)
    (hbase : ∀ x ∈ Icc 0 L, 0 < 1+q.v x) (hv0 : q.dv 0=0) (hvL : q.dv L=0)
    (hne : e ≠ uStar) :
    ∃ x y : Icc (0 : ℝ) L, prof e x ≠ prof e y := by
  by_contra h
  push Not at h
  let z : Icc (0 : ℝ) L := ⟨0,le_rfl,hL.le⟩
  have hconst : ∀ x ∈ Icc 0 L, q.u x=q.u 0 := by
    intro x hx
    rw [hRep ⟨x,hx⟩,hRep z]
    exact h ⟨x,hx⟩ z
  have heq := constant_value_eq p q hL hb halpha hm hu hequil
    (hpos 0 ⟨le_rfl,hL.le⟩) hconst hbase hv0 hvL
  apply hne
  apply hInj
  ext x
  rw [hStar,←hRep x,hconst x x.property,heq]

/-- Actual logistic ambient closure needs only nontriviality of phase points;
nonconstancy of every population profile is proved internally. -/
theorem closure_subset_admissible_of_nontrivial
    {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]
    (p : PhysicalParams) {L beta : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2) (hbeta : 0 ≤ beta)
    (halpha : 0 < p.alpha) (hb : 0 < p.b)
    (hnu : 0 ≤ p.nu) (hgamma : 0 < p.gamma) (hgamma1 : p.gamma ≤ 1+p.alpha)
    (hequil : p.LogisticEquilibrium) (hsigequil : p.SignalEquilibrium)
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {uStar : E} {S : Set (ℝ × E)}
    (hProf : Continuous prof) (hInj : Function.Injective prof)
    (hconst : ∀ x, prof uStar x=p.uStar) (hAff : IsClosed Aff)
    (hS : S ⊆ AmbientClosure.admissibleSet prof Aff)
    (hSne : ∀ z ∈ S, z.2 ≠ uStar)
    (hSSol : S ⊆ ActualSolutionClosure.solutionSet prof p.a p.b p.alpha p.m beta p.mu p.nu p.gamma) :
    closure S ⊆ AmbientClosure.admissibleSet prof Aff := by
  apply ActualSolutionClosure.closure_subset_admissible p hL hu hmu hm hm1 hbeta halpha hb
    hnu hgamma hgamma1 hequil hsigequil hProf hInj hconst hAff hS hSne hSSol
  intro z hz
  obtain ⟨q,hrep,hnn,hN0,hNL,_⟩ := hSSol hz
  apply nonconstant_of_phase_ne p q hL hb halpha hm hu hequil hInj hconst hrep
  · intro x hx
    rw [hrep ⟨x,hx⟩]
    exact (hS hz).2.2 ⟨x,hx⟩
  · intro x hx
    linarith [(hnn x hx).2]
  · exact hN0
  · exact hNL
  · exact hSne z hz

end
end ChemotaxisBifurcation.ConstantProfileIdentification
