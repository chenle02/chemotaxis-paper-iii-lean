module
public import ChemotaxisBifurcation.SignedEllipticEnergy
public import ChemotaxisBifurcation.ClassicalODECompactness
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.NeumannResolvent
open Real Set MeasureTheory Filter Topology
noncomputable section

/-- Explicit variation-of-constants construction of a genuine Neumann
response for every continuous source; no solution or response family is assumed. -/
theorem exists_profile_global {L mu : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (F : ℝ → ℝ) (hF : Continuous F) :
    Nonempty (SignedEllipticEnergy.Profile L mu F) := by
  let k := sqrt mu
  have hk : 0 < k := sqrt_pos.2 hmu
  have hk2 : k^2 = mu := sq_sqrt hmu.le
  let ep := fun x : ℝ => exp (k*x)
  let em := fun x : ℝ => exp (-k*x)
  let P := fun x : ℝ => ∫ t in (0 : ℝ)..x, em t*F t
  let M := fun x : ℝ => ∫ t in (0 : ℝ)..x, ep t*F t
  have hep : ∀ x, HasDerivAt ep (k*ep x) x := by
    intro x
    convert (((hasDerivAt_id x).const_mul k).exp) using 1 <;> dsimp [ep]; ring
  have hem : ∀ x, HasDerivAt em (-k*em x) x := by
    intro x
    convert (((hasDerivAt_id x).const_mul (-k)).exp) using 1 <;> dsimp [em]; ring
  have hepc : Continuous ep := continuous_iff_continuousAt.mpr (fun x => (hep x).continuousAt)
  have hemc : Continuous em := continuous_iff_continuousAt.mpr (fun x => (hem x).continuousAt)
  have hPc : Continuous (fun x => em x*F x) := hemc.mul hF
  have hMc : Continuous (fun x => ep x*F x) := hepc.mul hF
  have hP : ∀ x, HasDerivAt P (em x*F x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hPc.intervalIntegrable _ _)
      (hPc.stronglyMeasurableAtFilter _ _) hPc.continuousAt
  have hM : ∀ x, HasDerivAt M (ep x*F x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hMc.intervalIntegrable _ _)
      (hMc.stronglyMeasurableAtFilter _ _) hMc.continuousAt
  have hPP : Continuous P := continuous_iff_continuousAt.mpr (fun x => (hP x).continuousAt)
  have hMM : Continuous M := continuous_iff_continuousAt.mpr (fun x => (hM x).continuousAt)
  have hprod : ∀ x, ep x*em x = 1 := by
    intro x
    dsimp [ep,em]
    rw [← exp_add]
    convert exp_zero using 2; ring
  have hD : ep L-em L ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    apply exp_lt_exp.mpr
    nlinarith [mul_pos hk hL]
  let A := (ep L*P L+em L*M L)/(2*k*(ep L-em L))
  let V := fun x => A*(ep x+em x)-(ep x*P x-em x*M x)/(2*k)
  let dV := fun x => A*k*(ep x-em x)-(ep x*P x+em x*M x)/2
  have hVc : Continuous V :=
    (continuous_const.mul (hepc.add hemc)).sub (((hepc.mul hPP).sub (hemc.mul hMM)).div_const _)
  have hdVc : Continuous dV :=
    (continuous_const.mul (hepc.sub hemc)).sub (((hepc.mul hPP).add (hemc.mul hMM)).div_const _)
  have hder : ∀ x, HasDerivAt V (dV x) x := by
    intro x
    have hh := (((hep x).add (hem x)).const_mul A).sub
      ((((hep x).mul (hP x)).sub ((hem x).mul (hM x))).div_const (2*k))
    convert hh using 1
    dsimp [V,dV]
    field_simp
    ring
  have hder2 : ∀ x, HasDerivAt dV (mu*V x-F x) x := by
    intro x
    have hh := (((hep x).sub (hem x)).const_mul (A*k)).sub
      ((((hep x).mul (hP x)).add ((hem x).mul (hM x))).div_const 2)
    convert hh using 1
    dsimp [V,dV]
    have hFx : ep x*(em x*F x) = F x := by rw [← mul_assoc,hprod x,one_mul]
    have hFx' : em x*(ep x*F x) = F x := by rw [mul_left_comm,← mul_assoc,hprod x,one_mul]
    rw [hFx,hFx',← hk2]
    field_simp
    ring
  refine ⟨{
    V := V
    dV := dV
    continuous_V := hVc.continuousOn
    continuous_dV := hdVc.continuousOn
    derivative_V := fun x _ => hder x
    equation := fun x _ => hder2 x
    neumann_left := ?_
    neumann_right := ?_ }⟩
  · simp [dV,ep,em,P,M]
  · dsimp [dV,A]
    field_simp [hk.ne',hD]
    ring

/-- Actual existence for every source continuous only on the physical
interval. The global extension is constructed internally and agrees there. -/
theorem exists_profile {L mu : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc 0 L)) :
    Nonempty (SignedEllipticEnergy.Profile L mu F) := by
  let f : C(Icc (0 : ℝ) L,ℝ) := ⟨fun x => F x,continuousOn_iff_continuous_domRestrict.mp hF⟩
  let G := IccExtend hL.le f
  have hG : Continuous G := continuous_IccExtend_iff.mpr f.continuous
  obtain ⟨p⟩ := exists_profile_global hL hmu G hG
  refine ⟨{
    V := p.V
    dV := p.dV
    continuous_V := p.continuous_V
    continuous_dV := p.continuous_dV
    derivative_V := p.derivative_V
    equation := ?_
    neumann_left := p.neumann_left
    neumann_right := p.neumann_right }⟩
  intro x hx
  have hh := p.equation x hx
  have he : G x = F x := IccExtend_of_mem hL.le f (Ioo_subset_Icc_self hx)
  rwa [he] at hh

/-- Uniqueness of actual Neumann responses, from the proved zero-source
energy bound rather than a supplied inverse or uniqueness assumption. -/
theorem profile_unique {L mu : ℝ} {F : ℝ → ℝ}
    (hL : 0 < L) (hmu : 0 < mu) (p q : SignedEllipticEnergy.Profile L mu F) :
    ∀ x ∈ Icc 0 L, p.V x = q.V x ∧ p.dV x = q.dV x := by
  let d : SignedEllipticEnergy.Profile L mu (fun _ => 0) := {
    V := fun x => p.V x-q.V x
    dV := fun x => p.dV x-q.dV x
    continuous_V := p.continuous_V.sub q.continuous_V
    continuous_dV := p.continuous_dV.sub q.continuous_dV
    derivative_V := fun x hx => (p.derivative_V x hx).sub (q.derivative_V x hx)
    equation := by
      intro x hx
      convert (p.equation x hx).sub (q.equation x hx) using 1; ring
    neumann_left := by simp [p.neumann_left,q.neumann_left]
    neumann_right := by simp [p.neumann_right,q.neumann_right] }
  have hh := d.c1_bound hL hmu continuousOn_const (B := 0) le_rfl (by intros; simp)
  intro x hx
  have hz := hh x hx
  change |p.V x-q.V x|+|p.dV x-q.dV x| ≤ _ at hz
  simp only [mul_zero] at hz
  have h0 : |p.V x-q.V x| = 0 := by linarith [abs_nonneg (p.V x-q.V x),abs_nonneg (p.dV x-q.dV x)]
  have h1 : |p.dV x-q.dV x| = 0 := by linarith [abs_nonneg (p.V x-q.V x),abs_nonneg (p.dV x-q.dV x)]
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp h0),sub_eq_zero.mp (abs_eq_zero.mp h1)⟩

/-- A canonical actual elliptic response, selected only after existence is proved. -/
def response {L mu : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc 0 L)) : SignedEllipticEnergy.Profile L mu F :=
  Classical.choice (exists_profile hL hmu F hF)

/-- The actual equation supplies a continuous second derivative, including
one-sided closed-interval derivative identities at the two Neumann endpoints. -/
theorem profile_classical_C2 {L mu : ℝ} {F : ℝ → ℝ}
    (p : SignedEllipticEnergy.Profile L mu F) (hF : ContinuousOn F (Icc 0 L)) :
    ContinuousOn (fun x => mu*p.V x-F x) (Icc 0 L) ∧
      (∀ x ∈ Icc 0 L, HasDerivWithinAt p.V (p.dV x) (Icc 0 L) x) ∧
      ∀ x ∈ Icc 0 L, HasDerivWithinAt p.dV (mu*p.V x-F x) (Icc 0 L) x := by
  have hdd : ContinuousOn (fun x => mu*p.V x-F x) (Icc 0 L) :=
    (continuousOn_const.mul p.continuous_V).sub hF
  exact ⟨hdd,ClassicalODECompactness.derivativeWithin_closed_interval p.continuous_V
    p.continuous_dV p.derivative_V,
    ClassicalODECompactness.derivativeWithin_closed_interval p.continuous_dV hdd p.equation⟩

/-- The constructed response obeys the actual parameter-only classical bound. -/
theorem response_bound {L mu B : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc 0 L)) (hB : 0 ≤ B)
    (hb : ∀ x ∈ Icc 0 L, |F x| ≤ B) :
    ∀ x ∈ Icc 0 L,
      |(response hL hmu F hF).V x|+|(response hL hmu F hF).dV x| ≤
        (1/mu+2*L^2+2*L)*B := (response hL hmu F hF).c1_bound hL hmu hF hB hb

end
end ChemotaxisBifurcation.NeumannResolvent
