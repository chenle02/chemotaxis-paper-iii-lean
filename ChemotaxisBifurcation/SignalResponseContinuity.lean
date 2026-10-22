module
public import ChemotaxisBifurcation.UniformHolderAlgebra
public import ChemotaxisBifurcation.PhysicalClassicalAdapter

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.SignalResponseContinuity
open Real Set MeasureTheory Filter Topology
noncomputable section

/-- The literal signal equation gives a signed elliptic profile, without
any separately assumed response or resolvent identity. -/
def signalProfile {L a b alpha chi m beta mu nu gamma : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
    (hN0 : q.dv 0 = 0) (hNL : q.dv L = 0)
    (heq : ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) :
    SignedEllipticEnergy.Profile L mu (fun x => nu*q.u x^gamma) := {
  V := q.v
  dV := q.dv
  continuous_V := fun x hx => (q.derivative_v x hx).continuousWithinAt
  continuous_dV := fun x hx => (q.derivative_dv x hx).continuousWithinAt
  derivative_V := fun x hx => (q.derivative_v x (Ioo_subset_Icc_self hx)).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)
  equation := by
    intro x hx
    convert (q.derivative_dv x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2) using 1
    linarith [heq x hx]
  neumann_left := hN0
  neumann_right := hNL }

/-- Difference of actual signed elliptic solutions satisfies the actual
difference equation and Neumann data. -/
def differenceProfile {L mu : ℝ} {F G : ℝ → ℝ}
    (q : SignedEllipticEnergy.Profile L mu F) (r : SignedEllipticEnergy.Profile L mu G) :
    SignedEllipticEnergy.Profile L mu (fun x => F x-G x) := {
  V := fun x => q.V x-r.V x
  dV := fun x => q.dV x-r.dV x
  continuous_V := q.continuous_V.sub r.continuous_V
  continuous_dV := q.continuous_dV.sub r.continuous_dV
  derivative_V := fun x hx => (q.derivative_V x hx).sub (r.derivative_V x hx)
  equation := by
    intro x hx
    convert (q.equation x hx).sub (r.equation x hx) using 1; ring
  neumann_left := by simp only [q.neumann_left,r.neumann_left,sub_self]
  neumann_right := by simp only [q.neumann_right,r.neumann_right,sub_self] }

/-- The actual signal equation holds also for the continuous endpoint
second derivative representatives, by density of the open interval. -/
theorem ddv_eq_rhs {L a b alpha chi m beta mu nu gamma : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
    (hL : 0 < L) (hu : ∀ x ∈ Icc 0 L, 0 < q.u x)
    (heq : ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) :
    ∀ x ∈ Icc 0 L, q.ddv x = mu*q.v x-nu*q.u x^gamma := by
  have huc : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
  have hvc : ContinuousOn q.v (Icc 0 L) := fun x hx => (q.derivative_v x hx).continuousWithinAt
  have hc : ContinuousOn (fun x => mu*q.v x-nu*q.u x^gamma) (Icc 0 L) := (hvc.const_mul mu).sub
    ((huc.rpow_const (fun x hx => Or.inl (hu x hx).ne')).const_mul nu)
  have hclosed := isClosed_Icc.isClosed_eq q.continuous_ddv hc
  have hin : Ioo 0 L ⊆ {x ∈ Icc 0 L | q.ddv x = mu*q.v x-nu*q.u x^gamma} := by
    intro x hx; exact ⟨Ioo_subset_Icc_self hx,by linarith [heq x hx]⟩
  intro x hx
  have hx' : x ∈ closure (Ioo 0 L) := by rwa [closure_Ioo hL.ne]
  exact (closure_minimal hin hclosed hx').2

/-- Actual signal responses are uniformly C2 Lipschitz in the population
sup distance on each fixed positive compact population range. The constant is
chosen before both actual physical profiles and their sensitivities. -/
theorem exists_pair_bound (L mu nu gamma A B : ℝ) (hL : 0 < L) (hmu : 0 < mu) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ {a b alpha chi chi' m beta : ℝ}
      (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
      (r : PhysicalStrongPositivity.StationaryProfile L a b alpha chi' m beta),
      (∀ x ∈ Icc 0 L, q.u x ∈ Icc A B) → (∀ x ∈ Icc 0 L, r.u x ∈ Icc A B) →
      q.dv 0 = 0 → q.dv L = 0 → r.dv 0 = 0 → r.dv L = 0 →
      (∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) →
      (∀ x ∈ Ioo 0 L, r.ddv x-mu*r.v x+nu*r.u x^gamma = 0) →
      ∀ eta : ℝ, 0 ≤ eta → (∀ x ∈ Icc 0 L, |q.u x-r.u x| ≤ eta) →
      ∀ x ∈ Icc 0 L,
        |q.v x-r.v x|+|q.dv x-r.dv x| ≤ K*eta ∧ |q.ddv x-r.ddv x| ≤ K*eta := by
  obtain ⟨M,hM,hml⟩ := UniformHolderAlgebra.Control.scalar_rpow_lipschitz gamma A B hA.le (Or.inl hA)
  let D := |nu| *M
  have hD : 0 ≤ D := mul_nonneg (abs_nonneg _) hM
  let E := 1/mu+2*L^2+2*L
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let K := E*D+(|mu| *E+1)*D+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro a b alpha chi chi' m beta q r hq hr hq0 hqL hr0 hrL heq her eta heta hdist x hx
  have hqu : ∀ y ∈ Icc 0 L, 0 < q.u y := fun y hy => hA.trans_le (hq y hy).1
  have hru : ∀ y ∈ Icc 0 L, 0 < r.u y := fun y hy => hA.trans_le (hr y hy).1
  let p := differenceProfile (signalProfile q hq0 hqL heq) (signalProfile r hr0 hrL her)
  have hqc : ContinuousOn q.u (Icc 0 L) := fun y hy => (q.derivative_u y hy).continuousWithinAt
  have hrc : ContinuousOn r.u (Icc 0 L) := fun y hy => (r.derivative_u y hy).continuousWithinAt
  have hFc : ContinuousOn (fun y => nu*q.u y^gamma-nu*r.u y^gamma) (Icc 0 L) :=
    ((hqc.rpow_const (fun y hy => Or.inl (hqu y hy).ne')).const_mul nu).sub
      ((hrc.rpow_const (fun y hy => Or.inl (hru y hy).ne')).const_mul nu)
  have hFb : ∀ y ∈ Icc 0 L, |nu*q.u y^gamma-nu*r.u y^gamma| ≤ D*eta := by
    intro y hy
    rw [← mul_sub,abs_mul]
    have hp := hml (r.u y) (hr y hy) (q.u y) (hq y hy)
    have hh := mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_left (hdist y hy) hM)) (abs_nonneg nu)
    dsimp [D]
    nlinarith
  have hc1 : |q.v x-r.v x|+|q.dv x-r.dv x| ≤ E*(D*eta) :=
    p.c1_bound hL hmu hFc (mul_nonneg hD heta) hFb x hx
  have hK1 : E*D ≤ K := by dsimp [K]; nlinarith [mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg mu) hE) zero_le_one) hD]
  have hK2 : (|mu| *E+1)*D ≤ K := by dsimp [K]; nlinarith [mul_nonneg hE hD]
  constructor
  · exact hc1.trans (by nlinarith [mul_le_mul_of_nonneg_right hK1 heta])
  · rw [ddv_eq_rhs q hL hqu heq x hx,ddv_eq_rhs r hL hru her x hx]
    have hval : |q.v x-r.v x| ≤ E*(D*eta) := by linarith [abs_nonneg (q.dv x-r.dv x)]
    calc |mu*q.v x-nu*q.u x^gamma-(mu*r.v x-nu*r.u x^gamma)| =
        |mu*(q.v x-r.v x)-(nu*q.u x^gamma-nu*r.u x^gamma)| := by congr 1; ring
      _ ≤ |mu*(q.v x-r.v x)|+|nu*q.u x^gamma-nu*r.u x^gamma| := abs_sub _ _
      _ ≤ |mu| *(E*(D*eta))+D*eta := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hval (abs_nonneg _)) (hFb x hx)
      _ ≤ K*eta := by nlinarith [mul_le_mul_of_nonneg_right hK2 heta]

end
end ChemotaxisBifurcation.SignalResponseContinuity
