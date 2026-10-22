module
public import ChemotaxisBifurcation.IntervalStrongPositivity

@[expose] public section

/-! Strong positivity for the literal classical stationary population equation.
The physical drift sign is positive in u''=drift*u'-zero*u. This module
derives the constitutive-flux derivative and coefficient identification;
classical regularity and the original stationary equation remain inputs. -/
set_option autoImplicit false
namespace ChemotaxisBifurcation.PhysicalStrongPositivity
open Set
noncomputable section

/-- Differentiate the actual power-law chemotactic flux, including at zeros
of u when m>=1. The m=1 case uses the ordinary rpow derivative at zero. -/
theorem flux_hasDerivWithinAt {L chi m beta : ℝ} {u v du dv ddv : ℝ → ℝ}
    (hm : 1 ≤ m) (hbase : ∀ y ∈ Icc 0 L, 0 < 1 + v y)
    {x : ℝ} (hx : x ∈ Icc 0 L)
    (hu : HasDerivWithinAt u (du x) (Icc 0 L) x)
    (hv : HasDerivWithinAt v (dv x) (Icc 0 L) x)
    (hdv : HasDerivWithinAt dv (ddv x) (Icc 0 L) x) :
    HasDerivWithinAt (MinimalFlux.flux chi m beta u v dv)
      (AmbientClosure.driftCoeff chi m beta u v dv x * du x +
        chi * u x ^ m * (ddv x / (1 + v x) ^ beta -
          beta * dv x ^ 2 / (1 + v x) ^ (beta + 1))) (Icc 0 L) x := by
  have hp := hu.rpow_const (p := m) (Or.inr hm)
  have hn := (hv.const_add 1).rpow_const (p := -beta)
    (Or.inl (hbase x hx).ne')
  have hh := ((hp.fun_mul hn).fun_mul hdv).const_mul chi
  have hpow : (1 + v x) ^ (-beta - 1) = ((1 + v x) ^ (beta + 1))⁻¹ := by
    rw [show -beta - 1 = -(beta + 1) by ring, Real.rpow_neg (hbase x hx).le]
  have hpow0 : (1 + v x) ^ (-beta) = ((1 + v x) ^ beta)⁻¹ :=
    Real.rpow_neg (hbase x hx).le beta
  have hvalue : chi *
      ((du x * m * u x ^ (m - 1) * (1 + v x) ^ (-beta) +
        u x ^ m * (dv x * -beta * (1 + v x) ^ (-beta - 1))) * dv x +
          (u x ^ m * (1 + v x) ^ (-beta)) * ddv x) =
      AmbientClosure.driftCoeff chi m beta u v dv x * du x +
        chi * u x ^ m * (ddv x / (1 + v x) ^ beta -
          beta * dv x ^ 2 / (1 + v x) ^ (beta + 1)) := by
    rw [hpow, hpow0]
    unfold AmbientClosure.driftCoeff
    simp only [div_eq_mul_inv]
    ring
  rw [hvalue] at hh
  apply hh.congr
  · intro y hy
    simp only [MinimalFlux.flux, Real.rpow_neg (hbase y hy).le, div_eq_mul_inv]
    ring
  · simp only [MinimalFlux.flux, Real.rpow_neg (hbase x hx).le, div_eq_mul_inv]
    ring


/-- Ordinary continuous classical data give continuous physical coefficients,
including at zeros of u for m>=1. -/
theorem continuous_coefficients {L a b alpha chi m beta : ℝ}
    {u v dv ddv : ℝ → ℝ} (hm : 1 ≤ m) (halpha : 0 ≤ alpha)
    (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hdv : ContinuousOn dv (Icc 0 L)) (hddv : ContinuousOn ddv (Icc 0 L))
    (hbase : ∀ x ∈ Icc 0 L, 0 < 1 + v x) :
    ContinuousOn (AmbientClosure.driftCoeff chi m beta u v dv) (Icc 0 L) ∧
      ContinuousOn (AmbientClosure.zeroCoeff a b alpha chi m beta u v dv ddv) (Icc 0 L) := by
  have hum : ContinuousOn (fun x => u x ^ (m - 1)) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr (by linarith)
  have hua : ContinuousOn (fun x => u x ^ alpha) (Icc 0 L) :=
    hu.rpow_const fun _ _ => Or.inr halpha
  have hw : ContinuousOn (fun x => 1 + v x) (Icc 0 L) := continuousOn_const.add hv
  have hwb : ContinuousOn (fun x => (1 + v x) ^ beta) (Icc 0 L) :=
    hw.rpow_const fun x hx => Or.inl (hbase x hx).ne'
  have hwb1 : ContinuousOn (fun x => (1 + v x) ^ (beta + 1)) (Icc 0 L) :=
    hw.rpow_const fun x hx => Or.inl (hbase x hx).ne'
  have hne : ∀ x ∈ Icc 0 L, (1 + v x) ^ beta ≠ 0 := fun x hx =>
    (Real.rpow_pos_of_pos (hbase x hx) _).ne'
  have hne1 : ∀ x ∈ Icc 0 L, (1 + v x) ^ (beta + 1) ≠ 0 := fun x hx =>
    (Real.rpow_pos_of_pos (hbase x hx) _).ne'
  exact ⟨((continuousOn_const.mul hum).mul hdv).div hwb hne,
    (continuousOn_const.sub (continuousOn_const.mul hua)).sub
      ((continuousOn_const.mul hum).mul ((hddv.div hwb hne).sub
        ((continuousOn_const.mul (hdv.pow 2)).div hwb1 hne1)))⟩

/-- Factor the actual stationary population equation into its linear form.
The physical drift enters with a positive sign on the right-hand side. -/
theorem stationary_linear_identity {a b alpha chi m beta U V D DV DDV DDU : ℝ}
    (hm : 1 ≤ m) (halpha : 0 ≤ alpha) (hU : 0 ≤ U)
    (heq : DDU - (chi * m * U ^ (m - 1) * DV / (1 + V) ^ beta * D +
      chi * U ^ m * (DDV / (1 + V) ^ beta - beta * DV ^ 2 / (1 + V) ^ (beta + 1))) +
      a * U - b * U ^ (1 + alpha) = 0) :
    DDU = -(a - b * U ^ alpha - chi * U ^ (m - 1) *
      (DDV / (1 + V) ^ beta - beta * DV ^ 2 / (1 + V) ^ (beta + 1))) * U +
      (chi * m * U ^ (m - 1) * DV / (1 + V) ^ beta) * D := by
  have hpow : U ^ m = U ^ (m - 1) * U := by
    have h := Real.rpow_add_of_nonneg hU (show 0 ≤ m - 1 by linarith) zero_le_one
    simpa only [sub_add_cancel, Real.rpow_one] using h
  have hreact : U ^ (1 + alpha) = U ^ alpha * U := by
    rw [add_comm, Real.rpow_add_of_nonneg hU halpha zero_le_one, Real.rpow_one]
  rw [hpow, hreact] at heq
  linear_combination heq


/-- Classical data for the literal population equation. The stationary
identity is required only in the open interval; no linear ODE or positivity
conclusion is a field. First derivatives at endpoints are one-sided. -/
structure StationaryProfile (L a b alpha chi m beta : ℝ) where
  u : ℝ → ℝ
  du : ℝ → ℝ
  ddu : ℝ → ℝ
  v : ℝ → ℝ
  dv : ℝ → ℝ
  ddv : ℝ → ℝ
  derivative_u : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (du x) (Icc 0 L) x
  derivative_du : ∀ x ∈ Icc 0 L, HasDerivWithinAt du (ddu x) (Icc 0 L) x
  derivative_v : ∀ x ∈ Icc 0 L, HasDerivWithinAt v (dv x) (Icc 0 L) x
  derivative_dv : ∀ x ∈ Icc 0 L, HasDerivWithinAt dv (ddv x) (Icc 0 L) x
  continuous_ddu : ContinuousOn ddu (Icc 0 L)
  continuous_ddv : ContinuousOn ddv (Icc 0 L)
  stationary : ∀ x ∈ Ioo 0 L,
    ddu x - deriv (MinimalFlux.flux chi m beta u v dv) x +
      a * u x - b * u x ^ (1 + alpha) = 0
  neumann_left : du 0 = 0
  neumann_right : du L = 0

namespace StationaryProfile
variable {L a b alpha chi m beta : ℝ}

/-- Identify the actual classical population equation with the linear ODE
on the closed interval. Endpoint identities follow by continuity from the
original open-interval equation. Correct coefficients: -zeroCoeff,+driftCoeff. -/
def toLinearNeumannProfile (p : StationaryProfile L a b alpha chi m beta)
    (hL : 0 < L) (hm : 1 ≤ m) (halpha : 0 ≤ alpha)
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ p.u x)
    (hbase : ∀ x ∈ Icc 0 L, 0 < 1 + p.v x) :
    IntervalStrongPositivity.LinearNeumannProfile L := by
  have hu : ContinuousOn p.u (Icc 0 L) := fun x hx => (p.derivative_u x hx).continuousWithinAt
  have hdu : ContinuousOn p.du (Icc 0 L) := fun x hx => (p.derivative_du x hx).continuousWithinAt
  have hv : ContinuousOn p.v (Icc 0 L) := fun x hx => (p.derivative_v x hx).continuousWithinAt
  have hdv : ContinuousOn p.dv (Icc 0 L) := fun x hx => (p.derivative_dv x hx).continuousWithinAt
  obtain ⟨hB, hC⟩ := continuous_coefficients (a := a) (b := b) hm halpha hu hv hdv
    p.continuous_ddv hbase
  let A := fun x => -AmbientClosure.zeroCoeff a b alpha chi m beta p.u p.v p.dv p.ddv x
  let B := AmbientClosure.driftCoeff chi m beta p.u p.v p.dv
  have hA : ContinuousOn A (Icc 0 L) := hC.neg
  have hB' : ContinuousOn B (Icc 0 L) := hB
  have hres : ContinuousOn (fun x => p.ddu x - (A x * p.u x + B x * p.du x))
      (Icc 0 L) := p.continuous_ddu.sub ((hA.mul hu).add (hB'.mul hdu))
  have hclosed : IsClosed {x ∈ Icc 0 L | p.ddu x - (A x * p.u x + B x * p.du x) = 0} :=
    isClosed_Icc.isClosed_eq hres continuousOn_const
  have hin : Ioo 0 L ⊆ {x ∈ Icc 0 L | p.ddu x - (A x * p.u x + B x * p.du x) = 0} := by
    intro x hx
    have hx' := Ioo_subset_Icc_self hx
    have hflux := (flux_hasDerivWithinAt (chi := chi) (beta := beta) hm hbase hx' (p.derivative_u x hx')
      (p.derivative_v x hx') (p.derivative_dv x hx')).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    have hstation := p.stationary x hx
    rw [hflux.deriv] at hstation
    have hlin := stationary_linear_identity hm halpha (hnonneg x hx') hstation
    refine ⟨hx', ?_⟩
    change p.ddu x - (-AmbientClosure.zeroCoeff a b alpha chi m beta p.u p.v p.dv p.ddv x *
      p.u x + AmbientClosure.driftCoeff chi m beta p.u p.v p.dv x * p.du x) = 0
    unfold AmbientClosure.zeroCoeff AmbientClosure.driftCoeff
    rw [hlin]
    ring
  have hall := closure_minimal hin hclosed
  have heq : ∀ x ∈ Icc 0 L, p.ddu x = A x * p.u x + B x * p.du x := by
    intro x hx
    have hmem : x ∈ closure (Ioo 0 L) := by rwa [closure_Ioo hL.ne]
    exact sub_eq_zero.mp (hall hmem).2
  exact ⟨p.u, p.du, A, B, p.derivative_u,
    fun x hx => by rw [← heq x hx]; exact p.derivative_du x hx,
    hA, hB', p.neumann_left, p.neumann_right⟩

/-- Strict positivity for all given nonnegative classical stationary
population solutions with one positive value. No separate linearization or
strong maximum principle is assumed. -/
theorem positive_of_nonnegative (p : StationaryProfile L a b alpha chi m beta)
    (hL : 0 < L) (hm : 1 ≤ m) (halpha : 0 ≤ alpha)
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ p.u x)
    (hbase : ∀ x ∈ Icc 0 L, 0 < 1 + p.v x)
    (hpos : ∃ x ∈ Icc 0 L, 0 < p.u x) :
    ∀ x ∈ Icc 0 L, 0 < p.u x := by
  let q := p.toLinearNeumannProfile hL hm halpha hnonneg hbase
  have hqu : q.u = p.u := by rfl
  rw [← hqu] at hnonneg hpos ⊢
  exact IntervalStrongPositivity.positive_of_nonnegative hL q.derivative_u q.derivative_du
    q.continuous_a q.continuous_b q.neumann_left q.neumann_right hnonneg hpos

end StationaryProfile

end
end ChemotaxisBifurcation.PhysicalStrongPositivity
