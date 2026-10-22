module
public import ChemotaxisBifurcation.ClassicalMinimalCompactness

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.PhysicalClassicalAdapter
open Real Set MeasureTheory Filter Topology
noncomputable section

/-- Preserve the literal physical stationary profile while adapting its
closed-interval derivative data to the older classical estimate interface.
The constitutive flux derivative is derived, not supplied separately. -/
def toClassicalProfile {L a b alpha chi m beta : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
    (hm : 1 ≤ m) (hv : ∀ x ∈ Icc 0 L, 0 ≤ q.v x)
    (hN0 : q.dv 0 = 0) (hNL : q.dv L = 0) :
    StationaryMassIdentity.ClassicalProfile L a b alpha chi m beta := by
  have hbase : ∀ x ∈ Icc 0 L, 0 < 1+q.v x := by
    intro x hx; linarith [hv x hx]
  have hflux : ∀ x ∈ Icc 0 L,
      DifferentiableWithinAt ℝ (MinimalFlux.flux chi m beta q.u q.v q.dv) (Icc 0 L) x := by
    intro x hx
    exact (PhysicalStrongPositivity.flux_hasDerivWithinAt (chi := chi) (beta := beta)
      hm hbase hx (q.derivative_u x hx) (q.derivative_v x hx) (q.derivative_dv x hx)).differentiableWithinAt
  refine {
    u := q.u
    du := q.du
    ddu := q.ddu
    v := q.v
    dv := q.dv
    dJ := deriv (MinimalFlux.flux chi m beta q.u q.v q.dv)
    continuous_u := fun x hx => (q.derivative_u x hx).continuousWithinAt
    continuous_du := fun x hx => (q.derivative_du x hx).continuousWithinAt
    continuous_flux := fun x hx => (hflux x hx).continuousWithinAt
    derivative_u := fun x hx => (q.derivative_u x (Ioo_subset_Icc_self hx)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    derivative_du := fun x hx => (q.derivative_du x (Ioo_subset_Icc_self hx)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    derivative_v := fun x hx => (q.derivative_v x (Ioo_subset_Icc_self hx)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    derivative_flux := fun x hx => ((hflux x (Ioo_subset_Icc_self hx)).differentiableAt
      (Icc_mem_nhds hx.1 hx.2)).hasDerivAt
    stationary := q.stationary
    neumann_u_left := q.neumann_left
    neumann_u_right := q.neumann_right
    neumann_v_left := hN0
    neumann_v_right := hNL }

/-- The original physical signal equation gives the older signal interface
without altering any representative or derivative. -/
def toSignalData {L a b alpha chi m beta mu nu gamma : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
    (hm : 1 ≤ m) (hv : ∀ x ∈ Icc 0 L, 0 ≤ q.v x)
    (hN0 : q.dv 0 = 0) (hNL : q.dv L = 0)
    (heq : ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) :
    ClassicalLogisticEstimates.SignalData (toClassicalProfile q hm hv hN0 hNL) mu nu gamma := {
  ddv := q.ddv
  continuous_v := fun x hx => (q.derivative_v x hx).continuousWithinAt
  continuous_dv := fun x hx => (q.derivative_dv x hx).continuousWithinAt
  nonnegative_v := hv
  derivative_dv := fun x hx => (q.derivative_dv x (Ioo_subset_Icc_self hx)).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)
  stationary := heq }

end
end ChemotaxisBifurcation.PhysicalClassicalAdapter
