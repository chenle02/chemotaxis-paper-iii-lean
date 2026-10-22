module
public import ChemotaxisBifurcation.StationaryCompactness

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.StationaryLimitProfile
open Real Set StationaryODEState
noncomputable section

/-- The continuous augmented vector field is exactly the stationary
population equation on its physical nonnegative half-space. -/
theorem population_identity (a b alpha m beta mu nu gamma : ℝ) (z : State)
    (hm : 1 ≤ m) (halpha : 0 ≤ alpha) (hu : 0 ≤ z.2.1.1) (hv : 0 ≤ z.2.2.1) :
    (field a b alpha m beta mu nu gamma z).2.1.2 -
      (z.1*m*z.2.1.1^(m-1)*z.2.2.2/(1+z.2.2.1)^beta*z.2.1.2 +
        z.1*z.2.1.1^m*(signalRHS mu nu gamma z/(1+z.2.2.1)^beta-
          beta*z.2.2.2^2/(1+z.2.2.1)^(beta+1))) +
      a*z.2.1.1-b*z.2.1.1^(1+alpha) = 0 := by
  have hum : z.2.1.1^m = z.2.1.1^(m-1)*z.2.1.1 := by
    have hh := Real.rpow_add_of_nonneg hu (show 0 ≤ m-1 by linarith) zero_le_one
    simpa only [sub_add_cancel,Real.rpow_one] using hh
  have hua : z.2.1.1^(1+alpha) = z.2.1.1^alpha*z.2.1.1 := by
    rw [add_comm,Real.rpow_add_of_nonneg hu halpha zero_le_one,Real.rpow_one]
  have hw : offset z = 1+z.2.2.1 := max_eq_right (by linarith)
  simp only [field,zero,drift,hw,hum,hua]
  ring

/-- The extracted state yields a literal classical population stationary
profile, with the original differential equation and one-sided endpoint
regularity proved rather than supplied. This is the data consumed by the
physical strong-positivity and local-uniqueness bridges. -/
def toPopulationProfile {L a b alpha m beta mu nu gamma : ℝ}
    (g : ℝ → State) (hg : ContinuousOn g (Icc 0 L))
    (hd : ∀ x ∈ Icc 0 L,
      HasDerivWithinAt g (field a b alpha m beta mu nu gamma (g x)) (Icc 0 L) x)
    (hchi : ∀ x ∈ Icc 0 L, (g x).1 = (g 0).1)
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ (g x).2.1.1 ∧ 0 ≤ (g x).2.2.1)
    (hm : 1 ≤ m) (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma)
    (hN0 : (g 0).2.1.2 = 0) (hNL : (g L).2.1.2 = 0) :
    PhysicalStrongPositivity.StationaryProfile L a b alpha (g 0).1 m beta := by
  have hH := continuous_field a b alpha m beta mu nu gamma halpha hm hgamma
  have hdu : ∀ x ∈ Icc 0 L, HasDerivWithinAt (fun y => (g y).2.1.1)
      (g x).2.1.2 (Icc 0 L) x := fun x hx => (hd x hx).snd.fst.fst
  have hddu : ∀ x ∈ Icc 0 L, HasDerivWithinAt (fun y => (g y).2.1.2)
      (field a b alpha m beta mu nu gamma (g x)).2.1.2 (Icc 0 L) x :=
    fun x hx => (hd x hx).snd.fst.snd
  have hdv : ∀ x ∈ Icc 0 L, HasDerivWithinAt (fun y => (g y).2.2.1)
      (g x).2.2.2 (Icc 0 L) x := fun x hx => (hd x hx).snd.snd.fst
  have hddv : ∀ x ∈ Icc 0 L, HasDerivWithinAt (fun y => (g y).2.2.2)
      (signalRHS mu nu gamma (g x)) (Icc 0 L) x := fun x hx => (hd x hx).snd.snd.snd
  have hbase : ∀ x ∈ Icc 0 L, 0 < 1+(g x).2.2.1 := by
    intro x hx; linarith [(hnonneg x hx).2]
  refine {
    u := fun x => (g x).2.1.1
    du := fun x => (g x).2.1.2
    ddu := fun x => (field a b alpha m beta mu nu gamma (g x)).2.1.2
    v := fun x => (g x).2.2.1
    dv := fun x => (g x).2.2.2
    ddv := fun x => signalRHS mu nu gamma (g x)
    derivative_u := hdu
    derivative_du := hddu
    derivative_v := hdv
    derivative_dv := hddv
    continuous_ddu := (hH.comp_continuousOn hg).snd.fst.snd
    continuous_ddv := (hH.comp_continuousOn hg).snd.snd.snd
    stationary := ?_
    neumann_left := hN0
    neumann_right := hNL }
  intro x hx
  have hx' := Ioo_subset_Icc_self hx
  have hflux := (PhysicalStrongPositivity.flux_hasDerivWithinAt (chi := (g 0).1) (beta := beta)
    (u := fun y => (g y).2.1.1) (du := fun y => (g y).2.1.2)
    (v := fun y => (g y).2.2.1) (dv := fun y => (g y).2.2.2)
    (ddv := fun y => signalRHS mu nu gamma (g y)) hm hbase hx' (hdu x hx') (hdv x hx') (hddv x hx')).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  rw [hflux.deriv]
  have hi := population_identity a b alpha m beta mu nu gamma (g x) hm halpha
    (hnonneg x hx').1 (hnonneg x hx').2
  rw [hchi x hx'] at hi
  simpa only [AmbientClosure.driftCoeff] using hi

/-- The same extracted profile solves the actual signal equation, including
its continuous second derivative. -/
theorem signal_identity (mu nu gamma : ℝ) (g : ℝ → State) (x : ℝ) :
    signalRHS mu nu gamma (g x)-mu*(g x).2.2.1+nu*(g x).2.1.1^gamma = 0 := by
  dsimp [signalRHS]
  ring

end
end ChemotaxisBifurcation.StationaryLimitProfile
