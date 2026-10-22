module
public import ChemotaxisBifurcation.ClassicalStationaryC2Limit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.UniformComponentH2
open Real Set MeasureTheory Filter Topology
noncomputable section

/-- The actual finite-interval scalar L2 distance, with Lebesgue measure. -/
def l2Distance (L : ℝ) (f g : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ x in Icc 0 L, (f x-g x)^2)

/-- Uniform convergence of continuous representatives on a finite interval
implies convergence of their actual L2 distance; all integrands are measurable. -/
theorem l2Distance_tendsto {L : ℝ} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, ContinuousOn (f n) (Icc 0 L)) (hg : ContinuousOn g (Icc 0 L))
    (hu : TendstoUniformlyOn f g atTop (Icc 0 L)) :
    Tendsto (fun n => l2Distance L (f n) g) atTop (nhds 0) := by
  have hm : ∀ᶠ n in atTop, AEStronglyMeasurable (fun x => (f n x-g x)^2)
      (volume.restrict (Icc 0 L)) := Eventually.of_forall fun n =>
    ((hf n).sub hg |>.pow 2).aestronglyMeasurable measurableSet_Icc
  have hb : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ᵐ x ∂volume.restrict (Icc 0 L),
      ‖(f n x-g x)^2‖ ≤ C := by
    refine ⟨1, (Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one).mono ?_⟩
    intro n hn
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    have h := hn x hx
    rw [Real.dist_eq, abs_sub_comm] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (f n x-g x), abs_nonneg (f n x-g x)]
  have hl : ∀ᵐ x ∂volume.restrict (Icc 0 L),
      Tendsto (fun n => (f n x-g x)^2) atTop (nhds (0 : ℝ)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    simpa using ((hu.tendsto_at hx).sub (tendsto_const_nhds (x := g x))).pow 2
  have hi := tendsto_integral_filter_of_norm_le_const hm hb hl
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hi
  simpa only [l2Distance, Function.comp_def, integral_zero, Real.sqrt_zero] using hs

/-- Explicit sum of the three actual component L2 distances underlying the
one-dimensional H2 norm. No abstract Sobolev representation is asserted. -/
def componentH2Distance (L : ℝ) (u du ddu v dv ddv : ℝ → ℝ) : ℝ :=
  l2Distance L u v + l2Distance L du dv + l2Distance L ddu ddv

theorem componentH2Distance_tendsto {L : ℝ} {u du ddu : ℕ → ℝ → ℝ}
    {v dv ddv : ℝ → ℝ}
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hdu : ∀ n, ContinuousOn (du n) (Icc 0 L))
    (hddu : ∀ n, ContinuousOn (ddu n) (Icc 0 L))
    (hv : ContinuousOn v (Icc 0 L)) (hdv : ContinuousOn dv (Icc 0 L))
    (hddv : ContinuousOn ddv (Icc 0 L))
    (h0 : TendstoUniformlyOn u v atTop (Icc 0 L))
    (h1 : TendstoUniformlyOn du dv atTop (Icc 0 L))
    (h2 : TendstoUniformlyOn ddu ddv atTop (Icc 0 L)) :
    Tendsto (fun n => componentH2Distance L (u n) (du n) (ddu n) v dv ddv)
      atTop (nhds 0) := by
  simpa [componentH2Distance] using
    ((l2Distance_tendsto hu hv h0).add (l2Distance_tendsto hdu hdv h1)).add
      (l2Distance_tendsto hddu hddv h2)

/-- Actual bounded-sensitivity stationary profiles converge in all six uniform
components and in the explicit population/signal three-component L2 sums. -/
theorem exists_classical_componentH2_stationary_limit {L a b alpha m beta mu nu gamma X : ℝ}
    (chi : ℕ → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha)
    (hDDU : ∀ n, ContinuousOn (p n).ddu (Icc 0 L))
    (hDDV : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hnonconst : ∀ n, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, (p n).u x ≠ (p n).u y) :
    ∃ chiBar : ℝ,
    ∃ q : PhysicalStrongPositivity.StationaryProfile L a b alpha chiBar m beta,
    ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (fun n => chi (phi n)) atTop (nhds chiBar) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).u) q.u atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).du) q.du atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).v) q.v atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).dv) q.dv atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).ddu) q.ddu atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (s (phi n)).ddv) q.ddv atTop (Icc 0 L) ∧
      Tendsto (fun n => componentH2Distance L (p (phi n)).u (p (phi n)).du (p (phi n)).ddu
        q.u q.du q.ddu) atTop (nhds 0) ∧
      Tendsto (fun n => componentH2Distance L (p (phi n)).v (p (phi n)).dv (s (phi n)).ddv
        q.v q.dv q.ddv) atTop (nhds 0) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0 := by
  obtain ⟨chiBar,q,phi,hphi,hchiLim,hU,hDU,hV,hDV,hDDUlim,hDDVlim,hnn,hV0,hVL,hsig⟩ :=
    ClassicalStationaryC2Limit.exists_classical_C2_stationary_limit chi p s hL ha hb halpha
      hm hm1 hbeta hmu hnu hgamma hgamma1 hDDU hDDV hchi hpos hnonconst
  have hqu : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
  have hqdu : ContinuousOn q.du (Icc 0 L) := fun x hx => (q.derivative_du x hx).continuousWithinAt
  have hqv : ContinuousOn q.v (Icc 0 L) := fun x hx => (q.derivative_v x hx).continuousWithinAt
  have hqdv : ContinuousOn q.dv (Icc 0 L) := fun x hx => (q.derivative_dv x hx).continuousWithinAt
  refine ⟨chiBar,q,phi,hphi,hchiLim,hU,hDU,hV,hDV,hDDUlim,hDDVlim,?_,?_,hnn,hV0,hVL,hsig⟩
  · exact componentH2Distance_tendsto (fun n => (p (phi n)).continuous_u)
      (fun n => (p (phi n)).continuous_du) (fun n => hDDU (phi n))
      hqu hqdu q.continuous_ddu hU hDU hDDUlim
  · exact componentH2Distance_tendsto (fun n => (s (phi n)).continuous_v)
      (fun n => (s (phi n)).continuous_dv) (fun n => hDDV (phi n))
      hqv hqdv q.continuous_ddv hV hDV hDDVlim

end
end ChemotaxisBifurcation.UniformComponentH2
