module
public import ChemotaxisBifurcation.PhysicalSineDecay

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.PhysicalEndpointConcentration
open Real Set MeasureTheory Filter Topology IntervalConcentration EndpointConcentration
noncomputable section

/-- Genuine finite density measure of an actual physical profile. -/
def physicalDensity {L a b alpha chi m beta : ℝ}
    (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta)
    (hL : 0 ≤ L) (hu : ∀ x ∈ Icc 0 L, 0 ≤ q.u x) : FiniteMeasure (ClosedInterval L) :=
  densityFiniteMeasure L q.u hL (fun x hx => (q.derivative_u x hx).continuousWithinAt) hu

/-- Actual strictly decreasing minimal stationary profiles concentrate at
zero as sensitivity diverges: test integrals, finite measures and peak blowup.
No pointwise/tail/sine estimate is supplied. -/
theorem decreasing_actual_concentration {L m beta mu nu gamma uStar : ℝ}
    (chi : ℕ → ℝ)
    (q : ∀ n, PhysicalStrongPositivity.StationaryProfile L 0 0 0 (chi n) m beta)
    (hL : 0 < L) (huStar : 0 < uStar) (hm : 1 ≤ m) (hbeta : 0 ≤ beta) (hmu : 0 < mu) (hnu : 0 < nu)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hu : ∀ n x, x ∈ Icc 0 L → 0 < (q n).u x)
    (hv : ∀ n x, x ∈ Icc 0 L → 0 ≤ (q n).v x)
    (hN0 : ∀ n, (q n).dv 0 = 0) (hNL : ∀ n, (q n).dv L = 0)
    (heq : ∀ n x, x ∈ Ioo 0 L → (q n).ddv x-mu*(q n).v x+nu*(q n).u x^gamma = 0)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, (q n).u x = L*uStar)
    (hanti : ∀ n, StrictAntiOn (q n).u (Icc 0 L))
    (hchi : Tendsto chi atTop atTop) :
    (∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 L) →
      Tendsto (fun n => ∫ x in (0 : ℝ)..L, f x*(q n).u x) atTop (nhds (L*uStar*f 0))) ∧
    Tendsto (fun n => (q n).u 0) atTop atTop ∧
    Tendsto (fun n => physicalDensity (q n) hL.le (fun x hx => (hu n x hx).le)) atTop
      (nhds ((L*uStar).toNNReal • (diracProba (leftEndpoint L hL.le)).toFiniteMeasure)) := by
  let u := fun n => (q n).u
  have hc : ∀ n, ContinuousOn (u n) (Icc 0 L) := fun n x hx => (q n).derivative_u x hx |>.continuousWithinAt
  have hn : ∀ n x, x ∈ Icc 0 L → 0 ≤ u n x := fun n x hx => (hu n x hx).le
  have hm' : ∀ n, AntitoneOn (u n) (Icc 0 L) := fun n => (hanti n).antitoneOn
  have hpoint := PhysicalSineDecay.interior_tendsto_zero chi q hL hm hbeta hmu hnu hgamma hgamma1
    hu hv hN0 hNL heq hmass hanti hchi
  have htail := fun delta hdelta => tendsto_tail_of_antitoneOn u hc hn hm' hdelta (hpoint delta hdelta)
  refine ⟨?_,?_,?_⟩
  · intro f hf
    exact tendsto_integral_left_of_antitoneOn hL uStar huStar u hc hn hm' hmass hpoint f hf
  · exact peak_tendsto_atTop_left hL uStar huStar u hc hn hmass htail
      (fun n => (q n).u 0) (fun n x hx => hm' n ⟨le_rfl,hL.le⟩ hx hx.1)
  · exact tendsto_dirac_left hL uStar huStar u hc hn hmass htail

/-- The corresponding actual increasing branch concentrates at L. -/
theorem increasing_actual_concentration {L m beta mu nu gamma uStar : ℝ}
    (chi : ℕ → ℝ)
    (q : ∀ n, PhysicalStrongPositivity.StationaryProfile L 0 0 0 (chi n) m beta)
    (hL : 0 < L) (huStar : 0 < uStar) (hm : 1 ≤ m) (hbeta : 0 ≤ beta) (hmu : 0 < mu) (hnu : 0 < nu)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hu : ∀ n x, x ∈ Icc 0 L → 0 < (q n).u x)
    (hv : ∀ n x, x ∈ Icc 0 L → 0 ≤ (q n).v x)
    (hN0 : ∀ n, (q n).dv 0 = 0) (hNL : ∀ n, (q n).dv L = 0)
    (heq : ∀ n x, x ∈ Ioo 0 L → (q n).ddv x-mu*(q n).v x+nu*(q n).u x^gamma = 0)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, (q n).u x = L*uStar)
    (hmono : ∀ n, StrictMonoOn (q n).u (Icc 0 L))
    (hchi : Tendsto chi atTop atTop) :
    (∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 L) →
      Tendsto (fun n => ∫ x in (0 : ℝ)..L, f x*(q n).u x) atTop (nhds (L*uStar*f L))) ∧
    Tendsto (fun n => (q n).u L) atTop atTop ∧
    Tendsto (fun n => physicalDensity (q n) hL.le (fun x hx => (hu n x hx).le)) atTop
      (nhds ((L*uStar).toNNReal • (diracProba (rightEndpoint L hL.le)).toFiniteMeasure)) := by
  let u := fun n => (q n).u
  have hc : ∀ n, ContinuousOn (u n) (Icc 0 L) := fun n x hx => (q n).derivative_u x hx |>.continuousWithinAt
  have hn : ∀ n x, x ∈ Icc 0 L → 0 ≤ u n x := fun n x hx => (hu n x hx).le
  have hm' : ∀ n, MonotoneOn (u n) (Icc 0 L) := fun n => (hmono n).monotoneOn
  have hpoint := PhysicalSineDecay.interior_tendsto_zero_increasing chi q hL hm hbeta hmu hnu hgamma hgamma1
    hu hv hN0 hNL heq hmass hmono hchi
  have htail := fun delta hdelta => tendsto_head_of_monotoneOn u hc hn hm' hdelta (hpoint delta hdelta)
  refine ⟨?_,?_,?_⟩
  · intro f hf
    exact tendsto_integral_right_of_monotoneOn hL uStar huStar u hc hn hm' hmass hpoint f hf
  · exact peak_tendsto_atTop_right hL uStar huStar u hc hn hmass htail
      (fun n => (q n).u L) (fun n x hx => hm' n hx ⟨hL.le,le_rfl⟩ hx.2)
  · exact tendsto_dirac_right hL uStar huStar u hc hn hmass htail

end
end ChemotaxisBifurcation.PhysicalEndpointConcentration
