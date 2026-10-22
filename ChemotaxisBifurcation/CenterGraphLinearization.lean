module
public import ChemotaxisBifurcation.RemainderAxis

@[expose] public section

/-! The trivial-axis derivative of the actual reduced field follows by
restricting the full field to a differentiable graph in the kernel of its
modal projection. No zero graph derivative away from the critical parameter
is assumed; projection annihilates that derivative. Original time and the
physical amplitude coordinate are retained. Center-graph existence and the
full-field derivative/eigenprojection relation remain analytic inputs. -/
set_option autoImplicit false
namespace ChemotaxisBifurcation.CenterGraphLinearization
open Filter Topology
noncomputable section

/-- Restriction to the stable graph preserves the modal eigenvalue even when
its tangent vector has a nonzero stable component. -/
theorem derivative_of_restriction
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Pi : E →L[ℝ] ℝ) (PiOut : G →L[ℝ] ℝ) (phi : E) (L : E →L[ℝ] G)
    (F : E → G) (h : ℝ → E) (dh : E) (f : ℝ → ℝ) (sigma : ℝ)
    (hphi : Pi phi = 1) (hzero : h 0 = 0)
    (hh : HasDerivAt h dh 0)
    (hstable : ∀ᶠ s in nhds (0 : ℝ), Pi (h s) = 0)
    (hF : HasFDerivAt F L 0)
    (heigen : ∀ w : E, PiOut (L w) = sigma * Pi w)
    (hrestriction : ∀ᶠ s in nhds (0 : ℝ), f s = PiOut (F (s • phi + h s))) :
    HasDerivAt f sigma 0 := by
  have hproj := Pi.hasFDerivAt.comp_hasDerivAt 0 hh
  have hzeroDeriv : HasDerivAt (fun s : ℝ => Pi (h s)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hstable
  have hdh : Pi dh = 0 := hproj.unique hzeroDeriv
  have hcurve : HasDerivAt (fun s : ℝ => s • phi + h s) (phi + dh) 0 := by
    simpa only [one_smul, id_eq, _root_.Pi.add_apply] using ((hasDerivAt_id (0 : ℝ)).smul_const phi).fun_add hh
  have hFcurve : HasDerivAt (fun s : ℝ => F (s • phi + h s)) (L (phi + dh)) 0 := by
    have hbase : HasFDerivAt F L ((0 : ℝ) • phi + h 0) := by
      simpa only [zero_smul, hzero, add_zero] using hF
    exact hbase.comp_hasDerivAt 0 hcurve
  have hresult := PiOut.hasFDerivAt.comp_hasDerivAt 0 hFcurve
  have hvalue : PiOut (L (phi + dh)) = sigma := by
    rw [heigen, map_add, hphi, hdh]
    ring
  rw [hvalue] at hresult
  exact hresult.congr_of_eventuallyEq hrestriction


/-- Analytic center-graph and full-field data in physical parameter eta,
physical amplitude s and original time. This has no reduced-field derivative
or zero stable-graph tangent hypothesis. Domain and range may differ. -/
structure RestrictionData
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : PhysicalParams) (x beta : ℝ) (f : ℝ → ℝ → ℝ) (r : ℝ) where
  projection : E →L[ℝ] ℝ
  outputProjection : G →L[ℝ] ℝ
  phi : E
  field : ℝ → E → G
  linearization : ℝ → E →L[ℝ] G
  graph : ℝ → ℝ → E
  graphDerivative : ℝ → E
  normalized : projection phi = 1
  zero : ∀ eta, |eta| ≤ r → graph eta 0 = 0
  differentiable : ∀ eta, |eta| ≤ r → HasDerivAt (graph eta) (graphDerivative eta) 0
  stable : ∀ eta, |eta| ≤ r → ∀ᶠ s in nhds (0 : ℝ), projection (graph eta s) = 0
  fieldDerivative : ∀ eta, |eta| ≤ r → HasFDerivAt (field eta) (linearization eta) 0
  eigenprojection : ∀ eta, |eta| ≤ r → ∀ w,
    outputProjection (linearization eta w) =
      RemainderAxis.sigmaN0 p x beta (p.chiStar x beta + eta) * projection w
  restriction : ∀ eta, |eta| ≤ r → ∀ᶠ s in nhds (0 : ℝ),
    f eta s = outputProjection (field eta (s • phi + graph eta s))

/-- The named trivial-branch linearization assumption is derived from the
actual restriction and full-field derivative, not supplied as an input. -/
theorem trivialBranchLinearization_of_restriction
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {p : PhysicalParams} {x beta r : ℝ} {f : ℝ → ℝ → ℝ}
    (d : RestrictionData (E := E) (G := G) p x beta f r) :
    RemainderAxis.TrivialBranchLinearization p x beta f r := by
  intro eta heta
  exact derivative_of_restriction d.projection d.outputProjection d.phi
    (d.linearization eta) (d.field eta) (d.graph eta) (d.graphDerivative eta)
    (f eta) _ d.normalized (d.zero eta heta) (d.differentiable eta heta)
    (d.stable eta heta) (d.fieldDerivative eta heta) (d.eigenprojection eta heta)
    (d.restriction eta heta)

/-- The exact affine physical eigenvalue slope is inherited without changing
amplitude, parameter or time coordinates. -/
theorem derivative_eq_physical_slope
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {p : PhysicalParams} {x beta r : ℝ} {f : ℝ → ℝ → ℝ}
    (d : RestrictionData (E := E) (G := G) p x beta f r)
    (hp : PhysicalModeGuards.PositiveModeParameters p) (hx : 0 < x)
    (eta : ℝ) (heta : |eta| ≤ r) :
    HasDerivAt (f eta) (p.alphaN0 x beta * eta) 0 := by
  rw [← RemainderAxis.sigmaN0_shift p x beta eta hp hx]
  exact trivialBranchLinearization_of_restriction d eta heta

/-- Reach the existing remainder-bound consumer with no assumed reduced
trivial-axis derivative. Smoothness and point-jet inputs stay explicit. -/
theorem model_final_interface_of_restriction
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {p : PhysicalParams} {x beta betaN0 r : ℝ} {f : ℝ → ℝ → ℝ}
    (d : RestrictionData (E := E) (G := G) p x beta f r)
    (U : Set (ℝ × ℝ)) (hp : PhysicalModeGuards.PositiveModeParameters p) (hx : 0 < x)
    (h : RemainderFromJet.JetHyp
      (Function.uncurry (RemainderAxis.remainderOf p x beta betaN0 f)) U r) :
    ∃ C, 0 ≤ C ∧
      (∀ eta s, |eta| ≤ r → |s| ≤ r →
        |RemainderAxis.remainderOf p x beta betaN0 f eta s| ≤
          C * (s ^ 2 * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4)) ∧
      (∀ eta s, |eta| ≤ r → |s| ≤ r →
        |RemainderFromJet.jetRs (RemainderAxis.remainderOf p x beta betaN0 f) eta s| ≤
          C * (|s| * eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3)) ∧
      (∀ eta s, MixedRemainder.reducedField (p.alphaN0 x beta) betaN0
        (RemainderAxis.remainderOf p x beta betaN0 f) eta s = f eta s) :=
  RemainderAxis.model_final_interface p x beta betaN0 f U r hp hx h
    (trivialBranchLinearization_of_restriction d)

end
end ChemotaxisBifurcation.CenterGraphLinearization
