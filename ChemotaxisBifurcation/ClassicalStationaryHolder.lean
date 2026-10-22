module
public import ChemotaxisBifurcation.StationaryHolderField

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalStationaryHolder
open Real Set MeasureTheory Filter Topology StationaryODEState UniformHolderAlgebra
noncomputable section
variable {ι : Type*}

theorem logistic_state_bound {L a b alpha m beta mu nu gamma X : ℝ}
    (chi : ι → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha)
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hnonconst : ∀ n, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, (p n).u x ≠ (p n).u y) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n x, x ∈ Icc 0 L →
      ‖point (chi n) ((p n).u x) ((p n).du x) ((p n).v x) ((p n).dv x)‖ ≤ B := by
  let U := ClassicalLogisticEstimates.gronwallC1Envelope L a b alpha gamma nu X m
  have hU : 0 ≤ U := by
    dsimp [U,ClassicalLogisticEstimates.gronwallC1Envelope,SpikeEstimates.gronwallPopulationBound]
    positivity
  let V := (1/mu+2*L^2+2*L)*(nu*U^gamma)
  refine ⟨max (max X U) (max V 0),le_trans (le_max_right _ _) (le_max_right _ _),?_⟩
  intro n x hx
  have huc := ClassicalLogisticEstimates.c1_gronwall_bound (p n) (s n) hL ha hb halpha
    hgamma hgamma1 hm hm1 hbeta hmu.le hnu (hchi n) (hpos n) (hnonconst n)
  let F := fun y => nu*(p n).u y^gamma
  have hFc : ContinuousOn F (Icc 0 L) :=
    continuousOn_const.mul ((p n).continuous_u.rpow_const (fun _ _ => Or.inr hgamma.le))
  let q : SignedEllipticEnergy.Profile L mu F := {
    V := (p n).v
    dV := (p n).dv
    continuous_V := (s n).continuous_v
    continuous_dV := (s n).continuous_dv
    derivative_V := (p n).derivative_v
    equation := by
      intro y hy
      convert (s n).derivative_dv y hy using 1
      dsimp [F]
      linarith [(s n).stationary y hy]
    neumann_left := (p n).neumann_v_left
    neumann_right := (p n).neumann_v_right }
  have hFb : ∀ y ∈ Icc 0 L, |F y| ≤ nu*U^gamma := by
    intro y hy
    have huly : (p n).u y ≤ U := (le_abs_self _).trans (huc y hy).1
    dsimp [F]
    rw [abs_mul,abs_of_nonneg hnu,abs_of_nonneg (Real.rpow_nonneg (hpos n y hy).le _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hpos n y hy).le huly hgamma.le) hnu
  have hvc : |(p n).v x|+|(p n).dv x| ≤ V :=
    q.c1_bound hL hmu hFc (by positivity) hFb x hx
  change max |chi n| (max (max |(p n).u x| |(p n).du x|)
    (max |(p n).v x| |(p n).dv x|)) ≤ max (max X U) (max V 0)
  apply max_le
  · exact (hchi n).trans ((le_max_left _ _).trans (le_max_left _ _))
  apply max_le
  · exact (max_le (huc x hx).1 (huc x hx).2).trans ((le_max_right _ _).trans (le_max_left _ _))
  apply max_le
  · have hh : |(p n).v x| ≤ V := by linarith [abs_nonneg ((p n).dv x)]
    exact hh.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hh : |(p n).dv x| ≤ V := by linarith [abs_nonneg ((p n).v x)]
    exact hh.trans ((le_max_left _ _).trans (le_max_right _ _))


theorem minimal_state_bound {L alpha m beta mu nu gamma X uStar : ℝ}
    (chi : ι → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L 0 0 alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (_halpha : 0 ≤ alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, (p n).u x = L*uStar) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n x, x ∈ Icc 0 L →
      ‖point (chi n) ((p n).u x) ((p n).du x) ((p n).v x) ((p n).dv x)‖ ≤ B := by
  let U := ClassicalMinimalEstimates.populationEnvelope L uStar gamma nu X m
  let D := X*U^m*(2*nu*L*uStar^gamma)
  let A := max U D
  let V := (1/mu+2*L^2+2*L)*(nu*U^gamma)
  refine ⟨max (max X A) (max V 0),le_trans (le_max_right _ _) (le_max_right _ _),?_⟩
  intro n x hx
  have huc := ClassicalMinimalEstimates.c1_gronwall_bound (p n) (s n) hL hgamma hgamma1
    hm hm1 hbeta hmu.le hnu (hchi n) (hpos n) (hmass n)
  have hU : 0 ≤ U := (abs_nonneg _).trans (huc 0 ⟨le_rfl,hL.le⟩).1
  let F := fun y => nu*(p n).u y^gamma
  have hFc : ContinuousOn F (Icc 0 L) :=
    continuousOn_const.mul ((p n).continuous_u.rpow_const (fun _ _ => Or.inr hgamma))
  let q : SignedEllipticEnergy.Profile L mu F := {
    V := (p n).v
    dV := (p n).dv
    continuous_V := (s n).continuous_v
    continuous_dV := (s n).continuous_dv
    derivative_V := (p n).derivative_v
    equation := by
      intro y hy
      convert (s n).derivative_dv y hy using 1
      dsimp [F]
      linarith [(s n).stationary y hy]
    neumann_left := (p n).neumann_v_left
    neumann_right := (p n).neumann_v_right }
  have hFb : ∀ y ∈ Icc 0 L, |F y| ≤ nu*U^gamma := by
    intro y hy
    have huly : (p n).u y ≤ U := (le_abs_self _).trans (huc y hy).1
    dsimp [F]
    rw [abs_mul,abs_of_nonneg hnu,abs_of_nonneg (Real.rpow_nonneg (hpos n y hy).le _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hpos n y hy).le huly hgamma) hnu
  have hvc : |(p n).v x|+|(p n).dv x| ≤ V :=
    q.c1_bound hL hmu hFc (by positivity) hFb x hx
  change max |chi n| (max (max |(p n).u x| |(p n).du x|)
    (max |(p n).v x| |(p n).dv x|)) ≤ max (max X A) (max V 0)
  apply max_le
  · exact (hchi n).trans ((le_max_left _ _).trans (le_max_left _ _))
  apply max_le
  · exact (max_le ((huc x hx).1.trans (le_max_left U D)) ((huc x hx).2.trans (le_max_right U D))).trans ((le_max_right _ _).trans (le_max_left _ _))
  apply max_le
  · have hh : |(p n).v x| ≤ V := by linarith [abs_nonneg ((p n).dv x)]
    exact hh.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hh : |(p n).dv x| ≤ V := by linarith [abs_nonneg ((p n).v x)]
    exact hh.trans ((le_max_left _ _).trans (le_max_right _ _))

/-- Explicit uniform C2-Hölder criterion on actual representatives:
all six derivatives through order two are bounded and both actual second
derivatives share a positive exponent strictly below one. -/
def C2HolderCriterion (L : ℝ) (u du ddu v dv ddv : ι → ℝ → ℝ) : Prop :=
  ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧ ∀ n,
    (∀ x ∈ Icc 0 L, |u n x| ≤ C ∧ |du n x| ≤ C ∧ |ddu n x| ≤ C ∧
      |v n x| ≤ C ∧ |dv n x| ≤ C ∧ |ddv n x| ≤ C) ∧
    (∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L,
      |ddu n y-ddu n x| ≤ C*|y-x|^theta ∧ |ddv n y-ddv n x| ≤ C*|y-x|^theta)

/-- From a genuine common state bound, the actual stationary equations
supply the common C2-Hölder criterion. No Hölder field or derivative bound
is assumed; real-power composition and the common ODE modulus are derived. -/
theorem actual_holder_of_state_bound {L B a b alpha m beta mu nu gamma : ℝ}
    (chi : ι → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (hB : 0 ≤ B) (halpha : 0 ≤ alpha) (hm : 1 ≤ m) (hgamma : 0 ≤ gamma)
    (hDDU : ∀ n, ContinuousOn (p n).ddu (Icc 0 L))
    (hDDV : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hu : ∀ n x, x ∈ Icc 0 L → 0 ≤ (p n).u x)
    (hb : ∀ n x, x ∈ Icc 0 L →
      ‖point (chi n) ((p n).u x) ((p n).du x) ((p n).v x) ((p n).dv x)‖ ≤ B) :
    C2HolderCriterion L (fun n => (p n).u) (fun n => (p n).du) (fun n => (p n).ddu)
      (fun n => (p n).v) (fun n => (p n).dv) (fun n => (s n).ddv) := by
  let f := fun n x => point (chi n) ((p n).u x) ((p n).du x) ((p n).v x) ((p n).dv x)
  have hc : ∀ n, ContinuousOn (f n) (Icc 0 L) := fun n =>
    continuousOn_const.prodMk (((p n).continuous_u.prodMk (p n).continuous_du).prodMk
      ((s n).continuous_v.prodMk (s n).continuous_dv))
  have hd : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (f n) (field a b alpha m beta mu nu gamma (f n x)) x :=
    fun n x hx => classical_derivative (p n) (s n) hm halpha (hu n) hx
  have hH := continuous_field a b alpha m beta mu nu gamma halpha hm hgamma
  obtain ⟨M,hM,hl⟩ := StationaryHolderField.trajectory_modulus _ hH hL.le f hc hd hb
  obtain ⟨⟨hP⟩,⟨hS⟩⟩ := StationaryHolderField.field_controls f hB hM hb hl hu
    (fun n => (s n).nonnegative_v) halpha hm hgamma
  have hfield := fun n x hx => ClassicalStationaryC2Limit.field_eq_actual_derivatives
    (p n) (s n) hL hm halpha hgamma (hu n) (hDDU n) (hDDV n) x hx
  let h2 := hP.congr (fun n x hx => congrArg (fun z : State => z.2.1.2) (hfield n x hx))
  let k2 := hS.congr (fun n x hx => congrArg (fun z : State => z.2.2.2) (hfield n x hx))
  let theta := min h2.exponent k2.exponent / 2
  have ht : 0 < theta := half_pos (lt_min h2.exponent_pos k2.exponent_pos)
  have htu : theta ≤ h2.exponent := by dsimp [theta]; linarith [min_le_left h2.exponent k2.exponent,lt_min h2.exponent_pos k2.exponent_pos]
  have htv : theta ≤ k2.exponent := by dsimp [theta]; linarith [min_le_right h2.exponent k2.exponent,lt_min h2.exponent_pos k2.exponent_pos]
  have ht1 : theta < 1 := by dsimp [theta]; linarith [min_le_left h2.exponent k2.exponent,h2.exponent_le_one]
  let h2' := h2.weaken theta ht htu
  let k2' := k2.weaken theta ht htv
  let C := B+h2.bound+k2.bound+h2'.constant+k2'.constant+1
  have hCB : B ≤ C := by dsimp [C]; linarith [h2.bound_nonneg,k2.bound_nonneg,h2'.constant_nonneg,k2'.constant_nonneg]
  have hCu : h2.bound ≤ C := by dsimp [C]; linarith [h2.bound_nonneg,k2.bound_nonneg,h2'.constant_nonneg,k2'.constant_nonneg]
  have hCv : k2.bound ≤ C := by dsimp [C]; linarith [h2.bound_nonneg,k2.bound_nonneg,h2'.constant_nonneg,k2'.constant_nonneg]
  have hDu : h2'.constant ≤ C := by dsimp [C]; linarith [h2.bound_nonneg,k2.bound_nonneg,h2'.constant_nonneg,k2'.constant_nonneg]
  have hDv : k2'.constant ≤ C := by dsimp [C]; linarith [h2.bound_nonneg,k2.bound_nonneg,h2'.constant_nonneg,k2'.constant_nonneg]
  refine ⟨theta,⟨ht,ht1⟩,C,by dsimp [C]; linarith [h2.bound_nonneg,k2.bound_nonneg,h2'.constant_nonneg,k2'.constant_nonneg],?_⟩
  intro n
  constructor
  · intro x hx
    have hstate := hb n x hx
    change max |chi n| (max (max |(p n).u x| |(p n).du x|)
      (max |(p n).v x| |(p n).dv x|)) ≤ B at hstate
    have hcc := (max_le_iff.mp (max_le_iff.mp hstate).2)
    exact ⟨((max_le_iff.mp hcc.1).1).trans hCB,((max_le_iff.mp hcc.1).2).trans hCB,
      (h2.bounded n x hx).trans hCu,((max_le_iff.mp hcc.2).1).trans hCB,
      ((max_le_iff.mp hcc.2).2).trans hCB,(k2.bounded n x hx).trans hCv⟩
  · intro x hx y hy
    exact ⟨(h2'.modulus n x hx y hy).trans (mul_le_mul_of_nonneg_right hDu (Real.rpow_nonneg (abs_nonneg _) _)),
      (k2'.modulus n x hx y hy).trans (mul_le_mul_of_nonneg_right hDv (Real.rpow_nonneg (abs_nonneg _) _))⟩

/-- Concrete C2-Hölder bound on the actual six representatives. -/
def C2HolderBound (L theta C : ℝ) (u du ddu v dv ddv : ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc 0 L, |u x| ≤ C ∧ |du x| ≤ C ∧ |ddu x| ≤ C ∧
    |v x| ≤ C ∧ |dv x| ≤ C ∧ |ddv x| ≤ C) ∧
  (∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L,
    |ddu y-ddu x| ≤ C*|y-x|^theta ∧ |ddv y-ddv x| ≤ C*|y-x|^theta)

/-- Universal indexing type, containing only ordinary actual solution data.
It contains no estimate, compactness or Hölder conclusion. -/
structure LogisticMember (L a b alpha m beta mu nu gamma X : ℝ) where
  chi : ℝ
  p : StationaryMassIdentity.ClassicalProfile L a b alpha chi m beta
  s : ClassicalLogisticEstimates.SignalData p mu nu gamma
  continuous_ddu : ContinuousOn p.ddu (Icc 0 L)
  continuous_ddv : ContinuousOn s.ddv (Icc 0 L)
  chi_bound : |chi| ≤ X
  positive_u : ∀ x ∈ Icc 0 L, 0 < p.u x
  nonconstant : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, p.u x ≠ p.u y

/-- Uniform C2-Hölder estimate with constants chosen before the actual
logistic stationary solution, throughout the full frozen mobility range. -/
theorem logistic_uniform_C2_holder {L a b alpha m beta mu nu gamma X : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha) :
    ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
      ∀ (chi : ℝ) (p : StationaryMassIdentity.ClassicalProfile L a b alpha chi m beta)
        (s : ClassicalLogisticEstimates.SignalData p mu nu gamma),
      ContinuousOn p.ddu (Icc 0 L) → ContinuousOn s.ddv (Icc 0 L) →
      |chi| ≤ X → (∀ x ∈ Icc 0 L, 0 < p.u x) →
      (∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, p.u x ≠ p.u y) →
      C2HolderBound L theta C p.u p.du p.ddu p.v p.dv s.ddv := by
  let D := LogisticMember L a b alpha m beta mu nu gamma X
  let chi := fun d : D => d.chi
  let p := fun d : D => d.p
  let s := fun d : D => d.s
  obtain ⟨B,hB,hstate⟩ := logistic_state_bound chi p s hL ha hb halpha hm hm1 hbeta
    hmu hnu hgamma hgamma1 (fun d => d.chi_bound) (fun d => d.positive_u) (fun d => d.nonconstant)
  obtain ⟨theta,ht,C,hC,hall⟩ := actual_holder_of_state_bound chi p s hL hB halpha.le hm hgamma.le
    (fun d => d.continuous_ddu) (fun d => d.continuous_ddv)
    (fun d x hx => (d.positive_u x hx).le) hstate
  refine ⟨theta,ht,C,hC,?_⟩
  intro chi' p' s' hddu hddv hchi hpos hnonconst
  exact hall (⟨chi',p',s',hddu,hddv,hchi,hpos,hnonconst⟩ : D)

/-- Universal fixed-mass minimal actual solution data. -/
structure MinimalMember (L m beta mu nu gamma X uStar : ℝ) where
  chi : ℝ
  p : StationaryMassIdentity.ClassicalProfile L 0 0 0 chi m beta
  s : ClassicalLogisticEstimates.SignalData p mu nu gamma
  continuous_ddu : ContinuousOn p.ddu (Icc 0 L)
  continuous_ddv : ContinuousOn s.ddv (Icc 0 L)
  chi_bound : |chi| ≤ X
  positive_u : ∀ x ∈ Icc 0 L, 0 < p.u x
  mass : ∫ x in (0 : ℝ)..L, p.u x = L*uStar

/-- Uniform C2-Hölder estimate for the actual prescribed-mass minimal
stationary system, including the mobility endpoint m=2 and constant families. -/
theorem minimal_uniform_C2_holder {L m beta mu nu gamma X uStar : ℝ}
    (hL : 0 < L) (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) :
    ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
      ∀ (chi : ℝ) (p : StationaryMassIdentity.ClassicalProfile L 0 0 0 chi m beta)
        (s : ClassicalLogisticEstimates.SignalData p mu nu gamma),
      ContinuousOn p.ddu (Icc 0 L) → ContinuousOn s.ddv (Icc 0 L) →
      |chi| ≤ X → (∀ x ∈ Icc 0 L, 0 < p.u x) →
      (∫ x in (0 : ℝ)..L, p.u x) = L*uStar →
      C2HolderBound L theta C p.u p.du p.ddu p.v p.dv s.ddv := by
  let D := MinimalMember L m beta mu nu gamma X uStar
  let chi := fun d : D => d.chi
  let p := fun d : D => d.p
  let s := fun d : D => d.s
  obtain ⟨B,hB,hstate⟩ := minimal_state_bound chi p s hL le_rfl hm hm1 hbeta
    hmu hnu hgamma hgamma1 (fun d => d.chi_bound) (fun d => d.positive_u) (fun d => d.mass)
  obtain ⟨theta,ht,C,hC,hall⟩ := actual_holder_of_state_bound chi p s hL hB le_rfl hm hgamma
    (fun d => d.continuous_ddu) (fun d => d.continuous_ddv)
    (fun d x hx => (d.positive_u x hx).le) hstate
  refine ⟨theta,ht,C,hC,?_⟩
  intro chi' p' s' hddu hddv hchi hpos hmass
  exact hall (⟨chi',p',s',hddu,hddv,hchi,hpos,hmass⟩ : D)

/-- The same parameter-only logistic C2-Hölder estimate stated directly for
literal physical classical solutions, with their built-in C2 representatives. -/
theorem logistic_uniform_physical_C2_holder {L a b alpha m beta mu nu gamma X : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha) :
    ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
      ∀ (chi : ℝ) (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta),
      (∀ x ∈ Icc 0 L, 0 ≤ q.v x) → q.dv 0 = 0 → q.dv L = 0 →
      (∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) →
      |chi| ≤ X → (∀ x ∈ Icc 0 L, 0 < q.u x) →
      (∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, q.u x ≠ q.u y) →
      C2HolderBound L theta C q.u q.du q.ddu q.v q.dv q.ddv := by
  obtain ⟨theta,ht,C,hC,hall⟩ := logistic_uniform_C2_holder hL ha hb halpha hm hm1 hbeta
    hmu hnu hgamma hgamma1 (X := X)
  refine ⟨theta,ht,C,hC,?_⟩
  intro chi q hv hN0 hNL heq hchi hpos hnonconst
  exact hall chi (PhysicalClassicalAdapter.toClassicalProfile q hm hv hN0 hNL)
    (PhysicalClassicalAdapter.toSignalData q hm hv hN0 hNL heq)
    q.continuous_ddu q.continuous_ddv hchi hpos hnonconst

/-- The prescribed-mass minimal C2-Hölder estimate for literal physical
classical solutions; constants are uniform before quantifying the solution. -/
theorem minimal_uniform_physical_C2_holder {L m beta mu nu gamma X uStar : ℝ}
    (hL : 0 < L) (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) :
    ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
      ∀ (chi : ℝ) (q : PhysicalStrongPositivity.StationaryProfile L 0 0 0 chi m beta),
      (∀ x ∈ Icc 0 L, 0 ≤ q.v x) → q.dv 0 = 0 → q.dv L = 0 →
      (∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) →
      |chi| ≤ X → (∀ x ∈ Icc 0 L, 0 < q.u x) →
      (∫ x in (0 : ℝ)..L, q.u x) = L*uStar →
      C2HolderBound L theta C q.u q.du q.ddu q.v q.dv q.ddv := by
  obtain ⟨theta,ht,C,hC,hall⟩ := minimal_uniform_C2_holder hL hm hm1 hbeta
    hmu hnu hgamma hgamma1 (X := X) (uStar := uStar)
  refine ⟨theta,ht,C,hC,?_⟩
  intro chi q hv hN0 hNL heq hchi hpos hmass
  exact hall chi (PhysicalClassicalAdapter.toClassicalProfile q hm hv hN0 hNL)
    (PhysicalClassicalAdapter.toSignalData q hm hv hN0 hNL heq)
    q.continuous_ddu q.continuous_ddv hchi hpos hmass

end
end ChemotaxisBifurcation.ClassicalStationaryHolder
