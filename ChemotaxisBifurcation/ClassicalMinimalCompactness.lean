module
public import ChemotaxisBifurcation.UniformComponentH2
public import ChemotaxisBifurcation.ClassicalMinimalEstimates

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalMinimalCompactness
open Real Set MeasureTheory Filter Topology StationaryODEState
noncomputable section

theorem uniform_state_bound {L alpha m beta mu nu gamma X uStar : ℝ}
    (chi : ℕ → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L 0 0 alpha (chi n) m beta)
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


theorem exists_augmented_limit {L alpha m beta mu nu gamma X uStar : ℝ}
    (chi : ℕ → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L 0 0 alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (halpha : 0 ≤ alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, (p n).u x = L*uStar) :
    ∃ g : ℝ → State, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ContinuousOn g (Icc 0 L) ∧
      TendstoUniformlyOn (fun n x => point (chi (phi n)) ((p (phi n)).u x)
        ((p (phi n)).du x) ((p (phi n)).v x) ((p (phi n)).dv x)) g atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n x => field 0 0 alpha m beta mu nu gamma
        (point (chi (phi n)) ((p (phi n)).u x) ((p (phi n)).du x)
          ((p (phi n)).v x) ((p (phi n)).dv x)))
        (fun x => field 0 0 alpha m beta mu nu gamma (g x)) atTop (Icc 0 L) ∧
      (∀ x ∈ Icc 0 L, HasDerivWithinAt g (field 0 0 alpha m beta mu nu gamma (g x)) (Icc 0 L) x) ∧
      (∀ x ∈ Icc 0 L, (g x).1 = (g 0).1) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ (g x).2.1.1 ∧ 0 ≤ (g x).2.2.1) ∧
      (g 0).2.1.2 = 0 ∧ (g L).2.1.2 = 0 ∧ (g 0).2.2.2 = 0 ∧ (g L).2.2.2 = 0 := by
  let f := fun n x => point (chi n) ((p n).u x) ((p n).du x) ((p n).v x) ((p n).dv x)
  have hfc : ∀ n, ContinuousOn (f n) (Icc 0 L) := fun n =>
    continuousOn_const.prodMk ((((p n).continuous_u.prodMk (p n).continuous_du).prodMk
      ((s n).continuous_v.prodMk (s n).continuous_dv)))
  have hfd : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (f n) (field 0 0 alpha m beta mu nu gamma (f n x)) x :=
    fun n x hx => classical_derivative (p n) (s n) hm halpha (fun y hy => (hpos n y hy).le) hx
  obtain ⟨B,hB,hbound⟩ := uniform_state_bound chi p s hL halpha hm hm1 hbeta
    hmu hnu hgamma hgamma1 hchi hpos hmass
  have hH := continuous_field 0 0 alpha m beta mu nu gamma halpha hm hgamma
  obtain ⟨g,phi,hphi,hgc,huni,hsrc,_,hderiv⟩ :=
    ClassicalODECompactness.exists_stationary_subsequence (field 0 0 alpha m beta mu nu gamma)
      hH hL.le f hfc hfd hbound
  have hwhole := ClassicalODECompactness.derivativeWithin_closed_interval hgc
    (hH.comp_continuousOn hgc) hderiv
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl,hL.le⟩
  have h1 : L ∈ Icc 0 L := ⟨hL.le,le_rfl⟩
  have hchic : Continuous (fun z : State => z.1) := by fun_prop
  have huc : Continuous (fun z : State => z.2.1.1) := by fun_prop
  have hvc : Continuous (fun z : State => z.2.2.1) := by fun_prop
  have hchilim : ∀ x ∈ Icc 0 L, Tendsto (fun n => chi (phi n)) atTop (nhds (g x).1) := by
    intro x hx
    exact (hchic.tendsto (g x)).comp (huni.tendsto_at hx)
  have hconst : ∀ x ∈ Icc 0 L, (g x).1 = (g 0).1 := fun x hx =>
    tendsto_nhds_unique (hchilim x hx) (hchilim 0 h0)
  have hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ (g x).2.1.1 ∧ 0 ≤ (g x).2.2.1 := by
    intro x hx
    constructor
    · exact isClosed_Ici.mem_of_tendsto ((huc.tendsto (g x)).comp (huni.tendsto_at hx))
        (Eventually.of_forall (fun n => (hpos (phi n) x hx).le))
    · exact isClosed_Ici.mem_of_tendsto ((hvc.tendsto (g x)).comp (huni.tendsto_at hx))
        (Eventually.of_forall (fun n => (s (phi n)).nonnegative_v x hx))
  have htrace (q : State → ℝ) (hq : Continuous q) (x : ℝ) (hx : x ∈ Icc 0 L)
      (hz : ∀ n, q (f n x) = 0) : q (g x) = 0 := by
    have h := (hq.tendsto (g x)).comp (huni.tendsto_at hx)
    change Tendsto (fun n => q (f (phi n) x)) atTop (nhds (q (g x))) at h
    simp only [hz] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine ⟨g,phi,hphi,hgc,huni,hsrc,hwhole,hconst,hnonneg,?_,?_,?_,?_⟩
  · exact htrace (fun z => z.2.1.2) (by fun_prop) 0 h0 (fun n => (p n).neumann_u_left)
  · exact htrace (fun z => z.2.1.2) (by fun_prop) L h1 (fun n => (p n).neumann_u_right)
  · exact htrace (fun z => z.2.2.2) (by fun_prop) 0 h0 (fun n => (p n).neumann_v_left)
  · exact htrace (fun z => z.2.2.2) (by fun_prop) L h1 (fun n => (p n).neumann_v_right)


theorem exists_classical_C2_stationary_limit {L alpha m beta mu nu gamma X uStar : ℝ}
    (chi : ℕ → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L 0 0 alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (halpha : 0 ≤ alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hDDU : ∀ n, ContinuousOn (p n).ddu (Icc 0 L))
    (hDDV : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, (p n).u x = L*uStar) :
    ∃ chiBar : ℝ,
    ∃ q : PhysicalStrongPositivity.StationaryProfile L 0 0 alpha chiBar m beta,
    ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (fun n => chi (phi n)) atTop (nhds chiBar) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).u) q.u atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).du) q.du atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).v) q.v atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).dv) q.dv atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).ddu) q.ddu atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (s (phi n)).ddv) q.ddv atTop (Icc 0 L) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0 := by
  obtain ⟨g,phi,hphi,hgc,huni,hsrc,hderiv,hconst,hnn,hU0,hUL,hV0,hVL⟩ :=
    exists_augmented_limit chi p s hL halpha hm hm1 hbeta
      hmu hnu hgamma hgamma1 hchi hpos hmass
  let q := StationaryLimitProfile.toPopulationProfile g hgc hderiv hconst hnn hm halpha hgamma hU0 hUL
  have hPair := uniformContinuous_snd.comp_tendstoUniformlyOn huni
  have hU := uniformContinuous_fst.comp_tendstoUniformlyOn hPair
  have hV := uniformContinuous_snd.comp_tendstoUniformlyOn hPair
  have hUc := uniformContinuous_fst.comp_tendstoUniformlyOn hU
  have hDUc := uniformContinuous_snd.comp_tendstoUniformlyOn hU
  have hVc := uniformContinuous_fst.comp_tendstoUniformlyOn hV
  have hDVc := uniformContinuous_snd.comp_tendstoUniformlyOn hV
  have hchic : Continuous (fun z : State => z.1) := by fun_prop
  have hchil := (hchic.tendsto (g 0)).comp (huni.tendsto_at ⟨le_rfl,hL.le⟩)
  have hfield := fun n x hx => ClassicalStationaryC2Limit.field_eq_actual_derivatives (p n) (s n) hL hm halpha hgamma
    (fun y hy => (hpos n y hy).le) (hDDU n) (hDDV n) x hx
  have hsrcPair := uniformContinuous_snd.comp_tendstoUniformlyOn hsrc
  have hDDUc := uniformContinuous_snd.comp_tendstoUniformlyOn
    (uniformContinuous_fst.comp_tendstoUniformlyOn hsrcPair)
  have hDDVc := uniformContinuous_snd.comp_tendstoUniformlyOn
    (uniformContinuous_snd.comp_tendstoUniformlyOn hsrcPair)
  have hDU : TendstoUniformlyOn (fun n => (p (phi n)).ddu) q.ddu atTop (Icc 0 L) := by
    apply hDDUc.congr
    · exact Eventually.of_forall (fun n x hx => (congrArg (fun z : State => z.2.1.2) (hfield (phi n) x hx)))
  have hDV : TendstoUniformlyOn (fun n => (s (phi n)).ddv) q.ddv atTop (Icc 0 L) := by
    apply hDDVc.congr
    · exact Eventually.of_forall (fun n x hx => (congrArg (fun z : State => z.2.2.2) (hfield (phi n) x hx)))
  refine ⟨(g 0).1,q,phi,hphi,hchil,hUc,hDUc,hVc,hDVc,hDU,hDV,hnn,hV0,hVL,?_⟩
  intro x hx
  exact StationaryLimitProfile.signal_identity mu nu gamma g x


/-- Actual minimal-family C2 and component H2 compactness, including preservation
of the prescribed mass by actual uniform integral convergence. -/
theorem exists_classical_componentH2_stationary_limit {L alpha m beta mu nu gamma X uStar : ℝ}
    (chi : ℕ → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L 0 0 alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (halpha : 0 ≤ alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hDDU : ∀ n, ContinuousOn (p n).ddu (Icc 0 L))
    (hDDV : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, (p n).u x = L*uStar) :
    ∃ chiBar : ℝ,
    ∃ q : PhysicalStrongPositivity.StationaryProfile L 0 0 alpha chiBar m beta,
    ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (fun n => chi (phi n)) atTop (nhds chiBar) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).u) q.u atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).du) q.du atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).v) q.v atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).dv) q.dv atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).ddu) q.ddu atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (s (phi n)).ddv) q.ddv atTop (Icc 0 L) ∧
      Tendsto (fun n => UniformComponentH2.componentH2Distance L (p (phi n)).u (p (phi n)).du (p (phi n)).ddu
        q.u q.du q.ddu) atTop (nhds 0) ∧
      Tendsto (fun n => UniformComponentH2.componentH2Distance L (p (phi n)).v (p (phi n)).dv (s (phi n)).ddv
        q.v q.dv q.ddv) atTop (nhds 0) ∧
      (∀ x ∈ Icc 0 L, 0 ≤ q.u x ∧ 0 ≤ q.v x) ∧
      q.dv 0 = 0 ∧ q.dv L = 0 ∧
      (∫ x in (0 : ℝ)..L, q.u x) = L*uStar ∧
      ∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0 := by
  obtain ⟨chiBar,q,phi,hphi,hchiLim,hU,hDU,hV,hDV,hDDUlim,hDDVlim,hnn,hV0,hVL,hsig⟩ :=
    exists_classical_C2_stationary_limit chi p s hL halpha
      hm hm1 hbeta hmu hnu hgamma hgamma1 hDDU hDDV hchi hpos hmass
  have hqu : ContinuousOn q.u (Icc 0 L) := fun x hx => (q.derivative_u x hx).continuousWithinAt
  have hqdu : ContinuousOn q.du (Icc 0 L) := fun x hx => (q.derivative_du x hx).continuousWithinAt
  have hqv : ContinuousOn q.v (Icc 0 L) := fun x hx => (q.derivative_v x hx).continuousWithinAt
  have hqdv : ContinuousOn q.dv (Icc 0 L) := fun x hx => (q.derivative_dv x hx).continuousWithinAt
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (p (phi n)).u
      (volume.restrict (Icc 0 L)) := Eventually.of_forall fun n =>
    (p (phi n)).continuous_u.aestronglyMeasurable measurableSet_Icc
  have hbound : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ᵐ x ∂volume.restrict (Icc 0 L),
      ‖(p (phi n)).u x‖ ≤ C := by
    refine ⟨ClassicalMinimalEstimates.populationEnvelope L uStar gamma nu X m,
      Eventually.of_forall ?_⟩
    intro n
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    simpa only [Real.norm_eq_abs] using
      (ClassicalMinimalEstimates.c1_gronwall_bound (p (phi n)) (s (phi n)) hL hgamma hgamma1
        hm hm1 hbeta hmu.le hnu (hchi (phi n)) (hpos (phi n)) (hmass (phi n)) x hx).1
  have hpoint : ∀ᵐ x ∂volume.restrict (Icc 0 L),
      Tendsto (fun n => (p (phi n)).u x) atTop (nhds (q.u x)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    exact hU.tendsto_at hx
  have hi := tendsto_integral_filter_of_norm_le_const hmeas hbound hpoint
  have hmassSet : ∀ n, (∫ x in Icc 0 L, (p (phi n)).u x) = L*uStar := by
    intro n
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL.le]
    exact hmass (phi n)
  have hmLim : (∫ x in (0 : ℝ)..L, q.u x) = L*uStar := by
    rw [intervalIntegral.integral_of_le hL.le, ← integral_Icc_eq_integral_Ioc]
    exact tendsto_nhds_unique hi (by simpa only [hmassSet] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => L*uStar) atTop (nhds (L*uStar))))
  refine ⟨chiBar,q,phi,hphi,hchiLim,hU,hDU,hV,hDV,hDDUlim,hDDVlim,?_,?_,hnn,hV0,hVL,hmLim,hsig⟩
  · exact UniformComponentH2.componentH2Distance_tendsto (fun n => (p (phi n)).continuous_u)
      (fun n => (p (phi n)).continuous_du) (fun n => hDDU (phi n))
      hqu hqdu q.continuous_ddu hU hDU hDDUlim
  · exact UniformComponentH2.componentH2Distance_tendsto (fun n => (s (phi n)).continuous_v)
      (fun n => (s (phi n)).continuous_dv) (fun n => hDDV (phi n))
      hqv hqdv q.continuous_ddv hV hDV hDDVlim

end
end ChemotaxisBifurcation.ClassicalMinimalCompactness
