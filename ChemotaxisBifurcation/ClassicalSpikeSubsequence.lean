module
public import ChemotaxisBifurcation.ClassicalLogisticEstimates
public import ChemotaxisBifurcation.SignalWeakSubsequence

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalSpikeSubsequence
open Real Set MeasureTheory Filter Topology StationaryMassIdentity
noncomputable section

/-- An arbitrary population Lr moment bounds all smaller positive moments.
The scalar normalization is derived, not a physical equilibrium assumption. -/
theorem lower_moment {L R r t : ℝ} {u : ℝ → ℝ}
    (hL : 0 < L) (hR : 0 ≤ R) (hr : 1 < r) (ht : 0 < t) (htr : t ≤ r)
    (hu : ContinuousOn u (Icc 0 L)) (hu0 : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hbound : ∫ x in (0 : ℝ)..L, u x^r ≤ R) :
    ∫ x in (0 : ℝ)..L, u x^t ≤ L*(SignalPowerMoment.momentScale L R r)^t := by
  have hs : (SignalPowerMoment.momentScale L R r)^r = R/L := by
    dsimp [SignalPowerMoment.momentScale]
    rw [one_div, Real.rpow_inv_rpow (div_nonneg hR hL.le) (by linarith : r ≠ 0)]
  have hb : ∫ x in (0 : ℝ)..L, u x^(1+(r-1)) ≤
      L*(SignalPowerMoment.momentScale L R r)^(1+(r-1)) := by
    rw [show 1+(r-1)=r by ring,hs]
    have hh : L*(R/L)=R := by field_simp
    rwa [hh]
  exact IntervalMoments.logistic_power_integral_le L (SignalPowerMoment.momentScale L R r)
    (r-1) t u hL (by linarith) (Real.rpow_nonneg (div_nonneg hR hL.le) _) ht
    (by linarith) hu hu0 hb

/-- Actual classical stationary systems with a bounded population Lr moment
have a constant C1 signal subsequence and the corresponding interval source
limits. First integrals, flux bounds, mass bounds, positive mobility lower
bound, signal estimates and subsequence extraction are all derived. This
covers both nonnegative logistic coefficients and the fixed-mass minimal
case. Full conjugate-Lp tests are a separate stronger conclusion. -/
theorem exists_constant_signal_subsequence
    {L a b alpha gamma mu nu m beta r R : ℝ} {chi : ℕ → ℝ}
    (p : ∀ n, ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) (halpha : 0 < alpha)
    (hgamma : 0 < gamma) (hmu : 0 < mu) (hnu : 0 < nu)
    (hm : 0 < m) (hbeta : 0 ≤ beta) (hr : 1 < r) (hgr : gamma < r) (hR : 0 ≤ R)
    (hchi : Tendsto chi atTop atTop)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hvpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).v x)
    (hddv : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hbound : ∀ n, ∫ x in (0 : ℝ)..L, (p n).u x^r ≤ R) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ c : ℝ, 0 ≤ c ∧
      TendstoUniformlyOn (fun n => (p (phi n)).v) (fun _ => nu/mu*c) atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).dv) (fun _ => 0) atTop (Icc 0 L) ∧
      ∀ x y, 0 ≤ x → x ≤ y → y ≤ L →
        Tendsto (fun n => ∫ z in x..y, (p (phi n)).u z^gamma) atTop (𝓝 (c*(y-x))) := by
  let A := SignalPowerMoment.momentScale L R r
  let S := L*A^gamma
  let B := nu*S/(mu*L)+2*nu*S*L
  let kappa := 1/(1+B)^beta
  let F := fun n x => ∫ y in (0 : ℝ)..x, a*(p n).u y-b*(p n).u y^(1+alpha)
  have hA : 0 ≤ A := Real.rpow_nonneg (div_nonneg hR hL.le) _
  have hS : 0 ≤ S := mul_nonneg hL.le (Real.rpow_nonneg hA _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hk : 0 < kappa := one_div_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
  have hu0 : ∀ n x, x ∈ Icc 0 L → 0 ≤ (p n).u x := fun n x hx => (hpos n x hx).le
  have hmean : ∀ n, ∫ x in (0 : ℝ)..L, (p n).u x ≤ L*A := by
    intro n
    simpa only [Real.rpow_one] using lower_moment hL hR hr (by norm_num : (0 : ℝ)<1)
      hr.le (p n).continuous_u (hu0 n) (hbound n)
  have hsource : ∀ n, ∫ x in (0 : ℝ)..L, (p n).u x^gamma ≤ S :=
    fun n => lower_moment hL hR hr hgamma hgr.le (p n).continuous_u (hu0 n) (hbound n)
  have hvbound : ∀ n x, x ∈ Icc 0 L → (p n).v x ≤ B := by
    intro n x hx
    have hh := (SpikeEstimates.signal_sup_le L mu nu gamma (p n).u (p n).v (p n).dv (s n).ddv
      hL hmu hnu.le hgamma.le (p n).continuous_u (hu0 n) (s n).continuous_v
      (s n).nonnegative_v (p n).derivative_v (s n).continuous_dv (s n).derivative_dv
      (s n).stationary (p n).neumann_v_left (p n).neumann_v_right x hx).2
    have hnum := mul_le_mul_of_nonneg_left (hsource n) hnu.le
    have hd := div_le_div_of_nonneg_right hnum (mul_nonneg hmu.le hL.le)
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsource n)
      (by positivity : 0 ≤ 2*nu)) hL.le
    exact hh.trans (by dsimp [B]; linarith)
  apply SignalSpikeSubsequence.exists_constant_C1_and_interval_source_subsequence
    (beta := beta) (kappa := kappa) (M := L*A) (Fb := 2*a*L*A) (F := F)
    hL hgamma hr hgr hm hk hmu hnu hR hchi
    (fun n => (p n).continuous_u) hu0 (fun n => (p n).derivative_u)
    (fun n => (p n).continuous_du) (fun n => (s n).continuous_v) hvpos
    (fun n => (s n).continuous_dv) hddv (fun n => (p n).derivative_v)
    (fun n => (s n).derivative_dv) (fun n => (s n).stationary)
    (fun n => (p n).neumann_v_left) (fun n => (p n).neumann_v_right)
  · intro n
    apply SpikeEstimates.continuousOn_primitive hL.le
    exact (continuousOn_const.mul (p n).continuous_u).sub
      (continuousOn_const.mul ((p n).continuous_u.rpow_const fun _ _ => Or.inr (by linarith)))
  · intro n
    simpa only [F, mul_assoc] using SpikeEstimates.logistic_first_integral L a b alpha (chi n) m beta
      (p n).u (p n).v (p n).du (p n).ddu (p n).dv (p n).dJ
      hL.le halpha (p n).continuous_u (p n).continuous_du (p n).derivative_du
      (p n).continuous_flux (p n).derivative_flux (p n).stationary
      (p n).neumann_u_left (p n).neumann_v_left
  · intro n x hx
    exact (SpikeEstimates.logistic_F_bound L a b alpha A (p n).u ha hb halpha
      (p n).continuous_u (hu0 n) ((p n).mass_balance hL.le halpha.le) (hmean n) x hx).2
  · intro n x hx
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith [hvpos n x hx]) _)
      (Real.rpow_le_rpow (by linarith [hvpos n x hx]) (by linarith [hvbound n x hx]) hbeta)
  · exact hmean
  · exact hbound

/-- Full actual classical-system subsequence with every conjugate-Lp test
for the source and all three signal Sobolev components. No weak or extraction
conclusion is a premise. The componentwise weak criterion is explicit. -/
theorem exists_constant_signal_and_weak_tests
    {L a b alpha gamma mu nu m beta r R : ℝ} {chi : ℕ → ℝ}
    (p : ∀ n, ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) (halpha : 0 < alpha)
    (hgamma : 0 < gamma) (hmu : 0 < mu) (hnu : 0 < nu)
    (hm : 0 < m) (hbeta : 0 ≤ beta) (hr : 1 < r) (hgr : gamma < r) (hR : 0 ≤ R)
    (hchi : Tendsto chi atTop atTop)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hvpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).v x)
    (hddv : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hbound : ∀ n, ∫ x in (0 : ℝ)..L, (p n).u x^r ≤ R) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ c : ℝ, 0 ≤ c ∧
      TendstoUniformlyOn (fun n => (p (phi n)).v) (fun _ => nu/mu*c) atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).dv) (fun _ => 0) atTop (Icc 0 L) ∧
      (∀ x y, 0 ≤ x → x ≤ y → y ≤ L →
        Tendsto (fun n => ∫ z in x..y, (p (phi n)).u z^gamma) atTop (𝓝 (c*(y-x)))) ∧
      ∀ g : Lp ℝ (ENNReal.ofReal ((r/gamma)/(r/gamma-1))) (SignalWeakSource.intervalVolume L),
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, (p (phi n)).u x^gamma*g x
          ∂SignalWeakSource.intervalVolume L) atTop
          (𝓝 (∫ x : Icc (0 : ℝ) L, c*g x ∂SignalWeakSource.intervalVolume L)) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, (p (phi n)).v x*g x
          ∂SignalWeakSource.intervalVolume L) atTop
          (𝓝 (∫ x : Icc (0 : ℝ) L, (nu/mu*c)*g x ∂SignalWeakSource.intervalVolume L)) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, (p (phi n)).dv x*g x
          ∂SignalWeakSource.intervalVolume L) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, (s (phi n)).ddv x*g x
          ∂SignalWeakSource.intervalVolume L) atTop (𝓝 0) := by
  obtain ⟨phi,hphi,c,hc,hvlim,hdvlim,hinterval⟩ := exists_constant_signal_subsequence p s
    hL ha hb halpha hgamma hmu hnu hm hbeta hr hgr hR hchi hpos hvpos hddv hbound
  refine ⟨phi,hphi,c,hc,hvlim,hdvlim,hinterval,?_⟩
  exact SignalWeakSobolev.all_components_test_tendsto L mu nu gamma r R c
    (fun n => (p (phi n)).u) (fun n => (p (phi n)).v)
    (fun n => (p (phi n)).dv) (fun n => (s (phi n)).ddv)
    hL hmu hnu hgamma hr hgr hR (fun n => (p (phi n)).continuous_u)
    (fun n x hx => (hpos (phi n) x hx).le) (fun n => (s (phi n)).continuous_v)
    (fun n => hvpos (phi n)) (fun n => (s (phi n)).continuous_dv) (fun n => hddv (phi n))
    (fun n => (p (phi n)).derivative_v) (fun n => (s (phi n)).derivative_dv)
    (fun n => (s (phi n)).stationary) (fun n => (p (phi n)).neumann_v_left)
    (fun n => (p (phi n)).neumann_v_right) (fun n => hbound (phi n)) hvlim hdvlim


end
end ChemotaxisBifurcation.ClassicalSpikeSubsequence
