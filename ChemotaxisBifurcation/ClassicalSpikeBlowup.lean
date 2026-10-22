module
public import ChemotaxisBifurcation.ClassicalSpikeSubsequence
public import ChemotaxisBifurcation.SpikeLimitBlowup
public import ChemotaxisBifurcation.SignalWeakSobolev

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalSpikeBlowup
open Real Set MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
noncomputable section

/-- A local derivative bound gives an actual uniformly convergent subsequence. -/
theorem local_uniform_subsequence {a b K B : ℝ} (hab : a < b)
    (u du : ℕ → ℝ → ℝ)
    (hc : ∀ n, ContinuousOn (u n) (Icc a b))
    (hd : ∀ n x, x ∈ Ioo a b → HasDerivAt (u n) (du n x) x)
    (hk : ∀ n x, x ∈ Ioo a b → |du n x| ≤ K)
    (hb : ∀ n x, x ∈ Icc a b → |u n x| ≤ B) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ U : ℝ → ℝ,
      ContinuousOn U (Icc a b) ∧ TendstoUniformlyOn (fun n => u (phi n)) U atTop (Icc a b) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hk 0 ((a+b)/2) ⟨by linarith,by linarith⟩)
  have hmod : ∀ n x, x ∈ Icc a b → ∀ y, y ∈ Icc a b → |u n x-u n y| ≤ K*|x-y| := by
    have ordered : ∀ n x, x ∈ Icc a b → ∀ y, y ∈ Icc a b → y < x →
        |u n x-u n y| ≤ K*(x-y) := by
      intro n x hx y hy hyx
      obtain ⟨c,hc',hs⟩ := exists_hasDerivAt_eq_slope (u n) (du n) hyx
        ((hc n).mono (Icc_subset_Icc hy.1 hx.2))
        (fun z hz => hd n z ⟨hy.1.trans_lt hz.1,hz.2.trans_le hx.2⟩)
      have he : u n x-u n y = du n c*(x-y) := by rw [hs]; field_simp
      rw [he,abs_mul,abs_of_pos (sub_pos.mpr hyx)]
      exact mul_le_mul_of_nonneg_right (hk n c ⟨hy.1.trans_lt hc'.1,hc'.2.trans_le hx.2⟩) (by linarith)
    intro n x hx y hy
    rcases lt_trichotomy y x with hh|hh|hh
    · simpa only [abs_of_pos (sub_pos.mpr hh)] using ordered n x hx y hy hh
    · simp [hh]
    · rw [abs_sub_comm x y,abs_of_pos (sub_pos.mpr hh)]
      simpa only [abs_sub_comm] using ordered n y hy x hx hh
  let F : ℕ → Icc a b →ᵇ ℝ := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => u n x,continuousOn_iff_continuous_domRestrict.mp (hc n)⟩
  have hcomp : IsCompact (closure (range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) B)
      (isCompact_closedBall _ _) (range F)
    · intro f x hf
      obtain ⟨n,rfl⟩ := hf
      rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs]
      change |u n x| ≤ B
      exact hb n x x.property
    · apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => K*t)
        (by simpa using (show Continuous (fun t : ℝ => K*t) by fun_prop).tendsto 0)
      intro x y i
      rcases i with ⟨f,hf⟩
      obtain ⟨n,rfl⟩ := hf
      change dist (u n x) (u n y) ≤ K*dist x y
      simpa only [Real.dist_eq,Subtype.dist_eq] using hmod n x x.property y y.property
  obtain ⟨G,_,phi,hphi,ht⟩ := hcomp.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  let U := IccExtend hab.le G
  refine ⟨phi,hphi,U,(continuous_IccExtend_iff.mpr G.continuous).continuousOn,?_⟩
  rw [tendstoUniformlyOn_iff_restrict]
  have he : (Icc a b).domRestrict U = (G : Icc a b → ℝ) := by
    funext x; exact IccExtend_of_mem hab.le G x.property
  rw [he]
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ht

/-- Both local population compactness and constant interval source convergence
are derived from actual classical stationary equations and ordinary bounds. -/
theorem bounded_local_extraction
    {L a b alpha gamma mu nu m beta A D K B : ℝ} {chi : ℕ → ℝ}
    (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hmu : 0 < mu) (hnu : 0 < nu) (hm : 0 < m) (hbeta : 0 ≤ beta)
    (hchi : Tendsto chi atTop atTop)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hvpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).v x)
    (hddv : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hAD : A < D) (hsub : Icc A D ⊆ Icc 0 L)
    (hk : ∀ n x, x ∈ Ioo A D → |(p n).du x| ≤ K)
    (hbound : ∀ n x, x ∈ Icc 0 L → (p n).u x ≤ B) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ (U : ℝ → ℝ) (c : ℝ),
      ContinuousOn U (Icc A D) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).u) U atTop (Icc A D) ∧
      ∀ x y, 0 ≤ x → x ≤ y → y ≤ L →
        Tendsto (fun n => ∫ z in x..y, (p (phi n)).u z^gamma) atTop (𝓝 (c*(y-x))) := by
  let r := max 1 gamma+1
  have hr : 1 < r := by dsimp [r]; linarith [le_max_left (1 : ℝ) gamma]
  have hgr : gamma < r := by dsimp [r]; linarith [le_max_right (1 : ℝ) gamma]
  have hB : 0 ≤ B := (hpos 0 0 ⟨le_rfl,hL.le⟩).le.trans (hbound 0 0 ⟨le_rfl,hL.le⟩)
  have hmom : ∀ n, ∫ x in (0 : ℝ)..L, (p n).u x^r ≤ L*B^r := by
    intro n
    have hh := intervalIntegral.integral_mono_on hL.le
      (((p n).continuous_u.rpow_const (fun _ _ => Or.inr (by linarith : 0 ≤ r))).intervalIntegrable_of_Icc hL.le)
      (intervalIntegrable_const (μ := volume) (c := B^r))
      (fun x hx => Real.rpow_le_rpow (hpos n x hx).le (hbound n x hx) (by linarith))
    simpa only [intervalIntegral.integral_const,smul_eq_mul,sub_zero] using hh
  obtain ⟨phi,hphi,c,_,_,_,hc⟩ := ClassicalSpikeSubsequence.exists_constant_signal_subsequence
    p s hL ha hb halpha hg hmu hnu hm hbeta hr hgr (by positivity) hchi hpos hvpos hddv hmom
  obtain ⟨psi,hpsi,U,hU,hconv⟩ := local_uniform_subsequence hAD
    (fun n => (p (phi n)).u) (fun n => (p (phi n)).du)
    (fun n => (p (phi n)).continuous_u.mono hsub)
    (fun n x hx => (p (phi n)).derivative_u x ⟨(hsub (left_mem_Icc.mpr hAD.le)).1.trans_lt hx.1,
      hx.2.trans_le (hsub (right_mem_Icc.mpr hAD.le)).2⟩)
    (fun n => hk (phi n))
    (fun n x hx => by rw [abs_of_pos (hpos (phi n) x (hsub hx))]; exact hbound (phi n) x (hsub hx))
  exact ⟨fun n => phi (psi n),hphi.comp hpsi,U,c,hU,hconv,
    fun x y hx hxy hy => (hc x y hx hxy hy).comp hpsi.tendsto_atTop⟩

/-- Theorem 1.4 gradient blowup for actual positive classical stationary
families. The ordinary population mass bound is visible; no compactness,
weak convergence or limiting equation is supplied as a hypothesis. -/
theorem gradient_blowup
    {L a b alpha gamma mu nu m beta uStar : ℝ} {chi : ℕ → ℝ} {x : ℕ → ℝ}
    (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hmu : 0 < mu) (hnu : 0 < nu) (hm : 0 < m) (hbeta : 0 ≤ beta)
    (hchi : Tendsto chi atTop atTop) (huStar : 0 < uStar)
    (hpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).u z)
    (hvpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).v z)
    (hddv : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hmass : ∀ n, ∫ z in (0 : ℝ)..L, (p n).u z ≤ L*uStar)
    (hx : ∀ n, x n ∈ Icc 0 L)
    (hmax : ∀ n, IsMaxOn (p n).u (Icc 0 L) (x n))
    (hliminf : ∃ l₀, uStar < l₀ ∧ ∀ᶠ n in atTop, l₀ ≤ (p n).u (x n)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ xstar ∈ Icc 0 L,
      Tendsto (fun k => x (phi k)) atTop (𝓝 xstar) ∧
      ∀ delta > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
        ∃ y ∈ Ioo (max 0 (xstar-delta)) (min L (xstar+delta)), K < |(p (phi k)).du y| := by
  apply SpikeLimit.spike_gradient_blowup hL huStar hg
    (fun n => (p n).continuous_u) (fun n z hz => (hpos n z hz).le)
    (fun n => (p n).derivative_u) hmass hx hmax hliminf
  intro phi hphi A D K B hAD hsub hk hbnd
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hk.and hbnd)
  let tau := fun n : ℕ => n+N
  have htau : StrictMono tau := by intro i j hij; dsimp [tau]; omega
  have hphit : StrictMono (fun n => phi (tau n)) := hphi.comp htau
  obtain ⟨psi,hpsi,U,c,hU,hconv,hweak⟩ := bounded_local_extraction
    (fun n => p (phi (tau n))) (fun n => s (phi (tau n))) hL ha hb halpha hg hmu hnu hm hbeta
    (hchi.comp hphit.tendsto_atTop) (fun n => hpos (phi (tau n)))
    (fun n => hvpos (phi (tau n))) (fun n => hddv (phi (tau n))) hAD hsub
    (fun n => (hN (tau n) (by dsimp [tau]; omega)).1)
    (fun n => (hN (tau n) (by dsimp [tau]; omega)).2)
  exact ⟨fun n => tau (psi n),htau.comp hpsi,U,c,hU,hconv,hweak⟩

/-- Logistic Theorem 1.4 on one subsequence: actual gradient blowup,
constant C1 signal limit and source interval convergence. Both the mass and
moment bounds are derived from the literal population PDE. -/
theorem logistic_spike_subsequence
    {L a b alpha gamma mu nu m beta : ℝ} {chi : ℕ → ℝ} {x : ℕ → ℝ}
    (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hga : gamma < 1+alpha)
    (hmu : 0 < mu) (hnu : 0 < nu) (hm : 0 < m) (hbeta : 0 ≤ beta)
    (hchi : Tendsto chi atTop atTop)
    (hpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).u z)
    (hvpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).v z)
    (hddv : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hnonconst : ∀ n, ∃ z ∈ Icc 0 L, ∃ w ∈ Icc 0 L, (p n).u z ≠ (p n).u w)
    (hx : ∀ n, x n ∈ Icc 0 L)
    (hmax : ∀ n, IsMaxOn (p n).u (Icc 0 L) (x n))
    (hliminf : ∃ l₀, (a/b)^(1/alpha) < l₀ ∧ ∀ᶠ n in atTop, l₀ ≤ (p n).u (x n)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ xstar ∈ Icc 0 L, ∃ c : ℝ,
      0 ≤ c ∧ c ≤ ((a/b)^(1/alpha))^gamma ∧
      Tendsto (fun k => x (phi k)) atTop (𝓝 xstar) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).v) (fun _ => nu/mu*c) atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).dv) (fun _ => 0) atTop (Icc 0 L) ∧
      (∀ z w, 0 ≤ z → z ≤ w → w ≤ L →
        Tendsto (fun n => ∫ t in z..w, (p (phi n)).u t^gamma) atTop (𝓝 (c*(w-z)))) ∧
      ∀ delta > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
        ∃ y ∈ Ioo (max 0 (xstar-delta)) (min L (xstar+delta)), K < |(p (phi k)).du y| := by
  let uStar := (a/b)^(1/alpha)
  have hstar : 0 < uStar := Real.rpow_pos_of_pos (div_pos ha hb) _
  have hI := fun n => (p n).interval_bounds ha hb halpha hL (hpos n) (hnonconst n)
  have hmass : ∀ n, ∫ z in (0 : ℝ)..L, (p n).u z ≤ L*uStar := fun n => (hI n).2.2.1.le
  have hmoment : ∀ n, ∫ z in (0 : ℝ)..L, (p n).u z^(1+alpha) ≤ L*uStar^(1+alpha) :=
    fun n => (hI n).2.2.2.le
  obtain ⟨phi,hphi,xstar,hxs,hxlim,hblow⟩ := gradient_blowup p s hL ha.le hb.le halpha
    hg hmu hnu hm hbeta hchi hstar hpos hvpos hddv hmass hx hmax hliminf
  obtain ⟨psi,hpsi,c,hc,hV,hDV,hweak⟩ := ClassicalSpikeSubsequence.exists_constant_signal_subsequence
    (fun n => p (phi n)) (fun n => s (phi n)) hL ha.le hb.le halpha hg hmu hnu hm hbeta
    (by linarith : 1 < 1+alpha) hga (by positivity : 0 ≤ L*uStar^(1+alpha))
    (hchi.comp hphi.tendsto_atTop) (fun n => hpos (phi n)) (fun n => hvpos (phi n))
    (fun n => hddv (phi n)) (fun n => hmoment (phi n))
  have hc1 := (SpikeLimit.spike_limit_constant_le hL halpha hstar.le hg hga.le
    (fun n => (p (phi (psi n))).continuous_u) (fun n z hz => (hpos (phi (psi n)) z hz).le)
    (fun n => hmoment (phi (psi n))) (by simpa using hweak 0 L le_rfl hL.le le_rfl)).2
  exact ⟨fun n => phi (psi n),hphi.comp hpsi,xstar,hxs,c,hc,hc1,
    hxlim.comp hpsi.tendsto_atTop,hV,hDV,hweak,
    SpikeLimit.gradient_blowup_subseq hpsi hblow⟩

/-- The same spike subsequence carries every conjugate Lq test for the source
and all three signal components: the explicit componentwise weak-W2q criterion. -/
theorem logistic_spike_all_tests
    {L a b alpha gamma mu nu m beta : ℝ} {chi : ℕ → ℝ} {x : ℕ → ℝ}
    (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hga : gamma < 1+alpha)
    (hmu : 0 < mu) (hnu : 0 < nu) (hm : 0 < m) (hbeta : 0 ≤ beta)
    (hchi : Tendsto chi atTop atTop)
    (hpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).u z)
    (hvpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).v z)
    (hddv : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hnonconst : ∀ n, ∃ z ∈ Icc 0 L, ∃ w ∈ Icc 0 L, (p n).u z ≠ (p n).u w)
    (hx : ∀ n, x n ∈ Icc 0 L)
    (hmax : ∀ n, IsMaxOn (p n).u (Icc 0 L) (x n))
    (hliminf : ∃ l₀, (a/b)^(1/alpha) < l₀ ∧ ∀ᶠ n in atTop, l₀ ≤ (p n).u (x n)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ xstar ∈ Icc 0 L, ∃ c : ℝ,
      0 ≤ c ∧ c ≤ ((a/b)^(1/alpha))^gamma ∧
      Tendsto (fun k => x (phi k)) atTop (𝓝 xstar) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).v) (fun _ => nu/mu*c) atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).dv) (fun _ => 0) atTop (Icc 0 L) ∧
      (∀ z w, 0 ≤ z → z ≤ w → w ≤ L →
        Tendsto (fun n => ∫ t in z..w, (p (phi n)).u t^gamma) atTop (𝓝 (c*(w-z)))) ∧
      (∀ g : Lp ℝ (ENNReal.ofReal (((1+alpha)/gamma)/((1+alpha)/gamma-1)))
          (SignalWeakSource.intervalVolume L),
        Tendsto (fun n => ∫ z : Icc (0 : ℝ) L, (p (phi n)).u z^gamma*g z
          ∂SignalWeakSource.intervalVolume L) atTop
          (𝓝 (∫ z : Icc (0 : ℝ) L, c*g z ∂SignalWeakSource.intervalVolume L)) ∧
        Tendsto (fun n => ∫ z : Icc (0 : ℝ) L, (p (phi n)).v z*g z
          ∂SignalWeakSource.intervalVolume L) atTop
          (𝓝 (∫ z : Icc (0 : ℝ) L, (nu/mu*c)*g z ∂SignalWeakSource.intervalVolume L)) ∧
        Tendsto (fun n => ∫ z : Icc (0 : ℝ) L, (p (phi n)).dv z*g z
          ∂SignalWeakSource.intervalVolume L) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫ z : Icc (0 : ℝ) L, (s (phi n)).ddv z*g z
          ∂SignalWeakSource.intervalVolume L) atTop (𝓝 0)) ∧
      ∀ delta > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
        ∃ y ∈ Ioo (max 0 (xstar-delta)) (min L (xstar+delta)), K < |(p (phi k)).du y| := by
  obtain ⟨phi,hphi,xstar,hxs,c,hc,hc1,hxlim,hV,hDV,hweak,hblow⟩ :=
    logistic_spike_subsequence p s hL ha hb halpha hg hga hmu hnu hm hbeta hchi
      hpos hvpos hddv hnonconst hx hmax hliminf
  have hmoment : ∀ n, ∫ z in (0 : ℝ)..L, (p n).u z^(1+alpha) ≤
      L*((a/b)^(1/alpha))^(1+alpha) :=
    fun n => ((p n).interval_bounds ha hb halpha hL (hpos n) (hnonconst n)).2.2.2.le
  have htests := SignalWeakSobolev.all_components_test_tendsto L mu nu gamma (1+alpha)
    (L*((a/b)^(1/alpha))^(1+alpha)) c
    (fun n => (p (phi n)).u) (fun n => (p (phi n)).v)
    (fun n => (p (phi n)).dv) (fun n => (s (phi n)).ddv)
    hL hmu hnu hg (by linarith) hga (by positivity)
    (fun n => (p (phi n)).continuous_u) (fun n z hz => (hpos (phi n) z hz).le)
    (fun n => (s (phi n)).continuous_v) (fun n => hvpos (phi n))
    (fun n => (s (phi n)).continuous_dv) (fun n => hddv (phi n))
    (fun n => (p (phi n)).derivative_v) (fun n => (s (phi n)).derivative_dv)
    (fun n => (s (phi n)).stationary) (fun n => (p (phi n)).neumann_v_left)
    (fun n => (p (phi n)).neumann_v_right) (fun n => hmoment (phi n)) hV hDV
  exact ⟨phi,hphi,xstar,hxs,c,hc,hc1,hxlim,hV,hDV,hweak,htests,hblow⟩

/-- Compactness of the physical interval supplies the maximizers themselves.
The eventual peak assumption is exactly the liminf-maximum gap in witness form. -/
theorem gradient_blowup_of_eventual_peak
    {L a b alpha gamma mu nu m beta uStar : ℝ} {chi : ℕ → ℝ}
    (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hmu : 0 < mu) (hnu : 0 < nu) (hm : 0 < m) (hbeta : 0 ≤ beta)
    (hchi : Tendsto chi atTop atTop) (huStar : 0 < uStar)
    (hpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).u z)
    (hvpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).v z)
    (hddv : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hmass : ∀ n, ∫ z in (0 : ℝ)..L, (p n).u z ≤ L*uStar)
    (hpeak : ∃ l₀, uStar < l₀ ∧ ∀ᶠ n in atTop, ∃ z ∈ Icc 0 L, l₀ ≤ (p n).u z) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ xstar ∈ Icc 0 L,
      ∀ delta > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
        ∃ y ∈ Ioo (max 0 (xstar-delta)) (min L (xstar+delta)), K < |(p (phi k)).du y| := by
  have hex : ∀ n, ∃ z ∈ Icc 0 L, IsMaxOn (p n).u (Icc 0 L) z :=
    fun n => isCompact_Icc.exists_isMaxOn ⟨0,⟨le_rfl,hL.le⟩⟩ (p n).continuous_u
  choose x hx hmax using hex
  have hliminf : ∃ l₀, uStar < l₀ ∧ ∀ᶠ n in atTop, l₀ ≤ (p n).u (x n) := by
    obtain ⟨l₀,hl,hp⟩ := hpeak
    refine ⟨l₀,hl,hp.mono ?_⟩
    intro n hn
    obtain ⟨z,hz,hh⟩ := hn
    exact hh.trans (hmax n hz)
  obtain ⟨phi,hphi,xstar,hxs,_,hblow⟩ := gradient_blowup p s hL ha hb halpha hg hmu hnu
    hm hbeta hchi huStar hpos hvpos hddv hmass hx hmax hliminf
  exact ⟨phi,hphi,xstar,hxs,hblow⟩

/-- The minimal-model Theorem 1.4 gradient conclusion for actual prescribed-mass
classical solutions. No maximizers, compactness or limiting equation are assumed. -/
theorem minimal_gradient_blowup
    {L alpha gamma mu nu m beta uStar : ℝ} {chi : ℕ → ℝ}
    (p : ∀ n, StationaryMassIdentity.ClassicalProfile L 0 0 alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hmu : 0 < mu) (hnu : 0 < nu) (hm : 0 < m) (hbeta : 0 ≤ beta)
    (hchi : Tendsto chi atTop atTop) (huStar : 0 < uStar)
    (hpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).u z)
    (hvpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).v z)
    (hddv : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hmass : ∀ n, ∫ z in (0 : ℝ)..L, (p n).u z = L*uStar)
    (hpeak : ∃ l₀, uStar < l₀ ∧ ∀ᶠ n in atTop, ∃ z ∈ Icc 0 L, l₀ ≤ (p n).u z) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ xstar ∈ Icc 0 L,
      ∀ delta > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
        ∃ y ∈ Ioo (max 0 (xstar-delta)) (min L (xstar+delta)), K < |(p (phi k)).du y| := by
  exact gradient_blowup_of_eventual_peak p s hL le_rfl le_rfl halpha hg hmu hnu hm hbeta
    hchi huStar hpos hvpos hddv (fun n => (hmass n).le) hpeak

/-- The full logistic gradient conclusion for every gamma>0, with its mean
bound derived from the actual PDE and its maximizers constructed internally. -/
theorem logistic_gradient_blowup_of_eventual_peak
    {L a b alpha gamma mu nu m beta : ℝ} {chi : ℕ → ℝ}
    (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hmu : 0 < mu) (hnu : 0 < nu) (hm : 0 < m) (hbeta : 0 ≤ beta)
    (hchi : Tendsto chi atTop atTop)
    (hpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).u z)
    (hvpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).v z)
    (hddv : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hnonconst : ∀ n, ∃ z ∈ Icc 0 L, ∃ w ∈ Icc 0 L, (p n).u z ≠ (p n).u w)
    (hpeak : ∃ l₀, (a/b)^(1/alpha) < l₀ ∧ ∀ᶠ n in atTop, ∃ z ∈ Icc 0 L, l₀ ≤ (p n).u z) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ xstar ∈ Icc 0 L,
      ∀ delta > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
        ∃ y ∈ Ioo (max 0 (xstar-delta)) (min L (xstar+delta)), K < |(p (phi k)).du y| := by
  have hstar : 0 < (a/b)^(1/alpha) := Real.rpow_pos_of_pos (div_pos ha hb) _
  have hmass : ∀ n, ∫ z in (0 : ℝ)..L, (p n).u z ≤ L*((a/b)^(1/alpha)) :=
    fun n => ((p n).interval_bounds ha hb halpha hL (hpos n) (hnonconst n)).2.2.1.le
  exact gradient_blowup_of_eventual_peak p s hL ha.le hb.le halpha hg hmu hnu hm hbeta
    hchi hstar hpos hvpos hddv hmass hpeak

/-- The logistic moreover conclusion on an actual constructed subsequence,
with no supplied maximum points or extraction/tested-limit assumptions. -/
theorem logistic_spike_all_tests_of_eventual_peak
    {L a b alpha gamma mu nu m beta : ℝ} {chi : ℕ → ℝ}
    (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hga : gamma < 1+alpha)
    (hmu : 0 < mu) (hnu : 0 < nu) (hm : 0 < m) (hbeta : 0 ≤ beta)
    (hchi : Tendsto chi atTop atTop)
    (hpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).u z)
    (hvpos : ∀ n z, z ∈ Icc 0 L → 0 < (p n).v z)
    (hddv : ∀ n, ContinuousOn (s n).ddv (Icc 0 L))
    (hnonconst : ∀ n, ∃ z ∈ Icc 0 L, ∃ w ∈ Icc 0 L, (p n).u z ≠ (p n).u w)
    (hpeak : ∃ l₀, (a/b)^(1/alpha) < l₀ ∧
      ∀ᶠ n in atTop, ∃ z ∈ Icc 0 L, l₀ ≤ (p n).u z) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ xstar ∈ Icc 0 L, ∃ c : ℝ,
      0 ≤ c ∧ c ≤ ((a/b)^(1/alpha))^gamma ∧
      TendstoUniformlyOn (fun n => (p (phi n)).v) (fun _ => nu/mu*c) atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => (p (phi n)).dv) (fun _ => 0) atTop (Icc 0 L) ∧
      (∀ z w, 0 ≤ z → z ≤ w → w ≤ L →
        Tendsto (fun n => ∫ t in z..w, (p (phi n)).u t^gamma) atTop (𝓝 (c*(w-z)))) ∧
      (∀ g : Lp ℝ (ENNReal.ofReal (((1+alpha)/gamma)/((1+alpha)/gamma-1)))
          (SignalWeakSource.intervalVolume L),
        Tendsto (fun n => ∫ z : Icc (0 : ℝ) L, (p (phi n)).u z^gamma*g z
          ∂SignalWeakSource.intervalVolume L) atTop
          (𝓝 (∫ z : Icc (0 : ℝ) L, c*g z ∂SignalWeakSource.intervalVolume L)) ∧
        Tendsto (fun n => ∫ z : Icc (0 : ℝ) L, (p (phi n)).v z*g z
          ∂SignalWeakSource.intervalVolume L) atTop
          (𝓝 (∫ z : Icc (0 : ℝ) L, (nu/mu*c)*g z ∂SignalWeakSource.intervalVolume L)) ∧
        Tendsto (fun n => ∫ z : Icc (0 : ℝ) L, (p (phi n)).dv z*g z
          ∂SignalWeakSource.intervalVolume L) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫ z : Icc (0 : ℝ) L, (s (phi n)).ddv z*g z
          ∂SignalWeakSource.intervalVolume L) atTop (𝓝 0)) ∧
      ∀ delta > 0, ∀ K : ℝ, ∀ᶠ k in atTop,
        ∃ y ∈ Ioo (max 0 (xstar-delta)) (min L (xstar+delta)), K < |(p (phi k)).du y| := by
  have hex : ∀ n, ∃ z ∈ Icc 0 L, IsMaxOn (p n).u (Icc 0 L) z :=
    fun n => isCompact_Icc.exists_isMaxOn ⟨0,⟨le_rfl,hL.le⟩⟩ (p n).continuous_u
  choose x hx hmax using hex
  have hliminf : ∃ l₀, (a/b)^(1/alpha) < l₀ ∧ ∀ᶠ n in atTop, l₀ ≤ (p n).u (x n) := by
    obtain ⟨l₀,hl,hp⟩ := hpeak
    refine ⟨l₀,hl,hp.mono ?_⟩
    intro n hn
    obtain ⟨z,hz,hh⟩ := hn
    exact hh.trans (hmax n hz)
  obtain ⟨phi,hphi,xstar,hxs,c,hc,hc1,_,hV,hDV,hweak,htests,hblow⟩ :=
    logistic_spike_all_tests p s hL ha hb halpha hg hga hmu hnu hm hbeta hchi
      hpos hvpos hddv hnonconst hx hmax hliminf
  exact ⟨phi,hphi,xstar,hxs,c,hc,hc1,hV,hDV,hweak,htests,hblow⟩

end
end ChemotaxisBifurcation.ClassicalSpikeBlowup
