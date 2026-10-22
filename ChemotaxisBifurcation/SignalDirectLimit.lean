module
public import ChemotaxisBifurcation.SignalSourceVanishing
public import ChemotaxisBifurcation.SignalCompactness
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A direct constant-signal limit deduction

The paper's cutoff/first-integral argument already forces local source
integrals to vanish wherever the limiting signal derivative is nonzero.
Actual integrated signal equations then identify a local homogeneous ODE.
An extrema argument forces the limiting derivative to vanish everywhere.
This gives constant C1 limits and interval-tested source convergence without
constructing a weak source density. It does not itself assert weak Lq or
weak W2q convergence; those remain separate stronger statements.
-/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
namespace ChemotaxisBifurcation.SignalDirectLimit
noncomputable section

/-- An elementary extrema argument: the limit gradient vanishes if its
nonzero points satisfy the homogeneous signal equation. No weak source limit
or assumed constancy is required. -/
theorem gradient_eq_zero_of_local_signal_ode {L mu : ℝ} {V dV : ℝ → ℝ}
    (hL : 0 < L) (hmu : 0 < mu)
    (_hV : ContinuousOn V (Icc 0 L)) (hdV : ContinuousOn dV (Icc 0 L))
    (hV0 : ∀ x ∈ Icc 0 L, 0 ≤ V x)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x)
    (hlocal : ∀ x ∈ Ioo 0 L, dV x ≠ 0 → HasDerivAt dV (mu * V x) x)
    (hbc0 : dV 0 = 0) (hbcL : dV L = 0) :
    ∀ x ∈ Icc 0 L, dV x = 0 := by
  have extremum_zero : ∀ y ∈ Icc 0 L,
      (IsMinOn dV (Icc 0 L) y ∨ IsMaxOn dV (Icc 0 L) y) → dV y = 0 := by
    intro y hy hext
    by_contra hne
    have hy0 : y ≠ 0 := by intro hh; apply hne; simpa [hh] using hbc0
    have hyL : y ≠ L := by intro hh; apply hne; simpa [hh] using hbcL
    have hyI : y ∈ Ioo 0 L :=
      ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0), lt_of_le_of_ne hy.2 hyL⟩
    have hnhds := Icc_mem_nhds hyI.1 hyI.2
    have hzero : mu * V y = 0 := by
      rcases hext with hmin | hmax
      · exact (hmin.isLocalMin hnhds).hasDerivAt_eq_zero (hlocal y hyI hne)
      · exact (hmax.isLocalMax hnhds).hasDerivAt_eq_zero (hlocal y hyI hne)
    have hVy : V y = 0 := (mul_eq_zero.mp hzero).resolve_left hmu.ne'
    have hminV : IsMinOn V (Icc 0 L) y := by
      intro x hx
      rw [hVy]
      exact hV0 x hx
    exact hne ((hminV.isLocalMin hnhds).hasDerivAt_eq_zero (hderiv y hyI))
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hdV
  obtain ⟨b, hb, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hL.le) hdV
  have hamin := extremum_zero a ha (Or.inl hmin)
  have hbmax := extremum_zero b hb (Or.inr hmax)
  intro x hx
  have hlo := hmin hx
  have hhi := hmax hx
  rw [hamin] at hlo
  rw [hbmax] at hhi
  exact le_antisymm hhi hlo

/-- Integrated signal equation on an arbitrary closed subinterval. -/
theorem signal_source_integral_eq (L mu nu gamma p q : ℝ) (u v dv ddv : ℝ → ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ L) (hnu : nu ≠ 0) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hdv : ContinuousOn dv (Icc 0 L))
    (hderiv2 : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (heq : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0) :
    (∫ x in p..q, u x ^ gamma) =
      (mu * (∫ x in p..q, v x) - (dv q - dv p)) / nu := by
  have hsub : Icc p q ⊆ Icc 0 L := Icc_subset_Icc hp hq
  have hcu := hu.rpow_const (p := gamma) (fun _ _ => Or.inr hgamma)
  have hcv := (hv.const_smul mu).sub (hcu.const_smul nu)
  have hder : ∀ x ∈ Ioo p q, HasDerivAt dv (mu * v x - nu * u x ^ gamma) x := by
    intro x hx
    have hxI : x ∈ Ioo 0 L := ⟨hp.trans_lt hx.1, hx.2.trans_le hq⟩
    convert hderiv2 x hxI using 1
    linarith [heq x hxI]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpq (hdv.mono hsub)
    hder ((hcv.mono hsub).intervalIntegrable_of_Icc hpq)
  rw [intervalIntegral.integral_sub (((hv.mono hsub).intervalIntegrable_of_Icc hpq).const_mul mu)
      (((hcu.mono hsub).intervalIntegrable_of_Icc hpq).const_mul nu),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  apply (eq_div_iff hnu).mpr
  linarith

/-- Actual uniform signal/gradient convergence already determines every
population-source interval integral limit, without extracting a weak density. -/
theorem source_integral_tendsto_of_signal_pair_limit (L mu nu gamma p q : ℝ)
    (u v dv ddv : ℕ → ℝ → ℝ) (V dV : ℝ → ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ L) (hnu : nu ≠ 0) (hgamma : 0 ≤ gamma)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (heq : ∀ n x, x ∈ Ioo 0 L → ddv n x - mu * v n x + nu * u n x ^ gamma = 0)
    (hvlim : TendstoUniformlyOn v V atTop (Icc 0 L))
    (hdvlim : TendstoUniformlyOn dv dV atTop (Icc 0 L)) :
    Tendsto (fun n => ∫ x in p..q, u n x ^ gamma) atTop
      (𝓝 ((mu * (∫ x in p..q, V x) - (dV q - dV p)) / nu)) := by
  have hsub : uIcc p q ⊆ Icc 0 L := by
    rw [uIcc_of_le hpq]
    exact Icc_subset_Icc hp hq
  have hint := (hvlim.mono hsub).tendsto_intervalIntegral_of_continuousOn
    (μ := volume) (Eventually.of_forall fun n => (hv n).mono hsub)
  have hpI : p ∈ Icc 0 L := ⟨hp, hpq.trans hq⟩
  have hqI : q ∈ Icc 0 L := ⟨hp.trans hpq, hq⟩
  have hlim := (((tendsto_const_nhds (x := mu)).mul hint).sub
    ((hdvlim.tendsto_at hqI).sub (hdvlim.tendsto_at hpI))).div_const nu
  have he : (fun n => ∫ x in p..q, u n x ^ gamma) =
      (fun n => (mu * (∫ x in p..q, v n x) - (dv n q - dv n p)) / nu) := by
    funext n
    exact signal_source_integral_eq L mu nu gamma p q (u n) (v n) (dv n) (ddv n)
      hp hpq hq hnu hgamma (hu n) (hv n) (hdv n) (hderiv2 n) (heq n)
  rw [he]
  exact hlim
/-- Local interval identities imply the homogeneous signal ODE wherever the
gradient does not vanish. This is the deterministic replacement for invoking
an extracted weak source density. -/
theorem local_ode_of_interval_relation {L mu : ℝ} {V dV : ℝ → ℝ}
    (hV : ContinuousOn V (Icc 0 L)) (hdV : ContinuousOn dV (Icc 0 L))
    (hrel : ∀ p q : ℝ, 0 < p → p < q → q < L →
      (∀ t ∈ Icc p q, dV t ≠ 0) →
      ∀ a b : ℝ, p < a → a < b → b < q →
        dV b - dV a = mu * ∫ t in a..b, V t) :
    ∀ x ∈ Ioo 0 L, dV x ≠ 0 → HasDerivAt dV (mu * V x) x := by
  intro x hx hne
  have hcont := hdV.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hev : ∀ᶠ t in 𝓝 x, t ∈ Ioo 0 L ∧ dV t ≠ 0 :=
    Filter.Eventually.and (Ioo_mem_nhds hx.1 hx.2) (hcont.eventually_ne hne)
  obtain ⟨e, he, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let p := x - e / 2
  let q := x + e / 2
  have hinside : ∀ t ∈ Icc p q, t ∈ Ioo 0 L ∧ dV t ≠ 0 := by
    intro t ht
    apply hball
    rw [Real.dist_eq, abs_lt]
    dsimp [p, q] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hpq : p < q := by dsimp [p, q]; linarith
  have hp : 0 < p := (hinside p (left_mem_Icc.mpr hpq.le)).1.1
  have hq : q < L := (hinside q (right_mem_Icc.mpr hpq.le)).1.2
  have hpx : p < x := by dsimp [p]; linarith
  have hxq : x < q := by dsimp [q]; linarith
  have hidentity : ∀ t ∈ Ioo p q,
      dV t = dV x + mu * ((∫ z in (0 : ℝ)..t, V z) - ∫ z in (0 : ℝ)..x, V z) := by
    intro t ht
    have htI := (hinside t (Ioo_subset_Icc_self ht)).1
    have hsub0x : uIcc 0 x ⊆ Icc 0 L := by
      rw [uIcc_of_le hx.1.le]
      exact Icc_subset_Icc le_rfl hx.2.le
    have hsubxt : uIcc x t ⊆ Icc 0 L := by
      apply uIcc_subset_Icc
      · exact Ioo_subset_Icc_self hx
      · exact Ioo_subset_Icc_self htI
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hV.mono hsub0x).intervalIntegrable)
      ((hV.mono hsubxt).intervalIntegrable)
    rcases lt_trichotomy x t with hxt | hxt | htx
    · have hh := hrel p q hp hpq hq (fun z hz => (hinside z hz).2) x t hpx hxt ht.2
      linear_combination hh + mu * hsplit
    · subst t
      ring
    · have hh := hrel p q hp hpq hq (fun z hz => (hinside z hz).2) t x ht.1 htx hxq
      rw [intervalIntegral.integral_symm] at hh
      linear_combination -hh + mu * hsplit
  have hpder := (SpikeEstimates.hasDerivAt_primitive hV hx).sub_const
    (∫ z in (0 : ℝ)..x, V z)
  have hder := (hpder.const_mul mu).const_add (dV x)
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hpx hxq] with t ht
  exact hidentity t ht
/-- Constant signal limit and interval-tested population-source convergence
without any weak-source extraction or limiting density premise. This retains
the ordinary actual first integral and moment data and classical signal
pair convergence, which can be produced by SignalCompactness. It does not
claim weak Lq or weak W2q convergence. -/
theorem constant_limit_without_weak_source {L gamma m r beta kappa mu nu M Fb R : ℝ}
    {chi : ℕ → ℝ} {u du v dv ddv F : ℕ → ℝ → ℝ} {V dV : ℝ → ℝ}
    (hL : 0 < L) (hγ : 0 < gamma) (hγr : gamma < r) (hm : 0 < m) (hkappa : 0 < kappa)
    (hmu : 0 < mu) (hnu : 0 < nu) (hchi : Tendsto chi atTop atTop)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hdu : ∀ n, ∀ x ∈ Ioo 0 L, HasDerivAt (u n) (du n x) x)
    (hdu_cont : ∀ n, ContinuousOn (du n) (Icc 0 L))
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L)) (hv0 : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ v n x)
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L)) (hF : ∀ n, ContinuousOn (F n) (Icc 0 L))
    (hflux : ∀ n, ∀ x ∈ Icc 0 L,
      du n x = chi n * (u n x ^ m / (1 + v n x) ^ beta * dv n x) - F n x)
    (hFb : ∀ n, ∀ x ∈ Icc 0 L, |F n x| ≤ Fb)
    (hkappa_le : ∀ n, ∀ x ∈ Icc 0 L, kappa ≤ 1 / (1 + v n x) ^ beta)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x ≤ M)
    (hR : ∀ n, ∫ x in (0 : ℝ)..L, u n x ^ r ≤ R)
    (hV : ContinuousOn V (Icc 0 L)) (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x)
    (hdV_cont : ContinuousOn dV (Icc 0 L)) (hV0 : ∀ x ∈ Icc 0 L, 0 ≤ V x)
    (hdvconv : TendstoUniformlyOn dv dV atTop (Icc 0 L))
    (hvconv : TendstoUniformlyOn v V atTop (Icc 0 L))
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (hsignal : ∀ n x, x ∈ Ioo 0 L → ddv n x - mu * v n x + nu * u n x ^ gamma = 0)
    (hbc0 : dV 0 = 0) (hbcL : dV L = 0) :
    ∃ c, 0 ≤ c ∧ (∀ x ∈ Icc 0 L, V x = nu / mu * c) ∧
      (∀ x ∈ Icc 0 L, dV x = 0) ∧
      ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
        Tendsto (fun n => ∫ x in p..q, u n x ^ gamma) atTop (𝓝 (c * (q - p))) := by
  have hrel : ∀ p q : ℝ, 0 < p → p < q → q < L →
      (∀ t ∈ Icc p q, dV t ≠ 0) →
      ∀ a b : ℝ, p < a → a < b → b < q →
        dV b - dV a = mu * ∫ t in a..b, V t := by
    intro p q hp hpq hq hne a b hpa hab hbq
    have hzero := SpikeLimit.source_integral_tendsto_zero_of_nonzero_limit_gradient
      hp hpa hab hbq hq hγ hγr hm hkappa hchi hu hu0 hdu hdu_cont hv hv0 hdv hF
      hflux hFb hkappa_le hmass hR hdvconv hdV_cont hne
    have hlim := source_integral_tendsto_of_signal_pair_limit L mu nu gamma a b
      u v dv ddv V dV (by linarith) hab.le (by linarith) hnu.ne' hγ.le hu hv hdv
      hderiv2 hsignal hvconv hdvconv
    have heq : (mu * (∫ t in a..b, V t) - (dV b - dV a)) / nu = 0 :=
      tendsto_nhds_unique hlim hzero
    have hz := (div_eq_zero_iff).mp heq
    rcases hz with hz | hz
    · linarith
    · exact (hnu.ne' hz).elim
  have hlocal := local_ode_of_interval_relation hV hdV_cont hrel
  have hgrad := gradient_eq_zero_of_local_signal_ode hL hmu hV hdV_cont hV0 hdV hlocal hbc0 hbcL
  have hconstant : ∀ x ∈ Icc 0 L, V x = V 0 :=
    MinimalFlux.eq_left_of_hasDerivAt_zero hV (fun x hx => by
      simpa only [hgrad x (Ioo_subset_Icc_self hx)] using hdV x hx)
  let c := mu * V 0 / nu
  have hc : 0 ≤ c := div_nonneg (mul_nonneg hmu.le (hV0 0 ⟨le_rfl, hL.le⟩)) hnu.le
  have hVc : ∀ x ∈ Icc 0 L, V x = nu / mu * c := by
    intro x hx
    rw [hconstant x hx]
    dsimp [c]
    field_simp
  refine ⟨c, hc, hVc, hgrad, ?_⟩
  intro p q hp hpq hq
  have hint : (∫ x in p..q, V x) = V 0 * (q - p) := by
    rw [intervalIntegral.integral_congr (g := fun _ => V 0) (fun x hx => by
      rw [uIcc_of_le hpq] at hx
      exact hconstant x ⟨hp.trans hx.1, hx.2.trans hq⟩)]
    simp [mul_comm]
  have hlim := source_integral_tendsto_of_signal_pair_limit L mu nu gamma p q
    u v dv ddv V dV hp hpq hq hnu.ne' hγ.le hu hv hdv hderiv2 hsignal hvconv hdvconv
  have htarget : (mu * (∫ x in p..q, V x) - (dV q - dV p)) / nu = c * (q - p) := by
    rw [hint, hgrad q ⟨hp.trans hpq, hq⟩, hgrad p ⟨hp, hpq.trans hq⟩]
    dsimp [c]
    ring
  rwa [htarget] at hlim

end
end ChemotaxisBifurcation.SignalDirectLimit
