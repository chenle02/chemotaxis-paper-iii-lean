module
public import ChemotaxisBifurcation.SpikeLimit

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.SpikeLimit
open Set Filter Topology MeasureTheory

/-- Local population-source integral vanishing follows from the actual first
integral, uniform moment bounds and uniform signal-derivative convergence.
There is no weak source limit or weak extraction hypothesis. This exposes
the deterministic first part of `weakLimit_ae_zero` for a direct limit route. -/
theorem source_integral_tendsto_zero_of_nonzero_limit_gradient {L p q p' q' gamma m r beta kappa M Fb R : ℝ}
    {chi : ℕ → ℝ} {u du v dv F : ℕ → ℝ → ℝ} {dV : ℝ → ℝ}
    (hp : 0 < p) (hpp : p < p') (hpq : p' < q') (hqq : q' < q) (hq : q < L)
    (hγ : 0 < gamma) (hγr : gamma < r) (hm : 0 < m) (hkappa : 0 < kappa)
    (hchi : Tendsto chi atTop atTop)
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
    (hdvconv : TendstoUniformlyOn dv dV atTop (Icc 0 L))
    (hdV_cont : ContinuousOn dV (Icc 0 L)) (hdV_ne : ∀ x ∈ Icc p q, dV x ≠ 0)
 :
    Tendsto (fun n => ∫ x in p'..q', u n x ^ gamma) atTop (𝓝 0) := by
  have hL : 0 < L := by linarith
  have hpqI : Icc p q ⊆ Icc 0 L := Icc_subset_Icc hp.le hq.le
  -- the sign of `V_x` on `[p,q]` and a uniform lower bound `σ₀`
  obtain ⟨s, hs, hspos⟩ := exists_sign_pos (by linarith) (hdV_cont.mono hpqI) hdV_ne
  obtain ⟨xm, hxm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by linarith))
    ((continuousOn_const.mul hdV_cont).mono hpqI : ContinuousOn (fun x => s * dV x) (Icc p q))
  set σ0 : ℝ := s * dV xm with hσ0_def
  have hσ0 : 0 < σ0 := hspos xm hxm
  -- eventually `s (v_n)_x ≥ σ₀/2` on `[p,q]`
  have hev : ∀ᶠ n in atTop, ∀ x ∈ Icc p q, σ0 / 2 ≤ s * dv n x := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hdvconv (σ0 / 2) (by linarith)] with n hn
    intro x hx
    have h1 := hn x (hpqI hx)
    rw [Real.dist_eq] at h1
    have h2 : σ0 ≤ s * dV x := hmin hx
    have h3 : |s * dv n x - s * dV x| < σ0 / 2 := by
      rw [← mul_sub, abs_mul, hs, one_mul, abs_sub_comm]; exact h1
    have := neg_abs_le (s * dv n x - s * dV x)
    linarith
  -- the test function: a smooth bump, one on `[p',q']`, supported in `(p,q)`
  set c0 : ℝ := (p' + q') / 2 with hc0
  set ρ : ℝ := min (p' - p) (q - q') with hρ_def
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  let bump : ContDiffBump c0 :=
    ⟨(q' - p') / 2, (q' - p') / 2 + ρ, by linarith, by linarith⟩
  set phi : ℝ → ℝ := fun x => bump x with hphi_def
  have hphi_cd : ContDiff ℝ 1 phi := bump.contDiff
  have hphi_der : ∀ x, HasDerivAt phi (deriv phi x) x := fun x =>
    ((hphi_cd.differentiable one_ne_zero) x).hasDerivAt
  have hdphi : Continuous (deriv phi) := hphi_cd.continuous_deriv le_rfl
  have hsupp : ∀ x, phi x ≠ 0 → x ∈ Icc p q := by
    intro x hx
    have hmem : x ∈ Function.support bump := hx
    rw [bump.support_eq, Real.ball_eq_Ioo] at hmem
    have h1 : ρ ≤ p' - p := min_le_left _ _
    have h2 : ρ ≤ q - q' := min_le_right _ _
    constructor
    · have := hmem.1; simp only [bump] at this; linarith
    · have := hmem.2; simp only [bump] at this; linarith
  have hphi_one : ∀ x ∈ Icc p' q', phi x = 1 := by
    intro x hx
    refine bump.one_of_mem_closedBall ?_
    rw [Real.closedBall_eq_Icc]
    simp only [bump]
    constructor <;> linarith [hx.1, hx.2]
  have hphi_zero : ∀ x, x ∉ Icc p q → phi x = 0 := fun x hx => by
    by_contra h; exact hx (hsupp x h)
  have hphi0 : phi 0 = 0 := hphi_zero 0 fun h => by linarith [h.1]
  have hphiL : phi L = 0 := hphi_zero L fun h => by linarith [h.2]
  have hphi_nonneg : ∀ x, 0 ≤ phi x := fun x => bump.nonneg
  have hphi_le : ∀ x, phi x ≤ 1 := fun x => bump.le_one
  -- a bound `D` for `|φ'|` on `[0,L]`
  obtain ⟨xD, -, hD⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hL.le)
    (hdphi.abs.continuousOn : ContinuousOn (fun x => |deriv phi x|) (Icc 0 L))
  set D : ℝ := |deriv phi xD|
  -- the right-hand side of the test-function estimate is bounded
  have hrhs : ∀ n, |∫ x in (0 : ℝ)..L, u n x * deriv phi x| +
      |∫ x in (0 : ℝ)..L, F n x * phi x| ≤ D * M + Fb * L := by
    intro n
    have h1 : |∫ x in (0 : ℝ)..L, u n x * deriv phi x| ≤ D * M := by
      refine (intervalIntegral.abs_integral_le_integral_abs hL.le).trans ?_
      have hle : ∫ x in (0 : ℝ)..L, |u n x * deriv phi x| ≤ ∫ x in (0 : ℝ)..L, D * u n x := by
        refine intervalIntegral.integral_mono_on hL.le
          (((hu n).mul hdphi.continuousOn).abs.intervalIntegrable_of_Icc hL.le)
          (((hu n).intervalIntegrable_of_Icc hL.le).const_mul D) fun x hx => ?_
        rw [abs_mul, abs_of_nonneg (hu0 n x hx), mul_comm]
        exact mul_le_mul_of_nonneg_right (hD hx) (hu0 n x hx)
      rw [intervalIntegral.integral_const_mul] at hle
      have hD0 : 0 ≤ D := abs_nonneg _
      exact hle.trans (mul_le_mul_of_nonneg_left (hmass n) hD0)
    have h2 : |∫ x in (0 : ℝ)..L, F n x * phi x| ≤ Fb * L := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L)
        (C := Fb) (f := fun x => F n x * phi x) (fun x hx => by
          rw [uIoc_of_le hL.le] at hx
          have hx' := Ioc_subset_Icc_self hx
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hphi_nonneg x)]
          calc |F n x| * phi x ≤ Fb * 1 :=
                mul_le_mul (hFb n x hx') (hphi_le x) (hphi_nonneg x)
                  ((abs_nonneg _).trans (hFb n x hx'))
            _ = Fb := mul_one _)
      rw [Real.norm_eq_abs, sub_zero, abs_of_pos hL] at this
      exact this
    linarith
  -- `∫_{p'}^{q'} u_n^m → 0`
  have hm0 : Tendsto (fun n => ∫ x in p'..q', u n x ^ m) atTop (𝓝 0) := by
    refine tendsto_zero_of_mul_le (C := D * M + Fb * L) (mul_pos hkappa (half_pos hσ0)) hchi
      (fun n => intervalIntegral.integral_nonneg hpq.le fun x hx =>
        Real.rpow_nonneg (hu0 n x ⟨by linarith [hx.1], by linarith [hx.2]⟩) _) ?_
    filter_upwards [hev, hchi.eventually_ge_atTop 0] with n hn hchin
    have h := flux_test_bound (p := p') (q := q') (s := s) (sigma := σ0 / 2) (kappa := kappa)
      (beta := beta) hL.le (by linarith) hpq.le (by linarith) hchin hm hs hkappa
      (half_pos hσ0) (hu n) (hu0 n) (hdu n) (hdu_cont n) (hv n) (hv0 n) (hdv n) (hF n)
      hphi_der hdphi hphi0 hphiL (fun x _ => hphi_nonneg x) hphi_one (hflux n) (hkappa_le n)
      (fun x _ hx => hn x (hsupp x hx))
    have := hrhs n
    calc chi n * (kappa * (σ0 / 2)) * ∫ x in p'..q', u n x ^ m
        = chi n * kappa * (σ0 / 2) * ∫ x in p'..q', u n x ^ m := by ring
      _ ≤ _ := h.trans this
  -- `∫_{p'}^{q'} u_n^γ → 0`
  have hsub : Icc p' q' ⊆ Icc 0 L := Icc_subset_Icc (by linarith) (by linarith)
  have hγ0 : Tendsto (fun n => ∫ x in p'..q', u n x ^ gamma) atTop (𝓝 0) := by
    refine tendsto_integral_rpow_zero (R := R) hpq.le u hγ hγr hm (fun n => (hu n).mono hsub)
      (fun n x hx => hu0 n x (hsub hx)) (fun n => ?_) hm0
    refine le_trans ?_ (hR n)
    refine intervalIntegral.integral_mono_interval (by linarith) hpq.le (by linarith) ?_
      (((hu n).rpow_const fun _ _ => Or.inr (hγ.trans hγr).le).intervalIntegrable_of_Icc hL.le)
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx =>
      Real.rpow_nonneg (hu0 n x (Ioc_subset_Icc_self hx)) _)
  exact hγ0

end ChemotaxisBifurcation.SpikeLimit
