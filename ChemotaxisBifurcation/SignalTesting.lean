module
public import ChemotaxisBifurcation.SpikeEstimatesLogistic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Classical signal testing and actual integral W2q norms

Discharges the testing/Hölder and Minkowski hypotheses of
`SpikeEstimatesLogistic.logistic_W2q_bound`. The final theorem is about every
given positive classical signal solution, with its actual function norms.
It does not assert existence of the solution or prove the upstream population
moment bound; that bound is the input supplied by interval mass estimates.
No center-manifold, spectral or global PDE assertion is made here.
-/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
namespace ChemotaxisBifurcation.SpikeEstimates

/-- Testing a classical nonnegative Neumann signal equation with `v^(q-1)`.
For `q ≥ 2` the multiplier remains differentiable even where `v = 0`.
No testing identity or norm inequality is assumed. -/
theorem signal_testing_rpow (L mu nu gamma q : ℝ) (u v dv ddv : ℝ → ℝ)
    (hL : 0 ≤ L) (hq : 2 ≤ q) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hv0 : ∀ x ∈ Icc 0 L, 0 ≤ v x)
    (hdv : ContinuousOn dv (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x)
    (hderiv2 : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (heq : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0) :
    mu * (∫ x in (0 : ℝ)..L, v x ^ q) ≤
      nu * ∫ x in (0 : ℝ)..L, u x ^ gamma * v x ^ (q - 1) := by
  have hp1 : 0 ≤ q - 1 := by linarith
  have hp2 : 0 ≤ q - 2 := by linarith
  have hc1 := hv.rpow_const (p := q - 1) (fun _ _ => Or.inr hp1)
  have hc2 := hv.rpow_const (p := q - 2) (fun _ _ => Or.inr hp2)
  have hcq := hv.rpow_const (p := q) (fun _ _ => Or.inr (by linarith : 0 ≤ q))
  have hcu := hu.rpow_const (p := gamma) (fun _ _ => Or.inr hgamma)
  have hcg : ContinuousOn (fun x => (q - 1) * v x ^ (q - 2) * dv x ^ 2) (Icc 0 L) :=
    (hc2.const_smul (q - 1)).mul (hdv.pow 2)
  have hcf : ContinuousOn (fun x => mu * v x ^ q - nu * (u x ^ gamma * v x ^ (q - 1))) (Icc 0 L) :=
    (hcq.const_smul mu).sub ((hcu.mul hc1).const_smul nu)
  have hid : (∫ x in (0 : ℝ)..L,
      ((q - 1) * v x ^ (q - 2) * dv x ^ 2 +
        (mu * v x ^ q - nu * (u x ^ gamma * v x ^ (q - 1))))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL
      (f := fun x => v x ^ (q - 1) * dv x)
      (hc1.mul hdv) (fun x hx => ?_) (show IntervalIntegrable (fun x => (q - 1) * v x ^ (q - 2) * dv x ^ 2 + (mu * v x ^ q - nu * (u x ^ gamma * v x ^ (q - 1)))) volume 0 L from (hcg.add hcf).intervalIntegrable_of_Icc hL)]
    · simp [hbc0, hbcL]
    · have ht := ((hderiv x hx).rpow_const (Or.inr (by linarith : 1 ≤ q - 1))).mul (hderiv2 x hx)
      have hp : v x ^ q = v x ^ (q - 1) * v x := by
        have hh := Real.rpow_add' (hv0 x (Ioo_subset_Icc_self hx)) (by linarith : q - 1 + 1 ≠ 0)
        simpa only [sub_add_cancel, Real.rpow_one] using hh
      convert ht using 1
      have hs := heq x hx
      rw [hp]
      rw [show q - 1 - 1 = q - 2 by ring]
      have hdd : ddv x = mu * v x - nu * u x ^ gamma := by linarith
      rw [hdd]; ring
  have hg : 0 ≤ ∫ x in (0 : ℝ)..L, (q - 1) * v x ^ (q - 2) * dv x ^ 2 :=
    intervalIntegral.integral_nonneg hL fun x hx =>
      mul_nonneg (mul_nonneg hp1 (Real.rpow_nonneg (hv0 x hx) _)) (sq_nonneg _)
  rw [intervalIntegral.integral_add (hcg.intervalIntegrable_of_Icc hL)
    (hcf.intervalIntegrable_of_Icc hL),
    intervalIntegral.integral_sub ((hcq.intervalIntegrable_of_Icc hL).const_mul mu)
      (show IntervalIntegrable (fun x => nu * (u x ^ gamma * v x ^ (q - 1))) volume 0 L from ((hcu.mul hc1).intervalIntegrable_of_Icc hL).const_mul nu),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hid
  linarith
/-- Testing the classical positive Neumann signal equation for every `q > 1`.
Strict positivity is the ordinary positive-solution hypothesis, not a testing
or norm inequality. -/
theorem signal_testing_rpow_pos (L mu nu gamma q : ℝ) (u v dv ddv : ℝ → ℝ)
    (hL : 0 ≤ L) (hq : 1 < q) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hvpos : ∀ x ∈ Icc 0 L, 0 < v x)
    (hdv : ContinuousOn dv (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x)
    (hderiv2 : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (heq : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0) :
    mu * (∫ x in (0 : ℝ)..L, v x ^ q) ≤
      nu * ∫ x in (0 : ℝ)..L, u x ^ gamma * v x ^ (q - 1) := by
  have hv0 : ∀ x ∈ Icc 0 L, 0 ≤ v x := fun x hx => (hvpos x hx).le
  have hp1 : 0 ≤ q - 1 := by linarith
  have hc1 := hv.rpow_const (p := q - 1) (fun _ _ => Or.inr hp1)
  have hc2 := hv.rpow_const (p := q - 2) (fun x hx => Or.inl (hvpos x hx).ne')
  have hcq := hv.rpow_const (p := q) (fun _ _ => Or.inr (by linarith : 0 ≤ q))
  have hcu := hu.rpow_const (p := gamma) (fun _ _ => Or.inr hgamma)
  have hcg : ContinuousOn (fun x => (q - 1) * v x ^ (q - 2) * dv x ^ 2) (Icc 0 L) :=
    (hc2.const_smul (q - 1)).mul (hdv.pow 2)
  have hcf : ContinuousOn (fun x => mu * v x ^ q - nu * (u x ^ gamma * v x ^ (q - 1))) (Icc 0 L) :=
    (hcq.const_smul mu).sub ((hcu.mul hc1).const_smul nu)
  have hid : (∫ x in (0 : ℝ)..L,
      ((q - 1) * v x ^ (q - 2) * dv x ^ 2 +
        (mu * v x ^ q - nu * (u x ^ gamma * v x ^ (q - 1))))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL
      (f := fun x => v x ^ (q - 1) * dv x)
      (hc1.mul hdv) (fun x hx => ?_) (show IntervalIntegrable (fun x => (q - 1) * v x ^ (q - 2) * dv x ^ 2 + (mu * v x ^ q - nu * (u x ^ gamma * v x ^ (q - 1)))) volume 0 L from (hcg.add hcf).intervalIntegrable_of_Icc hL)]
    · simp [hbc0, hbcL]
    · have ht := ((hderiv x hx).rpow_const (p := q - 1) (Or.inl (hvpos x (Ioo_subset_Icc_self hx)).ne')).mul (hderiv2 x hx)
      have hp : v x ^ q = v x ^ (q - 1) * v x := by
        have hh := Real.rpow_add' (hv0 x (Ioo_subset_Icc_self hx)) (by linarith : q - 1 + 1 ≠ 0)
        simpa only [sub_add_cancel, Real.rpow_one] using hh
      convert ht using 1
      have hs := heq x hx
      rw [hp]
      rw [show q - 1 - 1 = q - 2 by ring]
      have hdd : ddv x = mu * v x - nu * u x ^ gamma := by linarith
      rw [hdd]; ring
  have hg : 0 ≤ ∫ x in (0 : ℝ)..L, (q - 1) * v x ^ (q - 2) * dv x ^ 2 :=
    intervalIntegral.integral_nonneg hL fun x hx =>
      mul_nonneg (mul_nonneg hp1 (Real.rpow_nonneg (hv0 x hx) _)) (sq_nonneg _)
  rw [intervalIntegral.integral_add (hcg.intervalIntegrable_of_Icc hL)
    (hcf.intervalIntegrable_of_Icc hL),
    intervalIntegral.integral_sub ((hcq.intervalIntegrable_of_Icc hL).const_mul mu)
      (show IntervalIntegrable (fun x => nu * (u x ^ gamma * v x ^ (q - 1))) volume 0 L from ((hcu.mul hc1).intervalIntegrable_of_Icc hL).const_mul nu),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hid
  linarith

/-- Continuous functions on the compact interval belong to every finite or
infinite Lp space for its restricted measure. -/
theorem interval_memLp_of_continuousOn {L : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 L)) (p : ENNReal) :
    MemLp f p (IntervalMoments.intervalMeasure L) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hf.norm
  apply MemLp.of_bound (IntervalMoments.integrable_of_continuousOn hf).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC (mem_image_of_mem (fun x => ‖f x‖) hx)

/-- Hölder's inequality for the actual interval integrals occurring in signal
power testing, without abstract norm inputs. -/
theorem interval_holder_signal (L gamma q : ℝ) (u v : ℝ → ℝ)
    (hL : 0 ≤ L) (hq : 1 < q) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hu0 : ∀ x ∈ Icc 0 L, 0 ≤ u x) (hv0 : ∀ x ∈ Icc 0 L, 0 ≤ v x) :
    (∫ x in (0 : ℝ)..L, u x ^ gamma * v x ^ (q - 1)) ≤
      (∫ x in (0 : ℝ)..L, (u x ^ gamma) ^ q) ^ (1 / q) *
        ((∫ x in (0 : ℝ)..L, v x ^ q) ^ (1 / q)) ^ (q - 1) := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q - 1 := by linarith
  have hcu := hu.rpow_const (p := gamma) (fun _ _ => Or.inr hgamma)
  have hcv := hv.rpow_const (p := q - 1) (fun _ _ => Or.inr hqm.le)
  have hconj : q.HolderConjugate (q / (q - 1)) := Real.HolderConjugate.conjExponent hq
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (f := fun x => u x ^ gamma) (g := fun x => v x ^ (q - 1))
    (μ := IntervalMoments.intervalMeasure L) ?_ ?_
    (interval_memLp_of_continuousOn hcu _) (interval_memLp_of_continuousOn hcv _)
  · simp_rw [IntervalMoments.integral_eq_intervalIntegral hL] at h
    have he : (∫ x in (0 : ℝ)..L, (v x ^ (q - 1)) ^ (q / (q - 1))) =
        ∫ x in (0 : ℝ)..L, v x ^ q := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hL] at hx
      simp only
      rw [← Real.rpow_mul (hv0 x hx)]
      congr 1
      field_simp
    rw [he] at h
    have hint0 : 0 ≤ ∫ x in (0 : ℝ)..L, v x ^ q :=
      intervalIntegral.integral_nonneg hL fun x hx => Real.rpow_nonneg (hv0 x hx) _
    have he2 : (∫ x in (0 : ℝ)..L, v x ^ q) ^ (1 / (q / (q - 1))) =
        ((∫ x in (0 : ℝ)..L, v x ^ q) ^ (1 / q)) ^ (q - 1) := by
      rw [← Real.rpow_mul hint0]
      congr 1
      field_simp
    rwa [he2] at h
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact Real.rpow_nonneg (hu0 x hx) _
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact Real.rpow_nonneg (hv0 x hx) _


/-- The real Lq seminorm equals its interval-integral formula for continuous
functions; this binds the norm to an actual function. -/
theorem lpNorm_interval_eq {L q : ℝ} {f : ℝ → ℝ}
    (hL : 0 ≤ L) (hq : 0 < q) (hf : ContinuousOn f (Icc 0 L)) :
    lpNorm f (ENNReal.ofReal q) (IntervalMoments.intervalMeasure L) =
      (∫ x in (0 : ℝ)..L, |f x| ^ q) ^ (1 / q) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp)
    (IntervalMoments.integrable_of_continuousOn hf).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs, one_div]
  rw [IntervalMoments.integral_eq_intervalIntegral hL]

/-- Actual Minkowski estimate for the signal second derivative, obtained from
its classical equation. There is no assumed norm inequality. -/
theorem signal_minkowski (L mu nu gamma q : ℝ) (u v ddv : ℝ → ℝ)
    (hL : 0 ≤ L) (hq : 1 < q) (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hddv : ContinuousOn ddv (Icc 0 L))
    (heq : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0) :
    (∫ x in (0 : ℝ)..L, |ddv x| ^ q) ^ (1 / q) ≤
      mu * (∫ x in (0 : ℝ)..L, |v x| ^ q) ^ (1 / q) +
      nu * (∫ x in (0 : ℝ)..L, |u x ^ gamma| ^ q) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  have hcu := hu.rpow_const (p := gamma) (fun _ _ => Or.inr hgamma)
  have hae : ddv =ᵐ[IntervalMoments.intervalMeasure L]
      mu • v - nu • (fun x => u x ^ gamma) := by
    change ddv =ᵐ[volume.restrict (Icc 0 L)] _
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [heq x hx]
  have h := lpNorm_sub_le
    ((interval_memLp_of_continuousOn hv (ENNReal.ofReal q)).const_smul mu)
    (g := nu • (fun x => u x ^ gamma))
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ q by linarith))
  have hnorm := congrArg ENNReal.toReal (eLpNorm_congr_ae (p := ENNReal.ofReal q) hae)
  simp only [toReal_eLpNorm] at hnorm
  rw [← hnorm, lpNorm_const_smul, lpNorm_const_smul] at h
  simp only [Real.nnnorm_of_nonneg hmu, Real.nnnorm_of_nonneg hnu] at h
  simpa only [lpNorm_interval_eq hL hq0 hddv, lpNorm_interval_eq hL hq0 hv,
    lpNorm_interval_eq hL hq0 hcu, NNReal.coe_mk] using h

/-- For nonnegative functions the actual integral Lq formula may omit absolute
values. -/
theorem integral_abs_rpow_eq {L q : ℝ} {f : ℝ → ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ Icc 0 L, 0 ≤ f x) :
    (∫ x in (0 : ℝ)..L, |f x| ^ q) = ∫ x in (0 : ℝ)..L, f x ^ q := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hL] at hx
  simp only [abs_of_nonneg (hf x hx)]

/-- The formerly assumed tested-Hölder inequality, proved for an actual
positive classical signal function and its actual Lq integral. -/
theorem signal_tested_holder_pos (L mu nu gamma q : ℝ) (u v dv ddv : ℝ → ℝ)
    (hL : 0 ≤ L) (hq : 1 < q) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hu0 : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hv : ContinuousOn v (Icc 0 L)) (hvpos : ∀ x ∈ Icc 0 L, 0 < v x)
    (hdv : ContinuousOn dv (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x)
    (hderiv2 : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (heq : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0) :
    mu * ((∫ x in (0 : ℝ)..L, |v x| ^ q) ^ (1 / q)) ^ q ≤
      nu * (∫ x in (0 : ℝ)..L, (u x ^ gamma) ^ q) ^ (1 / q) *
        ((∫ x in (0 : ℝ)..L, |v x| ^ q) ^ (1 / q)) ^ (q - 1) := by
  have hv0 : ∀ x ∈ Icc 0 L, 0 ≤ v x := fun x hx => (hvpos x hx).le
  rw [integral_abs_rpow_eq hL hv0]
  have hq0 : 0 < q := by linarith
  have hi : 0 ≤ ∫ x in (0 : ℝ)..L, v x ^ q :=
    intervalIntegral.integral_nonneg hL fun x hx => Real.rpow_nonneg (hv0 x hx) _
  rw [← Real.rpow_mul hi, one_div_mul_cancel hq0.ne', Real.rpow_one]
  have ht := signal_testing_rpow_pos L mu nu gamma q u v dv ddv hL hq hgamma hu hv hvpos
    hdv hderiv hderiv2 heq hbc0 hbcL
  have hh := mul_le_mul_of_nonneg_left
    (interval_holder_signal L gamma q u v hL hq hgamma hu hv hu0 hv0) hnu
  exact ht.trans (by simpa only [mul_assoc] using hh)

/-- Lemma 4.1(3)'s quantitative W2q bound for every given positive classical
signal solution. All three norms are actual integrals. The tested equation,
Hölder and Minkowski inputs of `logistic_W2q_bound` are discharged here;
only the population moment bound remains an explicit upstream input. -/
theorem logistic_W2q_actual (L mu nu gamma alpha uStar q : ℝ)
    (u v dv ddv : ℝ → ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hnu : 0 ≤ nu) (halpha : 0 < alpha)
    (hgamma : 0 < gamma) (huStar : 0 ≤ uStar) (hq : 1 < q)
    (hgq : gamma * q = 1 + alpha)
    (hu : ContinuousOn u (Icc 0 L)) (hu0 : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hv : ContinuousOn v (Icc 0 L)) (hvpos : ∀ x ∈ Icc 0 L, 0 < v x)
    (hdv : ContinuousOn dv (Icc 0 L)) (hddv : ContinuousOn ddv (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x)
    (hderiv2 : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (heq : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha)) :
    (∫ x in (0 : ℝ)..L, |v x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |dv x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |ddv x| ^ q) ^ (1 / q) ≤
      L ^ (1 / q) * uStar ^ gamma * (nu / mu + 2 * nu + 2 * nu * L) := by
  have hv0 : ∀ x ∈ Icc 0 L, 0 ≤ v x := fun x hx => (hvpos x hx).le
  have htest := signal_tested_holder_pos L mu nu gamma q u v dv ddv hL.le hq hnu hgamma.le
    hu hu0 hv hvpos hdv hderiv hderiv2 heq hbc0 hbcL
  have hmink := signal_minkowski L mu nu gamma q u v ddv hL.le hq hmu.le hnu hgamma.le
    hu hv hddv heq
  rw [integral_abs_rpow_eq hL.le
    (fun x hx => Real.rpow_nonneg (hu0 x hx) gamma)] at hmink
  have hgrad := logistic_gradient_le L mu nu gamma alpha uStar u v dv ddv hL hmu.le hnu
    halpha hgamma (by nlinarith) huStar hu hu0 hv hv0 hdv hderiv2 heq hbc0 hbcL hmoment
  exact logistic_W2q_bound L mu nu gamma alpha uStar q _ _ u dv hL hmu hnu huStar hq hgq
    hu0 hdv hmoment hgrad (Real.rpow_nonneg (intervalIntegral.integral_nonneg hL.le
      (fun x _ => Real.rpow_nonneg (abs_nonneg (v x)) q)) _) htest hmink
end ChemotaxisBifurcation.SpikeEstimates
