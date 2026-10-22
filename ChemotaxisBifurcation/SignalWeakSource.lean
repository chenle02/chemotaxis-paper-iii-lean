module
public import ChemotaxisBifurcation.SignalPolynomialTesting

/-!
# Full conjugate-Lq population-source convergence

The actual population power moment supplies uniform Lq control. Polynomial
tests follow from the actual signal equation and constant C1 convergence;
density then yields every conjugate-Lq test on interval Lebesgue measure.
This states tested weak convergence explicitly, without using a nominal
WeakSpace or assuming an extracted weak density.
-/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction
namespace ChemotaxisBifurcation.SignalWeakSource
noncomputable section

/-- Lebesgue measure on the closed interval subtype; endpoints have zero mass. -/
def intervalVolume (L : ℝ) : Measure (Icc (0 : ℝ) L) := Measure.comap Subtype.val volume

instance intervalVolume_finite (L : ℝ) : IsFiniteMeasure (intervalVolume L) := by
  refine ⟨?_⟩
  have hemb := MeasurableEmbedding.subtype_coe (measurableSet_Icc (a := (0 : ℝ)) (b := L))
  rw [intervalVolume, hemb.comap_apply, image_univ, Subtype.range_coe]
  exact measure_Icc_lt_top

/-- The subtype integral is the actual manuscript interval integral. -/
theorem integral_intervalVolume {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℝ) :
    (∫ x : Icc (0 : ℝ) L, f x ∂intervalVolume L) = ∫ x in (0 : ℝ)..L, f x := by
  rw [intervalVolume, integral_subtype_comap measurableSet_Icc,
    intervalIntegral.integral_of_le hL, integral_Icc_eq_integral_Ioc]

theorem continuous_memLp {L : ℝ} {f : Icc (0 : ℝ) L → ℝ}
    (hf : Continuous f) (p : ENNReal) : MemLp f p (intervalVolume L) := by
  let g : Icc (0 : ℝ) L →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩
  apply MemLp.of_bound hf.aestronglyMeasurable ‖g‖
  exact Eventually.of_forall (fun x => g.norm_coe_le_norm x)

/-- A continuous classical interval function as an actual Lp element. -/
def functionToLp {L : ℝ} (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) (p : ENNReal) :
    Lp ℝ p (intervalVolume L) :=
  (continuous_memLp (continuousOn_iff_continuous_domRestrict.mp hf) p).toLp
    ((Icc (0 : ℝ) L).domRestrict f)

theorem coe_functionToLp {L : ℝ} (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) (p : ENNReal) :
    functionToLp f hf p =ᵐ[intervalVolume L] (fun x : Icc (0 : ℝ) L => f x) :=
by
  unfold functionToLp
  exact MemLp.coeFn_toLp _

/-- The Lp representative has precisely the actual integral norm. -/
theorem norm_functionToLp {L q : ℝ} (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L))
    (hL : 0 ≤ L) (hq : 1 ≤ q) :
    ‖functionToLp f hf (ENNReal.ofReal q)‖ =
      (∫ x in (0 : ℝ)..L, |f x| ^ q) ^ (1 / q) := by
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq⟩
  have hq0 : 0 < q := by linarith
  rw [functionToLp, Lp.norm_toLp, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp)
      (continuousOn_iff_continuous_domRestrict.mp hf).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hq0.le, Real.norm_eq_abs, ← one_div, Set.domRestrict_apply]
  rw [integral_intervalVolume hL (fun x => |f x| ^ q)]

/-- Actual interval polynomial tests and a uniform integral Lq bound upgrade
to every conjugate-Lq test; the representatives are bound to real functions. -/
theorem all_conjugate_tests_of_polynomial_interval_tests (L q A c : ℝ) (f : ℕ → ℝ → ℝ)
    (hL : 0 ≤ L) (hq : 1 < q) (hf : ∀ n, ContinuousOn (f n) (Icc 0 L))
    (hbound : ∀ n, (∫ x in (0 : ℝ)..L, |f n x| ^ q) ^ (1 / q) ≤ A)
    (hpoly : ∀ P : Polynomial ℝ,
      Tendsto (fun n => ∫ x in (0 : ℝ)..L, f n x * P.eval x) atTop
        (𝓝 (∫ x in (0 : ℝ)..L, c * P.eval x))) :
    ∀ g : Lp ℝ (ENNReal.ofReal (q / (q - 1))) (intervalVolume L),
      Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, f n x * g x ∂intervalVolume L) atTop
        (𝓝 (∫ x : Icc (0 : ℝ) L, c * g x ∂intervalVolume L)) := by
  have hqm : 0 < q - 1 := by linarith
  have hq' : 1 < q / (q - 1) := (lt_div_iff₀ hqm).mpr (by linarith)
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq.le⟩
  have : Fact (1 ≤ ENNReal.ofReal (q / (q - 1))) :=
    ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq'.le⟩
  have : (ENNReal.ofReal q).HolderConjugate (ENNReal.ofReal (q / (q - 1))) :=
    (Real.HolderConjugate.conjExponent hq).ennrealOfReal
  let F := fun n => functionToLp (f n) (hf n) (ENNReal.ofReal q)
  let Fc := functionToLp (L := L) (fun _ => c) continuousOn_const (ENNReal.ofReal q)
  have hFnorm : ∀ n, ‖F n‖ ≤ A := by
    intro n
    rw [norm_functionToLp _ (hf n) hL hq.le]
    exact hbound n
  have hpairs : ∀ g : Lp ℝ (ENNReal.ofReal (q / (q - 1))) (intervalVolume L),
      Tendsto (fun n => ∫ x, F n x * g x ∂intervalVolume L) atTop
        (𝓝 (∫ x, Fc x * g x ∂intervalVolume L)) := by
    apply SignalWeakTesting.all_Lp_tests_of_polynomial_tests (intervalVolume L)
      (ENNReal.ofReal q) (ENNReal.ofReal (q / (q - 1))) (by simp) F Fc A hFnorm
    intro P
    have heqf : ∀ n, (∫ x, F n x * P.eval (x : ℝ) ∂intervalVolume L) =
        ∫ x in (0 : ℝ)..L, f n x * P.eval x := by
      intro n
      rw [← integral_intervalVolume hL]
      apply integral_congr_ae
      filter_upwards [coe_functionToLp (f n) (hf n) (ENNReal.ofReal q)] with x hx
      rw [hx]
    have heqc : (∫ x, Fc x * P.eval (x : ℝ) ∂intervalVolume L) =
        ∫ x in (0 : ℝ)..L, c * P.eval x := by
      rw [← integral_intervalVolume hL]
      apply integral_congr_ae
      filter_upwards [coe_functionToLp (L := L) (fun _ => c) continuousOn_const (ENNReal.ofReal q)] with x hx
      rw [hx]
    simp_rw [heqf, heqc]
    exact hpoly P
  intro g
  have heqf : ∀ n, (∫ x, F n x * g x ∂intervalVolume L) =
      ∫ x : Icc (0 : ℝ) L, f n x * g x ∂intervalVolume L := by
    intro n
    apply integral_congr_ae
    filter_upwards [coe_functionToLp (f n) (hf n) (ENNReal.ofReal q)] with x hx
    rw [hx]
  have heqc : (∫ x, Fc x * g x ∂intervalVolume L) =
      ∫ x : Icc (0 : ℝ) L, c * g x ∂intervalVolume L := by
    apply integral_congr_ae
    filter_upwards [coe_functionToLp (L := L) (fun _ => c) continuousOn_const (ENNReal.ofReal q)] with x hx
    rw [hx]
  simpa only [heqf, heqc] using hpairs g

/-- Actual uniform convergence and a uniform integral Lq bound imply all
conjugate-Lq tests. -/
theorem all_conjugate_tests_of_uniform_limit (L q A c : ℝ) (f : ℕ → ℝ → ℝ)
    (hL : 0 ≤ L) (hq : 1 < q) (hf : ∀ n, ContinuousOn (f n) (Icc 0 L))
    (hbound : ∀ n, (∫ x in (0 : ℝ)..L, |f n x| ^ q) ^ (1 / q) ≤ A)
    (hlim : TendstoUniformlyOn f (fun _ => c) atTop (Icc 0 L)) :
    ∀ g : Lp ℝ (ENNReal.ofReal (q / (q - 1))) (intervalVolume L),
      Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, f n x * g x ∂intervalVolume L) atTop
        (𝓝 (∫ x : Icc (0 : ℝ) L, c * g x ∂intervalVolume L)) := by
  apply all_conjugate_tests_of_polynomial_interval_tests L q A c f hL hq hf hbound
  intro P
  have hp := SignalPolynomialTesting.uniform_mul_fixed hL P.continuous.continuousOn hlim
  rw [← uIcc_of_le hL] at hp
  exact hp.tendsto_intervalIntegral_of_continuousOn (μ := volume)
    (Eventually.of_forall fun n => by
      rw [uIcc_of_le hL]
      exact (hf n).mul P.continuous.continuousOn)

/-- Full conjugate-Lq testing of the population source, with q=r/gamma>1,
from actual classical signal equations and constant C1 signal convergence.
Every test element of L^(q/(q-1)) is admitted; this is stronger than only
continuous, polynomial or interval testing. -/
theorem all_conjugate_tests_of_constant_C1_signal (L mu nu gamma r R c : ℝ)
    (u v dv ddv : ℕ → ℝ → ℝ)
    (hL : 0 < L) (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hgamma : 0 < gamma)
    (_hr : 1 < r) (hgamma_r : gamma < r) (_hR : 0 ≤ R)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hu0 : ∀ n x, x ∈ Icc 0 L → 0 ≤ u n x)
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (heq : ∀ n x, x ∈ Ioo 0 L → ddv n x - mu * v n x + nu * u n x ^ gamma = 0)
    (hbc0 : ∀ n, dv n 0 = 0) (hbcL : ∀ n, dv n L = 0)
    (hmoment : ∀ n, ∫ x in (0 : ℝ)..L, u n x ^ r ≤ R)
    (hvlim : TendstoUniformlyOn v (fun _ => nu / mu * c) atTop (Icc 0 L))
    (hdvlim : TendstoUniformlyOn dv (fun _ => 0) atTop (Icc 0 L)) :
    ∀ g : Lp ℝ (ENNReal.ofReal ((r / gamma) / (r / gamma - 1))) (intervalVolume L),
      Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, u n x ^ gamma * g x ∂intervalVolume L) atTop
        (𝓝 (∫ x : Icc (0 : ℝ) L, c * g x ∂intervalVolume L)) := by

  let q : ℝ := r / gamma
  have hq : 1 < q := (lt_div_iff₀ hgamma).mpr (by simpa using hgamma_r)
  have hq0 : 0 < q := by linarith
  have hcu : ∀ n, ContinuousOn (fun x => u n x ^ gamma) (Icc 0 L) :=
    fun n => (hu n).rpow_const (fun _ _ => Or.inr hgamma.le)
  have hexp : gamma * q = r := by dsimp [q]; field_simp
  have hbound : ∀ n, (∫ x in (0 : ℝ)..L, |u n x ^ gamma| ^ q) ^ (1 / q) ≤ R ^ (1 / q) := by
    intro n
    have hi : (∫ x in (0 : ℝ)..L, |u n x ^ gamma| ^ q) = ∫ x in (0 : ℝ)..L, u n x ^ r := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hL.le] at hx
      simp only
      rw [abs_of_nonneg (Real.rpow_nonneg (hu0 n x hx) gamma),
        ← Real.rpow_mul (hu0 n x hx), hexp]
    rw [hi]
    exact Real.rpow_le_rpow
      (intervalIntegral.integral_nonneg hL.le (fun x hx => Real.rpow_nonneg (hu0 n x hx) r))
      (hmoment n) (by positivity)
  exact all_conjugate_tests_of_polynomial_interval_tests L q (R ^ (1 / q)) c
    (fun n x => u n x ^ gamma) hL.le hq hcu hbound
    (SignalPolynomialTesting.polynomial_source_test_tendsto L mu nu gamma c
      u v dv ddv hL.le hnu hgamma.le hu hv hdv hderiv2 heq hbc0 hbcL hvlim hdvlim hmu)
end
end ChemotaxisBifurcation.SignalWeakSource
