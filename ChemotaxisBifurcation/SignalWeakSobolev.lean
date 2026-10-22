module
public import ChemotaxisBifurcation.SignalWeakSource

/-!
# Componentwise weak-W2q signal tests

All three actual classical signal components converge against every
conjugate-Lq test. The second-derivative limit follows from the literal
signal equation and the full source-tested limit, not just the C1 topology.
-/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace ChemotaxisBifurcation.SignalWeakSobolev
noncomputable section
open SignalWeakSource

/-- Continuity extends the actual classical signal equation to the endpoints. -/
theorem signal_eq_on_Icc {L mu nu gamma : ℝ} {u v ddv : ℝ → ℝ}
    (hL : 0 < L) (hgamma : 0 ≤ gamma)
    (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hddv : ContinuousOn ddv (Icc 0 L))
    (heq : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0) :
    ∀ x ∈ Icc 0 L, ddv x = mu * v x - nu * u x ^ gamma := by
  have hcu := hu.rpow_const (p := gamma) (fun _ _ => Or.inr hgamma)
  have h : EqOn ddv (fun x => mu * v x - nu * u x ^ gamma) (Ioo 0 L) := by
    intro x hx
    linarith [heq x hx]
  exact h.of_subset_closure hddv ((hv.const_smul mu).sub (hcu.const_smul nu))
    Ioo_subset_Icc_self (by rw [closure_Ioo hL.ne])

/-- Full conjugate-Lq testing of all three signal components and the source.
The signal conclusion spells out componentwise weak-W2q convergence rather
than relabeling uniform C1 convergence as a stronger topology. -/
theorem all_components_test_tendsto (L mu nu gamma r R c : ℝ)
    (u v dv ddv : ℕ → ℝ → ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hnu : 0 < nu) (hgamma : 0 < gamma)
    (hr : 1 < r) (hgamma_r : gamma < r) (hR : 0 ≤ R)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hu0 : ∀ n x, x ∈ Icc 0 L → 0 ≤ u n x)
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hvpos : ∀ n x, x ∈ Icc 0 L → 0 < v n x)
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hddv : ∀ n, ContinuousOn (ddv n) (Icc 0 L))
    (hderiv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x)
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (heq : ∀ n x, x ∈ Ioo 0 L → ddv n x - mu * v n x + nu * u n x ^ gamma = 0)
    (hbc0 : ∀ n, dv n 0 = 0) (hbcL : ∀ n, dv n L = 0)
    (hmoment : ∀ n, ∫ x in (0 : ℝ)..L, u n x ^ r ≤ R)
    (hvlim : TendstoUniformlyOn v (fun _ => nu / mu * c) atTop (Icc 0 L))
    (hdvlim : TendstoUniformlyOn dv (fun _ => 0) atTop (Icc 0 L)) :
    ∀ g : Lp ℝ (ENNReal.ofReal ((r / gamma) / (r / gamma - 1))) (intervalVolume L),
      Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, u n x ^ gamma * g x ∂intervalVolume L) atTop
        (𝓝 (∫ x : Icc (0 : ℝ) L, c * g x ∂intervalVolume L)) ∧
      Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, v n x * g x ∂intervalVolume L) atTop
        (𝓝 (∫ x : Icc (0 : ℝ) L, (nu / mu * c) * g x ∂intervalVolume L)) ∧
      Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, dv n x * g x ∂intervalVolume L) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, ddv n x * g x ∂intervalVolume L) atTop (𝓝 0) := by
  let q : ℝ := r / gamma
  have hq : 1 < q := (lt_div_iff₀ hgamma).mpr (by simpa using hgamma_r)
  let B := L ^ (1 / q) * SignalPowerMoment.momentScale L R r ^ gamma *
    (nu / mu + 2 * nu + 2 * nu * L)
  have hsum : ∀ n,
      (∫ x in (0 : ℝ)..L, |v n x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |dv n x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |ddv n x| ^ q) ^ (1 / q) ≤ B := by
    intro n
    exact SignalPowerMoment.W2q_bound_of_power_moment L mu nu gamma r R (u n) (v n) (dv n) (ddv n)
      hL hmu hnu.le hgamma hr hgamma_r hR (hu n) (hu0 n) (hv n) (hvpos n) (hdv n)
      (hddv n) (hderiv n) (hderiv2 n) (heq n) (hbc0 n) (hbcL n) (hmoment n)
  have hnorm0 : ∀ f : ℝ → ℝ, 0 ≤ (∫ x in (0 : ℝ)..L, |f x| ^ q) ^ (1 / q) :=
    fun f => Real.rpow_nonneg (intervalIntegral.integral_nonneg hL.le
      (fun x _ => Real.rpow_nonneg (abs_nonneg (f x)) q)) _
  have hVbound : ∀ n, (∫ x in (0 : ℝ)..L, |v n x| ^ q) ^ (1 / q) ≤ B := by
    intro n
    linarith [hsum n, hnorm0 (dv n), hnorm0 (ddv n)]
  have hDVbound : ∀ n, (∫ x in (0 : ℝ)..L, |dv n x| ^ q) ^ (1 / q) ≤ B := by
    intro n
    linarith [hsum n, hnorm0 (v n), hnorm0 (ddv n)]
  have hweakU := all_conjugate_tests_of_constant_C1_signal L mu nu gamma r R c u v dv ddv
    hL hmu.ne' hnu.ne' hgamma hr hgamma_r hR hu hu0 hv hdv hderiv2 heq hbc0 hbcL hmoment hvlim hdvlim
  have hweakV := all_conjugate_tests_of_uniform_limit L q B (nu / mu * c) v hL.le hq hv hVbound hvlim
  have hweakDV := all_conjugate_tests_of_uniform_limit L q B 0 dv hL.le hq hdv hDVbound hdvlim
  have hqm : 0 < q - 1 := by linarith
  have hq' : 1 < q / (q - 1) := (lt_div_iff₀ hqm).mpr (by linarith)
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq.le⟩
  have : Fact (1 ≤ ENNReal.ofReal (q / (q - 1))) :=
    ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq'.le⟩
  have : (ENNReal.ofReal q).HolderConjugate (ENNReal.ofReal (q / (q - 1))) :=
    (Real.HolderConjugate.conjExponent hq).ennrealOfReal
  intro g
  refine ⟨hweakU g, hweakV g, ?_, ?_⟩
  · simpa only [zero_mul, integral_zero] using hweakDV g
  · have hEqInt : ∀ n,
        (∫ x : Icc (0 : ℝ) L, ddv n x * g x ∂intervalVolume L) =
        mu * (∫ x : Icc (0 : ℝ) L, v n x * g x ∂intervalVolume L) -
        nu * (∫ x : Icc (0 : ℝ) L, u n x ^ gamma * g x ∂intervalVolume L) := by
      intro n
      have hVlp := continuous_memLp (continuousOn_iff_continuous_domRestrict.mp (hv n)) (ENNReal.ofReal q)
      have hUlp := continuous_memLp (continuousOn_iff_continuous_domRestrict.mp
        ((hu n).rpow_const (p := gamma) (fun _ _ => Or.inr hgamma.le))) (ENNReal.ofReal q)
      have hVint : Integrable (fun x : Icc (0 : ℝ) L => v n x * g x) (intervalVolume L) := by
        exact (hVlp.integrable_mul (Lp.memLp g)).congr (Eventually.of_forall fun _ => rfl)
      have hUint : Integrable (fun x : Icc (0 : ℝ) L => u n x ^ gamma * g x) (intervalVolume L) := by
        exact (hUlp.integrable_mul (Lp.memLp g)).congr (Eventually.of_forall fun _ => rfl)
      have hUV := signal_eq_on_Icc hL hgamma.le (hu n) (hv n) (hddv n) (heq n)
      calc (∫ x : Icc (0 : ℝ) L, ddv n x * g x ∂intervalVolume L) =
          ∫ x : Icc (0 : ℝ) L, mu * (v n x * g x) - nu * (u n x ^ gamma * g x) ∂intervalVolume L := by
            apply integral_congr_ae
            exact Eventually.of_forall fun x => by
              simp only
              rw [hUV x x.property]
              ring
        _ = _ := by
          rw [integral_sub (hVint.const_mul mu) (hUint.const_mul nu), integral_const_mul, integral_const_mul]
    have hlim := ((hweakV g).const_mul mu).sub ((hweakU g).const_mul nu)
    have htarget : mu * (∫ x : Icc (0 : ℝ) L, (nu / mu * c) * g x ∂intervalVolume L) -
        nu * (∫ x : Icc (0 : ℝ) L, c * g x ∂intervalVolume L) = 0 := by
      rw [integral_const_mul, integral_const_mul]
      field_simp
      ring
    rw [htarget] at hlim
    simpa only [hEqInt] using hlim
end
end ChemotaxisBifurcation.SignalWeakSobolev
