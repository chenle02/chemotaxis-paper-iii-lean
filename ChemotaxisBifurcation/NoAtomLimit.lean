module
public import ChemotaxisBifurcation.NoDiracMass
public import ChemotaxisBifurcation.IntervalConcentration

@[expose] public section

/-!
# Weak limits of the densities carry no atoms (Remark 1.3(2), `R:spike-solution-rk`)

Remark 1.3(2) (TeX lines 1004–1019) states that, in the non-minimal model, the
spikes of Theorem 1.4 (`T:spiky-solu-thm`, TeX line 962) cannot carry a Dirac
mass. `NoDiracMass.window_mass_tendstoUniformly` proves the remark's display:
the mass of `u_n` in `(x*-δ, x*+δ) ∩ (0,L)` tends to zero as `δ → 0+`,
uniformly in `n` and `x*`. This file draws the measure-level conclusion.

* `measure_singleton_eq_zero_of_small_balls`: on a pseudo-metric space, if
  `μ_i → μ` weakly along a nontrivial filter and the `μ_i`-mass of small balls
  around `x` is eventually small, then `μ {x} = 0`. The proof tests the weak
  convergence against a thickened indicator of `{x}`, which is the open-set
  lower bound of the Portmanteau theorem specialised to a ball.
* `densityFiniteMeasure_singleton_eq_zero`: every weak limit of the finite
  measures `u_n(x) dx` on `[0,L]` has no atoms.
* `not_tendsto_smul_dirac` and `not_subseq_tendsto_smul_dirac`: no family,
  and in particular no subsequence, of the measures `u_n(x) dx` converges to
  `c δ_{x*}` with `c > 0`.

The PDE inputs (continuity, positivity, nonconstancy and the logistic mass
identity of each `u_n`) remain hypotheses, exactly as in `NoDiracMass`.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.NoAtomLimit

open MeasureTheory Set Filter
open ChemotaxisBifurcation.EndpointConcentration ChemotaxisBifurcation.IntervalConcentration
  ChemotaxisBifurcation.NoDiracMass
open scoped ENNReal NNReal Topology BoundedContinuousFunction

/-- **Abstract no-atom criterion.** On a pseudo-metric space, let `μ_i → μ`
weakly along a nontrivial filter. If for every `ε > 0` some ball around `x`
eventually has `μ_i`-mass at most `ε`, then `μ {x} = 0`. This is the open-set
Portmanteau bound `μ(B) ≤ liminf μ_i(B)` applied to small balls `B`
(Remark 1.3(2), TeX lines 1005–1019). -/
theorem measure_singleton_eq_zero_of_small_balls
    {X ι : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {l : Filter ι} [l.NeBot] {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    (hlim : Tendsto μs l (𝓝 μ)) (x : X)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 0 < r ∧ ∀ᶠ i in l, (μs i : Measure X) (Metric.ball x r) ≤ ENNReal.ofReal ε) :
    (μ : Measure X) {x} = 0 := by
  have hle : ∀ ε : ℝ, 0 < ε → (μ : Measure X) {x} ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨r, hr, hball⟩ := hsmall ε hε
    set f : X →ᵇ ℝ≥0 := thickenedIndicator hr ({x} : Set X)
    have hconv := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp hlim f
    -- the indicator of `{x}` lies below `f`
    have hlow : (μ : Measure X) {x} ≤ ∫⁻ y, (f y : ℝ≥0∞) ∂(μ : Measure X) := by
      refine (measure_mono subset_closure).trans ?_
      rw [← lintegral_indicator_one isClosed_closure.measurableSet]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ closure ({x} : Set X)
      · rw [indicator_of_mem hy, Pi.one_apply, thickenedIndicator_one_of_mem_closure hr _ hy,
          ENNReal.coe_one]
      · rw [indicator_of_notMem hy]
        exact bot_le
    -- `f` lies below the indicator of the ball
    have hup : ∀ i,
        ∫⁻ y, (f y : ℝ≥0∞) ∂(μs i : Measure X) ≤ (μs i : Measure X) (Metric.ball x r) := by
      intro i
      rw [← lintegral_indicator_one Metric.isOpen_ball.measurableSet]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ Metric.ball x r
      · rw [indicator_of_mem hy, Pi.one_apply, ← ENNReal.coe_one, ENNReal.coe_le_coe]
        exact thickenedIndicator_le_one hr _ y
      · rw [indicator_of_notMem hy, thickenedIndicator_zero hr _
          (by rwa [Metric.thickening_singleton]), ENNReal.coe_zero]
    refine hlow.trans (le_of_tendsto hconv ?_)
    filter_upwards [hball] with i hi
    exact (hup i).trans hi
  have hlim0 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [ENNReal.ofReal_zero] at h
  exact le_antisymm (ge_of_tendsto hlim0 (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε))
    bot_le

/-- On the interval subtype `[0,L]`, the ball of radius `δ` around `x` is the
preimage of `(x-δ, x+δ)`. -/
theorem ball_eq_preimage (L : ℝ) (x : ClosedInterval L) (δ : ℝ) :
    Metric.ball x δ = Subtype.val ⁻¹' Ioo ((x : ℝ) - δ) ((x : ℝ) + δ) := by
  ext y
  simp only [Metric.mem_ball, Subtype.dist_eq, mem_preimage, ← Real.ball_eq_Ioo]

/-- The `u(x) dx`-mass of the ball of radius `δ` around `x ∈ [0,L]` is the
manuscript's window integral `∫_{(x-δ,x+δ)∩(0,L)} u` (TeX lines 1014–1016). -/
theorem densityFiniteMeasure_ball (L : ℝ) (hL : 0 ≤ L) (u : ℝ → ℝ)
    (hcont : ContinuousOn u (Icc 0 L)) (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (x : ClosedInterval L) (δ : ℝ) :
    ((densityFiniteMeasure L u hL hcont hnonneg : FiniteMeasure (ClosedInterval L)) :
        Measure (ClosedInterval L)) (Metric.ball x δ) =
      ENNReal.ofReal (∫ y in window L x δ, u y) := by
  rw [ball_eq_preimage]
  change densityMeasure L u _ = _
  rw [densityMeasure_preimage hcont hnonneg measurableSet_Ioo, window]
  congr 1
  exact setIntegral_congr_set (ae_eq_set_inter (ae_eq_refl _) Ioo_ae_eq_Icc.symm)

/-- **Remark 1.3(2), the conclusion as a measure statement.** Let `u_i`
(common `a, b, α > 0`, `L > 0`) be continuous, positive, nonconstant
densities satisfying the logistic mass identity
`a ∫_0^L u_i = b ∫_0^L u_i^(1+α)`. If the finite measures `u_i(x) dx` on
`[0,L]` converge weakly along a nontrivial filter to a finite measure `μ`,
then `μ` has no atoms: `μ {x} = 0` for every `x ∈ [0,L]`
(TeX lines 1004–1019). -/
theorem densityFiniteMeasure_singleton_eq_zero
    (a b alpha L : ℝ) {ι : Type*} (u : ι → ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ∀ i, ContinuousOn (u i) (Icc 0 L)) (hpos : ∀ i, ∀ x ∈ Icc 0 L, 0 < u i x)
    (hnonconst : ∀ i, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u i x ≠ u i y)
    (hmass : ∀ i,
      a * ∫ x in (0 : ℝ)..L, u i x = b * ∫ x in (0 : ℝ)..L, u i x ^ (1 + alpha))
    {l : Filter ι} [l.NeBot] {μ : FiniteMeasure (ClosedInterval L)}
    (hlim : Tendsto (fun i => densityFiniteMeasure L (u i) hL.le (hcont i)
      (fun x hx => (hpos i x hx).le)) l (𝓝 μ))
    (x : ClosedInterval L) :
    (μ : Measure (ClosedInterval L)) {x} = 0 := by
  refine measure_singleton_eq_zero_of_small_balls hlim x fun ε hε => ?_
  have hunif := window_mass_tendstoUniformly a b alpha L u ha hb halpha hL hcont hpos
    hnonconst hmass
  rw [Metric.tendstoUniformly_iff] at hunif
  obtain ⟨δ, hδε, hδ⟩ := ((hunif ε hε).and self_mem_nhdsWithin).exists
  refine ⟨δ, hδ, Eventually.of_forall fun i => ?_⟩
  rw [densityFiniteMeasure_ball]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := hδε (i, (x : ℝ))
  rw [Real.dist_eq, zero_sub, abs_neg] at h
  exact (le_abs_self _).trans h.le

/-- `c δ_{x*}` with `c > 0` gives positive mass `c` to `{x*}`. -/
theorem smul_dirac_singleton (L : ℝ) (c : ℝ≥0) (xstar : ClosedInterval L) :
    ((c • (diracProba xstar).toFiniteMeasure : FiniteMeasure (ClosedInterval L)) :
        Measure (ClosedInterval L)) {xstar} = c := by
  rw [FiniteMeasure.toMeasure_smul]
  change (c • Measure.dirac xstar) {xstar} = (c : ℝ≥0∞)
  rw [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton xstar), ENNReal.smul_def,
    smul_eq_mul, mul_one]

/-- **Remark 1.3(2): spikes cannot carry a Dirac mass.** Under the hypotheses
of `densityFiniteMeasure_singleton_eq_zero`, the measures `u_i(x) dx` do not
converge weakly, along any nontrivial filter, to `c δ_{x*}` with `c > 0` and
`x* ∈ [0,L]` (TeX lines 1005–1006). -/
theorem not_tendsto_smul_dirac
    (a b alpha L : ℝ) {ι : Type*} (u : ι → ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ∀ i, ContinuousOn (u i) (Icc 0 L)) (hpos : ∀ i, ∀ x ∈ Icc 0 L, 0 < u i x)
    (hnonconst : ∀ i, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u i x ≠ u i y)
    (hmass : ∀ i,
      a * ∫ x in (0 : ℝ)..L, u i x = b * ∫ x in (0 : ℝ)..L, u i x ^ (1 + alpha))
    (l : Filter ι) [l.NeBot] (c : ℝ≥0) (hc : 0 < c) (xstar : ClosedInterval L) :
    ¬ Tendsto (fun i => densityFiniteMeasure L (u i) hL.le (hcont i)
      (fun x hx => (hpos i x hx).le)) l (𝓝 (c • (diracProba xstar).toFiniteMeasure)) := by
  intro hlim
  have h0 := densityFiniteMeasure_singleton_eq_zero a b alpha L u ha hb halpha hL hcont hpos
    hnonconst hmass hlim xstar
  rw [smul_dirac_singleton, ENNReal.coe_eq_zero] at h0
  exact hc.ne' h0

/-- **Remark 1.3(2), in the manuscript's words.** For a sequence `u_n` as in
`densityFiniteMeasure_singleton_eq_zero`, no subsequence `u_{φ(k)}(x) dx`
converges weakly to `c δ_{x*}` with `c > 0` and `x* ∈ [0,L]`
(TeX lines 1005–1006). -/
theorem not_subseq_tendsto_smul_dirac
    (a b alpha L : ℝ) (u : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hpos : ∀ n, ∀ x ∈ Icc 0 L, 0 < u n x)
    (hnonconst : ∀ n, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u n x ≠ u n y)
    (hmass : ∀ n,
      a * ∫ x in (0 : ℝ)..L, u n x = b * ∫ x in (0 : ℝ)..L, u n x ^ (1 + alpha))
    (φ : ℕ → ℕ) (c : ℝ≥0) (hc : 0 < c) (xstar : ClosedInterval L) :
    ¬ Tendsto (fun k => densityFiniteMeasure L (u (φ k)) hL.le (hcont (φ k))
      (fun x hx => (hpos (φ k) x hx).le)) atTop
        (𝓝 (c • (diracProba xstar).toFiniteMeasure)) :=
  not_tendsto_smul_dirac a b alpha L (fun k => u (φ k)) ha hb halpha hL (fun k => hcont (φ k))
    (fun k => hpos (φ k)) (fun k => hnonconst (φ k)) (fun k => hmass (φ k)) atTop c hc xstar

end ChemotaxisBifurcation.NoAtomLimit
