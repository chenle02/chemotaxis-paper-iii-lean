module
public import ChemotaxisBifurcation.EndpointConcentration
public import ChemotaxisBifurcation.IntervalMoments

@[expose] public section

/-!
# Endpoint concentration of interval densities (Theorem 1.3(3))

`EndpointConcentration` proves that finite measures on `[0,L]` with a fixed
positive mass and vanishing mass outside every neighborhood of an endpoint
converge weakly to a multiple of the Dirac mass there. This file supplies the
application inputs for Theorem 1.3(3), label `T:global-extension`, TeX lines
3336–3393:

* the finite Borel measures `u_j(x) dx` on the interval subtype `[0,L]`,
  built from continuous densities that are nonnegative on `[0,L]`;
* their common mass `L u*` from the prescribed mass `∫_0^L u_j = L u*`;
* the tail premise for every relatively open neighborhood of an endpoint,
  derived from the interval tails `∫_δ^L u_j → 0` (left endpoint) or
  `∫_0^δ u_j → 0` (right endpoint, the reflected branch);
* the monotone tail step `∫_δ^L u_j ≤ (L - δ) u_j(δ)` for decreasing `u_j`;
* `∫_0^L f u_j → L u* f(0)` for every `f ∈ C([0,L])`, and `max u_j → ∞`.

The pointwise decay `u_j(δ) → 0` (the sine-test argument, TeX lines
3349–3379), the monotonicity of the solutions, their fixed mass and their
continuity are the PDE inputs and stay hypotheses.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.IntervalConcentration

open MeasureTheory Set Filter
open ChemotaxisBifurcation.EndpointConcentration ChemotaxisBifurcation.IntervalMoments
open scoped ENNReal NNReal Topology BoundedContinuousFunction

/-- The measure `u(x) dx` on `ℝ`, carried by `[0,L]`. -/
noncomputable def densityOnReal (L : ℝ) (u : ℝ → ℝ) : Measure ℝ :=
  (intervalMeasure L).withDensity fun x => ENNReal.ofReal (u x)

/-- The measure `u(x) dx` on the interval subtype `[0,L]`. -/
noncomputable def densityMeasure (L : ℝ) (u : ℝ → ℝ) : Measure (ClosedInterval L) :=
  Measure.comap Subtype.val (densityOnReal L u)

theorem val_measurableEmbedding (L : ℝ) :
    MeasurableEmbedding (Subtype.val : ClosedInterval L → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Icc

section Construction

variable {L : ℝ} {u : ℝ → ℝ}

theorem densityOnReal_apply (hcont : ContinuousOn u (Icc 0 L))
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x) {S : Set ℝ} (hS : MeasurableSet S) :
    densityOnReal L u S = ENNReal.ofReal (∫ x in S ∩ Icc 0 L, u x) := by
  rw [densityOnReal, withDensity_apply _ hS, Measure.restrict_restrict hS,
    ofReal_integral_eq_lintegral_ofReal]
  · exact hcont.integrableOn_Icc.mono_set inter_subset_right
  · exact ae_restrict_of_forall_mem (hS.inter measurableSet_Icc) fun x hx => hnonneg x hx.2

/-- The mass that `u(x) dx` gives to `{x ∈ [0,L] : x ∈ S}`. -/
theorem densityMeasure_preimage (hcont : ContinuousOn u (Icc 0 L))
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x) {S : Set ℝ} (hS : MeasurableSet S) :
    densityMeasure L u (Subtype.val ⁻¹' S) = ENNReal.ofReal (∫ x in S ∩ Icc 0 L, u x) := by
  rw [densityMeasure, (val_measurableEmbedding L).comap_apply, image_preimage_eq_inter_range,
    Subtype.range_coe, densityOnReal_apply hcont hnonneg (hS.inter measurableSet_Icc),
    inter_assoc, inter_self]

theorem densityMeasure_univ (hL : 0 ≤ L) (hcont : ContinuousOn u (Icc 0 L))
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x) :
    densityMeasure L u univ = ENNReal.ofReal (∫ x in (0 : ℝ)..L, u x) := by
  have h := densityMeasure_preimage hcont hnonneg MeasurableSet.univ
  rw [preimage_univ, univ_inter] at h
  rw [h, ← integral_eq_intervalIntegral hL]

theorem densityMeasure_isFinite (hL : 0 ≤ L) (hcont : ContinuousOn u (Icc 0 L))
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x) : IsFiniteMeasure (densityMeasure L u) :=
  ⟨by rw [densityMeasure_univ hL hcont hnonneg]; exact ENNReal.ofReal_lt_top⟩

/-- `u(x) dx` as a finite measure on `[0,L]`. -/
noncomputable def densityFiniteMeasure (L : ℝ) (u : ℝ → ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn u (Icc 0 L)) (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x) :
    FiniteMeasure (ClosedInterval L) :=
  ⟨densityMeasure L u, densityMeasure_isFinite hL hcont hnonneg⟩

/-- The mass of `u(x) dx` is `∫_0^L u`, so the prescribed mass `L u*` gives
total mass `L u*`. -/
theorem densityFiniteMeasure_mass (hL : 0 ≤ L) (hcont : ContinuousOn u (Icc 0 L))
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x) :
    (densityFiniteMeasure L u hL hcont hnonneg).mass =
      (∫ x in (0 : ℝ)..L, u x).toNNReal := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  exact densityMeasure_univ hL hcont hnonneg

/-- Integrals against `u(x) dx` are the manuscript's `∫_0^L f u`. -/
theorem integral_densityMeasure (hL : 0 ≤ L) (hcont : ContinuousOn u (Icc 0 L))
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x) (f : ℝ → ℝ) :
    ∫ x, f x.val ∂densityMeasure L u = ∫ x in (0 : ℝ)..L, f x * u x := by
  have hemb := val_measurableEmbedding L
  rw [← hemb.integral_map, densityMeasure, hemb.map_comap, Subtype.range_coe, densityOnReal,
    restrict_withDensity measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_self, integral_withDensity_eq_integral_toReal_smul₀
      ((hcont.aemeasurable measurableSet_Icc).ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← integral_eq_intervalIntegral hL]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp [ENNReal.toReal_ofReal (hnonneg x hx), mul_comm]

end Construction

section Neighborhoods

variable {L : ℝ}

/-- Every relatively open neighborhood of `0` in `[0,L]` contains an initial
interval `[0,δ)`, `0 < δ < L`. -/
theorem compl_subset_of_left (hL : 0 < L) {U : Set (ClosedInterval L)} (hU : IsOpen U)
    (h0 : leftEndpoint L hL.le ∈ U) :
    ∃ δ ∈ Ioo 0 L, Uᶜ ⊆ Subtype.val ⁻¹' Ici δ := by
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  have hV0 : (0 : ℝ) ∈ V := h0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 hV0
  refine ⟨min (ε / 2) (L / 2), ⟨by positivity, (min_le_right _ _).trans_lt (half_lt_self hL)⟩, ?_⟩
  intro x hx
  simp only [mem_preimage, mem_Ici]
  by_contra hlt
  rw [not_le] at hlt
  apply hx
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg x.2.1]
  linarith [min_le_left (ε / 2) (L / 2)]

/-- Every relatively open neighborhood of `L` in `[0,L]` contains a final
interval `(δ,L]`, `0 < δ < L`. -/
theorem compl_subset_of_right (hL : 0 < L) {U : Set (ClosedInterval L)} (hU : IsOpen U)
    (hLmem : rightEndpoint L hL.le ∈ U) :
    ∃ δ ∈ Ioo 0 L, Uᶜ ⊆ Subtype.val ⁻¹' Iic δ := by
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  have hVL : L ∈ V := hLmem
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV L hVL
  refine ⟨max (L - ε / 2) (L / 2), ⟨lt_max_of_lt_right (by positivity),
    max_lt (by linarith) (half_lt_self hL)⟩, ?_⟩
  intro x hx
  simp only [mem_preimage, mem_Iic]
  by_contra hlt
  rw [not_le] at hlt
  apply hx
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [x.2.2])]
  linarith [le_max_left (L - ε / 2) (L / 2)]

/-- A finite-measure version of squeezing: domination by real numbers tending
to `0` makes the measures of a set tend to `0`. -/
theorem tendsto_apply_of_le {X : Type*} [MeasurableSpace X] {μ : ℕ → FiniteMeasure X}
    {s : Set X} {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0))
    (hle : ∀ n, (μ n : Measure X) s ≤ ENNReal.ofReal (t n)) :
    Tendsto (fun n => μ n s) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => (t n).toNNReal) atTop (𝓝 0) := by
    have h := (continuous_real_toNNReal.tendsto 0).comp ht
    rw [Real.toNNReal_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun n => by simp) (fun n => ?_)
  have h := hle n
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  exact ENNReal.coe_le_coe.mp h

end Neighborhoods

section Concentration

variable {L : ℝ}

theorem interval_tail_eq {u : ℝ → ℝ} (hcont : ContinuousOn u (Icc 0 L))
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x) {δ : ℝ} (hδ : δ ∈ Ioo 0 L) :
    densityMeasure L u (Subtype.val ⁻¹' Ici δ) = ENNReal.ofReal (∫ x in δ..L, u x) := by
  have hset : Ici δ ∩ Icc 0 L = Icc δ L := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hδ.1.le.trans h1, h2⟩
  rw [densityMeasure_preimage hcont hnonneg measurableSet_Ici, hset,
    intervalIntegral.integral_of_le hδ.2.le, integral_Icc_eq_integral_Ioc]

theorem interval_head_eq {u : ℝ → ℝ} (hcont : ContinuousOn u (Icc 0 L))
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x) {δ : ℝ} (hδ : δ ∈ Ioo 0 L) :
    densityMeasure L u (Subtype.val ⁻¹' Iic δ) = ENNReal.ofReal (∫ x in (0 : ℝ)..δ, u x) := by
  have hset : Iic δ ∩ Icc 0 L = Icc 0 δ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, h2.trans hδ.2.le⟩
  rw [densityMeasure_preimage hcont hnonneg measurableSet_Iic, hset,
    intervalIntegral.integral_of_le hδ.1.le, integral_Icc_eq_integral_Ioc]

/-- **Theorem 1.3(3), left endpoint, measure form.** Densities on `[0,L]`
with mass `L u*` whose tails `∫_δ^L u_j` vanish for every `δ ∈ (0,L)`
converge weakly, as finite measures on `[0,L]`, to `L u* δ_0`. -/
theorem tendsto_dirac_left (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in δ..L, u n x) atTop (𝓝 0)) :
    Tendsto (fun n => densityFiniteMeasure L (u n) hL.le (hcont n) (hnonneg n)) atTop
      (𝓝 ((L * uStar).toNNReal • (diracProba (leftEndpoint L hL.le)).toFiniteMeasure)) := by
  apply tendsto_left_endpoint_on_Icc L hL.le _ (by simpa using mul_pos hL huStar)
  · intro n
    rw [densityFiniteMeasure_mass, hmass]
  · intro U hU h0
    obtain ⟨δ, hδ, hsub⟩ := compl_subset_of_left hL hU h0
    refine tendsto_apply_of_le (htail δ hδ) fun n => ?_
    calc (densityFiniteMeasure L (u n) hL.le (hcont n) (hnonneg n) : Measure _) Uᶜ
        ≤ densityMeasure L (u n) (Subtype.val ⁻¹' Ici δ) := measure_mono hsub
      _ = ENNReal.ofReal (∫ x in δ..L, u n x) := interval_tail_eq (hcont n) (hnonneg n) hδ

/-- **Theorem 1.3(3), right endpoint, measure form** (the reflected branch
`C_1^-`): vanishing `∫_0^δ u_j` gives weak convergence to `L u* δ_L`. -/
theorem tendsto_dirac_right (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in (0 : ℝ)..δ, u n x) atTop (𝓝 0)) :
    Tendsto (fun n => densityFiniteMeasure L (u n) hL.le (hcont n) (hnonneg n)) atTop
      (𝓝 ((L * uStar).toNNReal • (diracProba (rightEndpoint L hL.le)).toFiniteMeasure)) := by
  apply tendsto_right_endpoint_on_Icc L hL.le _ (by simpa using mul_pos hL huStar)
  · intro n
    rw [densityFiniteMeasure_mass, hmass]
  · intro U hU hLmem
    obtain ⟨δ, hδ, hsub⟩ := compl_subset_of_right hL hU hLmem
    refine tendsto_apply_of_le (htail δ hδ) fun n => ?_
    calc (densityFiniteMeasure L (u n) hL.le (hcont n) (hnonneg n) : Measure _) Uᶜ
        ≤ densityMeasure L (u n) (Subtype.val ⁻¹' Iic δ) := measure_mono hsub
      _ = ENNReal.ofReal (∫ x in (0 : ℝ)..δ, u n x) := interval_head_eq (hcont n) (hnonneg n) hδ

/-- The bounded continuous test function on `[0,L]` given by `f ∈ C([0,L])`. -/
noncomputable def testFunction (L : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) :
    ClosedInterval L →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => f x.val, hf.domRestrict⟩

/-- **Theorem 1.3(3), left endpoint, TeX lines 3381–3385**:
`∫_0^L f u_j → L u* f(0)` for every `f ∈ C([0,L])`. -/
theorem tendsto_integral_left (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in δ..L, u n x) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) :
    Tendsto (fun n => ∫ x in (0 : ℝ)..L, f x * u n x) atTop (𝓝 (L * uStar * f 0)) := by
  have h := tendsto_integral_test_of_vanishing_tails (leftEndpoint L hL.le)
    ((L * uStar).toNNReal) (by simpa using mul_pos hL huStar)
    (fun n => densityFiniteMeasure L (u n) hL.le (hcont n) (hnonneg n))
    (fun n => by rw [densityFiniteMeasure_mass, hmass])
    (fun U hU h0 => ?_) (testFunction L f hf)
  · simp only [Real.coe_toNNReal _ (mul_pos hL huStar).le] at h
    convert h using 1
    · funext n
      exact (integral_densityMeasure hL.le (hcont n) (hnonneg n) f).symm
    · rfl
  · obtain ⟨δ, hδ, hsub⟩ := compl_subset_of_left hL hU h0
    refine tendsto_apply_of_le (htail δ hδ) fun n => ?_
    calc (densityFiniteMeasure L (u n) hL.le (hcont n) (hnonneg n) : Measure _) Uᶜ
        ≤ densityMeasure L (u n) (Subtype.val ⁻¹' Ici δ) := measure_mono hsub
      _ = ENNReal.ofReal (∫ x in δ..L, u n x) := interval_tail_eq (hcont n) (hnonneg n) hδ

/-- **Theorem 1.3(3), right endpoint**: `∫_0^L f u_j → L u* f(L)`. -/
theorem tendsto_integral_right (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in (0 : ℝ)..δ, u n x) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) :
    Tendsto (fun n => ∫ x in (0 : ℝ)..L, f x * u n x) atTop (𝓝 (L * uStar * f L)) := by
  have h := tendsto_integral_test_of_vanishing_tails (rightEndpoint L hL.le)
    ((L * uStar).toNNReal) (by simpa using mul_pos hL huStar)
    (fun n => densityFiniteMeasure L (u n) hL.le (hcont n) (hnonneg n))
    (fun n => by rw [densityFiniteMeasure_mass, hmass])
    (fun U hU hLmem => ?_) (testFunction L f hf)
  · simp only [Real.coe_toNNReal _ (mul_pos hL huStar).le] at h
    convert h using 1
    · funext n
      exact (integral_densityMeasure hL.le (hcont n) (hnonneg n) f).symm
    · rfl
  · obtain ⟨δ, hδ, hsub⟩ := compl_subset_of_right hL hU hLmem
    refine tendsto_apply_of_le (htail δ hδ) fun n => ?_
    calc (densityFiniteMeasure L (u n) hL.le (hcont n) (hnonneg n) : Measure _) Uᶜ
        ≤ densityMeasure L (u n) (Subtype.val ⁻¹' Iic δ) := measure_mono hsub
      _ = ENNReal.ofReal (∫ x in (0 : ℝ)..δ, u n x) := interval_head_eq (hcont n) (hnonneg n) hδ

end Concentration

section Monotone

variable {L : ℝ}

/-- The monotone tail step (TeX lines 3378–3379): for `u` decreasing and
nonnegative on `[0,L]`, `∫_δ^L u ≤ (L - δ) u(δ)`. -/
theorem tail_le_of_antitoneOn {u : ℝ → ℝ} (hcont : ContinuousOn u (Icc 0 L))
    (hanti : AntitoneOn u (Icc 0 L)) {δ : ℝ} (hδ : δ ∈ Ioo 0 L) :
    ∫ x in δ..L, u x ≤ (L - δ) * u δ := by
  have hδmem : δ ∈ Icc 0 L := ⟨hδ.1.le, hδ.2.le⟩
  have h := intervalIntegral.integral_mono_on hδ.2.le
    ((hcont.mono (Icc_subset_Icc hδ.1.le le_rfl)).intervalIntegrable_of_Icc hδ.2.le)
    (intervalIntegrable_const (μ := volume) (c := u δ))
    (fun x hx => hanti hδmem ⟨hδ.1.le.trans hx.1, hx.2⟩ hx.1)
  simpa using h

/-- The mirror step for `u` increasing: `∫_0^δ u ≤ δ u(δ)`. -/
theorem head_le_of_monotoneOn {u : ℝ → ℝ} (hcont : ContinuousOn u (Icc 0 L))
    (hmono : MonotoneOn u (Icc 0 L)) {δ : ℝ} (hδ : δ ∈ Ioo 0 L) :
    ∫ x in (0 : ℝ)..δ, u x ≤ δ * u δ := by
  have hδmem : δ ∈ Icc 0 L := ⟨hδ.1.le, hδ.2.le⟩
  have h := intervalIntegral.integral_mono_on hδ.1.le
    ((hcont.mono (Icc_subset_Icc le_rfl hδ.2.le)).intervalIntegrable_of_Icc hδ.1.le)
    (intervalIntegrable_const (μ := volume) (c := u δ))
    (fun x hx => hmono ⟨hx.1, hx.2.trans hδ.2.le⟩ hδmem hx.2)
  simpa using h

/-- Decreasing nonnegative densities with `u_j(δ) → 0` have vanishing tails
`∫_δ^L u_j → 0`. -/
theorem tendsto_tail_of_antitoneOn (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x) (hanti : ∀ n, AntitoneOn (u n) (Icc 0 L))
    {δ : ℝ} (hδ : δ ∈ Ioo 0 L) (hpoint : Tendsto (fun n => u n δ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in δ..L, u n x) atTop (𝓝 0) := by
  have hup : Tendsto (fun n => (L - δ) * u n δ) atTop (𝓝 0) := by
    simpa using hpoint.const_mul (L - δ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_)
    (fun n => tail_le_of_antitoneOn (hcont n) (hanti n) hδ)
  exact intervalIntegral.integral_nonneg hδ.2.le fun x hx =>
    hnonneg n x ⟨hδ.1.le.trans hx.1, hx.2⟩

/-- Increasing nonnegative densities with `u_j(δ) → 0` have vanishing heads
`∫_0^δ u_j → 0`. -/
theorem tendsto_head_of_monotoneOn (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x) (hmono : ∀ n, MonotoneOn (u n) (Icc 0 L))
    {δ : ℝ} (hδ : δ ∈ Ioo 0 L) (hpoint : Tendsto (fun n => u n δ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in (0 : ℝ)..δ, u n x) atTop (𝓝 0) := by
  have hup : Tendsto (fun n => δ * u n δ) atTop (𝓝 0) := by
    simpa using hpoint.const_mul δ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_)
    (fun n => head_le_of_monotoneOn (hcont n) (hmono n) hδ)
  exact intervalIntegral.integral_nonneg hδ.1.le fun x hx =>
    hnonneg n x ⟨hx.1, hx.2.trans hδ.2.le⟩

/-- **Theorem 1.3(3) along `C_1^+`, from the PDE inputs.** For strictly
decreasing (here: decreasing) nonnegative continuous densities on `[0,L]`
with mass `L u*` and `u_j(δ) → 0` for every `δ ∈ (0,L)`,
`∫_0^L f u_j → L u* f(0)` for every `f ∈ C([0,L])`. -/
theorem tendsto_integral_left_of_antitoneOn (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x) (hanti : ∀ n, AntitoneOn (u n) (Icc 0 L))
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (hpoint : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => u n δ) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) :
    Tendsto (fun n => ∫ x in (0 : ℝ)..L, f x * u n x) atTop (𝓝 (L * uStar * f 0)) :=
  tendsto_integral_left hL uStar huStar u hcont hnonneg hmass
    (fun δ hδ => tendsto_tail_of_antitoneOn u hcont hnonneg hanti hδ (hpoint δ hδ)) f hf

/-- **Theorem 1.3(3) along `C_1^-`, from the PDE inputs**: increasing
densities concentrate at `L`. -/
theorem tendsto_integral_right_of_monotoneOn (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x) (hmono : ∀ n, MonotoneOn (u n) (Icc 0 L))
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (hpoint : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => u n δ) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) :
    Tendsto (fun n => ∫ x in (0 : ℝ)..L, f x * u n x) atTop (𝓝 (L * uStar * f L)) :=
  tendsto_integral_right hL uStar huStar u hcont hnonneg hmass
    (fun δ hδ => tendsto_head_of_monotoneOn u hcont hnonneg hmono hδ (hpoint δ hδ)) f hf

end Monotone

section Peak

variable {L : ℝ}

/-- **Theorem 1.3(3), "in particular" (TeX line 950 and 3390), left endpoint.**
If `peak j` bounds `u_j` on `[0,L]` (for instance `peak j = max u_j`), then
`peak j → ∞`. -/
theorem peak_tendsto_atTop_left (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in δ..L, u n x) atTop (𝓝 0))
    (peak : ℕ → ℝ) (hpeak : ∀ n, ∀ x ∈ Icc 0 L, u n x ≤ peak n) :
    Tendsto peak atTop atTop := by
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  refine peak_tendsto_atTop_of_mass_tail_window_bounds (I := Ioo (0 : ℝ) L) (L * uStar)
    (mul_pos hL huStar) peak (fun n => (hnonneg n 0 h0).trans (hpeak n 0 h0))
    (fun δ => δ.val) (fun ε hε => ⟨⟨min (ε / 2) (L / 2), by positivity,
      (min_le_right _ _).trans_lt (half_lt_self hL)⟩, by positivity,
      (min_le_left _ _).trans_lt (half_lt_self hε)⟩)
    (fun n δ => ∫ x in δ.val..L, u n x) (fun δ => htail δ.val δ.2) (fun n δ => ?_)
  obtain ⟨δ, hδ⟩ := δ
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (((hcont n).mono (Icc_subset_Icc le_rfl hδ.2.le)).intervalIntegrable_of_Icc
      (μ := volume) hδ.1.le)
    (((hcont n).mono (Icc_subset_Icc hδ.1.le le_rfl)).intervalIntegrable_of_Icc
      (μ := volume) hδ.2.le)
  have hhead : ∫ x in (0 : ℝ)..δ, u n x ≤ δ * peak n :=
    integral_le_of_le hδ.1.le ((hcont n).mono (Icc_subset_Icc le_rfl hδ.2.le))
      fun x hx => hpeak n x ⟨hx.1, hx.2.trans hδ.2.le⟩
  simp only
  linarith [hmass n]

/-- **Theorem 1.3(3), "in particular", right endpoint.** -/
theorem peak_tendsto_atTop_right (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in (0 : ℝ)..δ, u n x) atTop (𝓝 0))
    (peak : ℕ → ℝ) (hpeak : ∀ n, ∀ x ∈ Icc 0 L, u n x ≤ peak n) :
    Tendsto peak atTop atTop := by
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  refine peak_tendsto_atTop_of_mass_tail_window_bounds (I := Ioo (0 : ℝ) L) (L * uStar)
    (mul_pos hL huStar) peak (fun n => (hnonneg n 0 h0).trans (hpeak n 0 h0))
    (fun δ => L - δ.val) (fun ε hε => ⟨⟨max (L - ε / 2) (L / 2),
      lt_max_of_lt_right (by positivity), max_lt (by linarith) (half_lt_self hL)⟩,
      by simp only; linarith [max_lt (by linarith : L - ε / 2 < L) (half_lt_self hL)],
      by simp only; linarith [le_max_left (L - ε / 2) (L / 2)]⟩)
    (fun n δ => ∫ x in (0 : ℝ)..δ.val, u n x) (fun δ => htail δ.val δ.2) (fun n δ => ?_)
  obtain ⟨δ, hδ⟩ := δ
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (((hcont n).mono (Icc_subset_Icc le_rfl hδ.2.le)).intervalIntegrable_of_Icc
      (μ := volume) hδ.1.le)
    (((hcont n).mono (Icc_subset_Icc hδ.1.le le_rfl)).intervalIntegrable_of_Icc
      (μ := volume) hδ.2.le)
  have htailI : ∫ x in δ..L, u n x ≤ (L - δ) * peak n := by
    have h := intervalIntegral.integral_mono_on hδ.2.le
      (((hcont n).mono (Icc_subset_Icc hδ.1.le le_rfl)).intervalIntegrable_of_Icc hδ.2.le)
      (intervalIntegrable_const (μ := volume) (c := peak n))
      (fun x hx => hpeak n x ⟨hδ.1.le.trans hx.1, hx.2⟩)
    simpa using h
  simp only
  linarith [hmass n]

/-- The maximum of `u_j` on `[0,L]` tends to infinity (left-endpoint branch). -/
theorem max_tendsto_atTop_left (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in δ..L, u n x) atTop (𝓝 0))
    (xmax : ℕ → ℝ) (hmax : ∀ n, IsMaxOn (u n) (Icc 0 L) (xmax n)) :
    Tendsto (fun n => u n (xmax n)) atTop atTop :=
  peak_tendsto_atTop_left hL uStar huStar u hcont hnonneg hmass htail _
    fun n _ hx => hmax n hx

end Peak

end ChemotaxisBifurcation.IntervalConcentration
