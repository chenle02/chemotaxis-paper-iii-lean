module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.

# Paper III -- endpoint concentration from fixed mass and vanishing tails

This file isolates the measure-theoretic consumer used in Theorem 1.3(3),
label `T:global-extension`.  The production of the tail estimate from the
stationary PDE, monotonicity, and the sine test remains an explicit input.
-/

public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace ChemotaxisBifurcation.EndpointConcentration

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

/-- Fixed positive mass and vanishing mass outside every open neighborhood of
`endpoint` force weak convergence to the Dirac mass at `endpoint`.

The measures are genuine finite measures.  Their common mass is retained in
the target; the proof normalizes them only internally in order to apply the
probability-measure Portmanteau theorem. -/
theorem tendsto_mass_smul_dirac_of_vanishing_tails
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    (endpoint : X) (mass : ℝ≥0) (hmass_pos : 0 < mass)
    (μ : ℕ → FiniteMeasure X)
    (hmass : ∀ n, (μ n).mass = mass)
    (htail : ∀ U : Set X, IsOpen U → endpoint ∈ U →
      Tendsto (fun n ↦ μ n Uᶜ) atTop (𝓝 0)) :
    Tendsto μ atTop
      (𝓝 (mass • (diracProba endpoint).toFiniteMeasure)) := by
  have : Nonempty X := ⟨endpoint⟩
  have hμ_nonzero (n : ℕ) : μ n ≠ 0 := by
    rw [← FiniteMeasure.mass_nonzero_iff, hmass n]
    exact ne_of_gt hmass_pos
  have hnormalized_tail (U : Set X) (hU_open : IsOpen U)
      (hendpoint : endpoint ∈ U) :
      Tendsto (fun n ↦ (μ n).normalize Uᶜ) atTop (𝓝 0) := by
    have hscaled :
        Tendsto (fun n ↦ mass⁻¹ * μ n Uᶜ) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (htail U hU_open hendpoint)
    convert hscaled using 1
    · funext n
      rw [(μ n).normalize_eq_of_nonzero (hμ_nonzero n), hmass n]
  have hnormalized :
      Tendsto (fun n ↦ (μ n).normalize) atTop
        (𝓝 (diracProba endpoint)) := by
    apply tendsto_of_forall_isClosed_limsup_le
    intro F hF_closed
    by_cases hendpoint : endpoint ∈ F
    · have hbound :
          limsup (fun n ↦ (μ n).normalize F) atTop ≤ 1 :=
        limsup_le_of_le (by isBoundedDefault) <|
          Eventually.of_forall fun n ↦ (μ n).normalize.apply_le_one F
      simpa [diracProba, hendpoint] using hbound
    · have htail_F :
          Tendsto (fun n ↦ (μ n).normalize F) atTop (𝓝 0) := by
        have hendpoint_compl : endpoint ∈ Fᶜ := hendpoint
        simpa only [compl_compl] using
          hnormalized_tail Fᶜ (isOpen_compl_iff.mpr hF_closed) hendpoint_compl
      rw [htail_F.limsup_eq]
      simp [diracProba, hendpoint]
  have hfinite :
      Tendsto (fun n ↦ (μ n).normalize.toFiniteMeasure) atTop
        (𝓝 (diracProba endpoint).toFiniteMeasure) := by
    exact (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds atTop).mp
      hnormalized
  have hscaled :
      Tendsto (fun n ↦ mass • (μ n).normalize.toFiniteMeasure) atTop
        (𝓝 (mass • (diracProba endpoint).toFiniteMeasure)) :=
    ((continuous_const_smul mass).tendsto _).comp hfinite
  exact hscaled.congr' <| Eventually.of_forall fun n ↦ by
    simpa [hmass n] using (μ n).self_eq_mass_smul_normalize.symm

/-- The preceding weak-convergence statement written at the level of every
bounded continuous real test function.  On a compact space this includes every
continuous real-valued test function. -/
theorem tendsto_integral_test_of_vanishing_tails
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    (endpoint : X) (mass : ℝ≥0) (hmass_pos : 0 < mass)
    (μ : ℕ → FiniteMeasure X)
    (hmass : ∀ n, (μ n).mass = mass)
    (htail : ∀ U : Set X, IsOpen U → endpoint ∈ U →
      Tendsto (fun n ↦ μ n Uᶜ) atTop (𝓝 0))
    (f : X →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(μ n : Measure X)) atTop
      (𝓝 ((mass : ℝ) * f endpoint)) := by
  have hweak := tendsto_mass_smul_dirac_of_vanishing_tails
    endpoint mass hmass_pos μ hmass htail
  have htest :=
    FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f
  have hdirac :
      ((diracProba endpoint).toFiniteMeasure : Measure X) = Measure.dirac endpoint :=
    rfl
  simpa [hdirac, MeasureTheory.integral_dirac, NNReal.smul_def] using htest

/-- A compact interval is represented by its actual subtype, so its topology
and Borel measurable space are the relative ones used by the manuscript. -/
abbrev ClosedInterval (L : ℝ) := Set.Icc (0 : ℝ) L

/-- The left endpoint `0` as a point of `[0,L]`. -/
def leftEndpoint (L : ℝ) (hL : 0 ≤ L) : ClosedInterval L :=
  ⟨0, le_rfl, hL⟩

/-- The right endpoint `L` as a point of `[0,L]`. -/
def rightEndpoint (L : ℝ) (hL : 0 ≤ L) : ClosedInterval L :=
  ⟨L, hL, le_rfl⟩

/-- Manuscript-facing left-endpoint specialization on `[0,L]`.

The tail hypothesis is relative to the compact interval.  In the paper it is
supplied by the monotonicity estimate
`integral_[delta,L] u_j -> 0`. -/
theorem tendsto_left_endpoint_on_Icc
    (L : ℝ) (hL : 0 ≤ L) (mass : ℝ≥0) (hmass_pos : 0 < mass)
    (μ : ℕ → FiniteMeasure (ClosedInterval L))
    (hmass : ∀ n, (μ n).mass = mass)
    (htail : ∀ U : Set (ClosedInterval L), IsOpen U →
      leftEndpoint L hL ∈ U → Tendsto (fun n ↦ μ n Uᶜ) atTop (𝓝 0)) :
    Tendsto μ atTop
      (𝓝 (mass • (diracProba (leftEndpoint L hL)).toFiniteMeasure)) :=
  tendsto_mass_smul_dirac_of_vanishing_tails
    (leftEndpoint L hL) mass hmass_pos μ hmass htail

/-- Manuscript-facing right-endpoint specialization on `[0,L]`, used after
reflection of the decreasing-branch argument. -/
theorem tendsto_right_endpoint_on_Icc
    (L : ℝ) (hL : 0 ≤ L) (mass : ℝ≥0) (hmass_pos : 0 < mass)
    (μ : ℕ → FiniteMeasure (ClosedInterval L))
    (hmass : ∀ n, (μ n).mass = mass)
    (htail : ∀ U : Set (ClosedInterval L), IsOpen U →
      rightEndpoint L hL ∈ U → Tendsto (fun n ↦ μ n Uᶜ) atTop (𝓝 0)) :
    Tendsto μ atTop
      (𝓝 (mass • (diracProba (rightEndpoint L hL)).toFiniteMeasure)) :=
  tendsto_mass_smul_dirac_of_vanishing_tails
    (rightEndpoint L hL) mass hmass_pos μ hmass htail

/-- A scalar consumer for the manuscript's final peak-growth deduction.

`windowSize i` is the length of a shrinking endpoint neighborhood and
`tail n i` is the mass outside it.  The inequality is what follows when a
nonnegative density is bounded above by `peak n` on that neighborhood. -/
theorem peak_tendsto_atTop_of_mass_tail_window_bounds
    {I : Type*} (mass : ℝ) (hmass_pos : 0 < mass)
    (peak : ℕ → ℝ) (_hpeak_nonneg : ∀ n, 0 ≤ peak n)
    (windowSize : I → ℝ)
    (hwindow_small : ∀ ε, 0 < ε →
      ∃ i, 0 ≤ windowSize i ∧ windowSize i < ε)
    (tail : ℕ → I → ℝ)
    (htail : ∀ i, Tendsto (fun n ↦ tail n i) atTop (𝓝 0))
    (hmass_bound : ∀ n i,
      mass ≤ peak n * windowSize i + tail n i) :
    Tendsto peak atTop atTop := by
  rw [tendsto_atTop]
  intro B
  let C : ℝ := max B 0 + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith [le_max_right B 0]
  have hB_lt_C : B < C := by
    dsimp [C]
    linarith [le_max_left B 0]
  obtain ⟨i, hwindow_nonneg, hwindow_lt⟩ :=
    hwindow_small (mass / (2 * C)) (div_pos hmass_pos (mul_pos two_pos hC_pos))
  have hCwindow : C * windowSize i < mass / 2 := by
    calc
      C * windowSize i < C * (mass / (2 * C)) :=
        mul_lt_mul_of_pos_left hwindow_lt hC_pos
      _ = mass / 2 := by field_simp [ne_of_gt hC_pos]
  have htail_eventually : ∀ᶠ n in atTop, tail n i < mass / 2 :=
    (htail i) (Iio_mem_nhds (half_pos hmass_pos))
  filter_upwards [htail_eventually] with n hn
  apply le_of_lt
  apply hB_lt_C.trans
  by_contra hnot
  have hpeak_le : peak n ≤ C := le_of_not_gt hnot
  have hproduct_le : peak n * windowSize i ≤ C * windowSize i :=
    mul_le_mul_of_nonneg_right hpeak_le hwindow_nonneg
  linarith [hmass_bound n i]

end ChemotaxisBifurcation.EndpointConcentration
