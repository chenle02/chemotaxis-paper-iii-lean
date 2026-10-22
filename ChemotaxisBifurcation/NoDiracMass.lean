module
public import ChemotaxisBifurcation.LocalizedMassBounds
public import ChemotaxisBifurcation.IntervalMoments

@[expose] public section

/-!
# Local mass in shrinking windows (Remark 1.3(2), label `R:spike-solution-rk`)

The manuscript shows that, in the non-minimal model, spikes cannot carry a
Dirac mass: for every stationary density `u_n`,
`∫_{(x*-δ,x*+δ)∩(0,L)} u_n ≤ (2δ)^(α/(1+α)) ‖u_n‖_{L^(1+α)}
  < u* L^(1/(1+α)) (2δ)^(α/(1+α))`,
so the mass in shrinking neighborhoods tends to zero uniformly in `n`.

`LocalizedMassBounds` proves Hölder on an abstract finite measure and the
one-sided statement `∀ ε > 0, eventually, ∀ i, mass i < ε`. This file supplies
the application inputs the P1–P4 review listed:

* the nonnegativity upgrade from that one-sided statement to uniform
  convergence to zero;
* the reference measure of `[0,L]`, `MemLp` of a continuous density, the
  neighborhood length `≤ 2δ` and the exponent specialization `p = 1 + α`,
  `q = (1+α)/α`;
* the strict global moment bound, taken from `IntervalMoments`
  (Lemma 4.1(1)), which yields the strict display.

The logistic mass identity, continuity, positivity and nonconstancy of each
`u_n` remain PDE inputs. Passing from uniform local mass control to the
absence of atoms in a weak limit is not proved here.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.NoDiracMass

open MeasureTheory Set Filter ChemotaxisBifurcation.IntervalMoments
open scoped Topology

/-- **Nonnegativity upgrade.** Nonnegative masses that are eventually below
every `ε`, uniformly in the index, converge to zero uniformly. -/
theorem tendstoUniformly_zero_of_nonneg {I T : Type*} {l : Filter T} (mass : I → T → ℝ)
    (hnonneg : ∀ i t, 0 ≤ mass i t)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in l, ∀ i, mass i t < ε) :
    TendstoUniformly (fun t i => mass i t) (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hsmall ε hε] with t ht i
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hnonneg i t)]
  exact ht i

/-- `LocalizedMassBounds.uniform_small_mass` with nonnegative masses:
uniform convergence to zero (TeX line 1018). -/
theorem uniform_mass_tendsto_zero {I T : Type*} (l : Filter T) (r : T → ℝ) (K c p q : ℝ)
    (hpq : p.HolderConjugate q) (hr : Tendsto r l (𝓝 0)) (mass : I → T → ℝ)
    (hnonneg : ∀ i t, 0 ≤ mass i t)
    (hbound : ∀ i t, mass i t ≤ K ^ (1 / p) * (c * r t) ^ (1 / q)) :
    TendstoUniformly (fun t i => mass i t) (fun _ => 0) l :=
  tendstoUniformly_zero_of_nonneg mass hnonneg
    (LocalizedMassBounds.uniform_small_mass l r K c p q hpq hr mass hbound)

/-- The neighborhood `(x*-δ, x*+δ) ∩ (0,L)` of the manuscript's display. -/
def window (L xstar δ : ℝ) : Set ℝ := Ioo (xstar - δ) (xstar + δ) ∩ Ioo 0 L

theorem window_integral_eq (L xstar δ : ℝ) (u : ℝ → ℝ) :
    ∫ x in window L xstar δ, u x = ∫ x in Ioo (xstar - δ) (xstar + δ), u x ∂intervalMeasure L := by
  rw [Measure.restrict_restrict measurableSet_Ioo]
  exact setIntegral_congr_set (ae_eq_set_inter (ae_eq_refl _) Ioo_ae_eq_Icc)

/-- **Remark 1.3(2), the display.** For `a, b, α > 0`, `u* = (a/b)^(1/α)`
and a continuous, positive, nonconstant density on `[0,L]` satisfying the
logistic mass identity, every window of half-width `δ > 0` satisfies
`∫_{(x*-δ,x*+δ)∩(0,L)} u ≤ (2δ)^(α/(1+α)) (∫_0^L u^(1+α))^(1/(1+α))
  < u* L^(1/(1+α)) (2δ)^(α/(1+α))`. -/
theorem window_mass_bounds
    (a b alpha L : ℝ) (u : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y)
    (hmass : a * ∫ x in (0 : ℝ)..L, u x = b * ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha))
    (xstar δ : ℝ) (hδ : 0 < δ) :
    ∫ x in window L xstar δ, u x ≤
        (2 * δ) ^ (alpha / (1 + alpha)) *
          (∫ x in (0 : ℝ)..L, u x ^ (1 + alpha)) ^ (1 / (1 + alpha)) ∧
      ∫ x in window L xstar δ, u x <
        (a / b) ^ (1 / alpha) * L ^ (1 / (1 + alpha)) * (2 * δ) ^ (alpha / (1 + alpha)) := by
  set p := 1 + alpha with hp_def
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hpq := Real.HolderConjugate.conjExponent hp1
  have hq : 1 / Real.conjExponent p = alpha / (1 + alpha) := by
    rw [Real.conjExponent, one_div_div, hp_def, add_sub_cancel_left]
  have hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x := fun x hx => (hpos x hx).le
  have hnonneg_ae : ∀ᵐ x ∂intervalMeasure L, 0 ≤ u x :=
    ae_restrict_of_forall_mem measurableSet_Icc hnonneg
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hmem : MemLp u (ENNReal.ofReal p) (intervalMeasure L) :=
    MemLp.of_bound (hcont.aestronglyMeasurable measurableSet_Icc) C
      (ae_restrict_of_forall_mem measurableSet_Icc hC)
  set S := Ioo (xstar - δ) (xstar + δ) with hS_def
  have hH := LocalizedMassBounds.local_mass_le_power_moment (intervalMeasure L) S u p
    (Real.conjExponent p) hpq hnonneg_ae hmem
  rw [hq] at hH
  -- the local moment is at most the global moment
  have hpowc : ContinuousOn (fun x => u x ^ p) (Icc 0 L) :=
    hcont.rpow_const fun _ _ => Or.inr hp0.le
  have hA0 : 0 ≤ ∫ x in S, u x ^ p ∂intervalMeasure L :=
    integral_nonneg_of_ae ((ae_restrict_of_ae hnonneg_ae).mono fun x hx =>
      Real.rpow_nonneg hx p)
  have hA : ∫ x in S, u x ^ p ∂intervalMeasure L ≤ ∫ x in (0 : ℝ)..L, u x ^ p := by
    rw [← integral_eq_intervalIntegral hL.le]
    exact setIntegral_le_integral (integrable_of_continuousOn hpowc)
      (hnonneg_ae.mono fun x hx => Real.rpow_nonneg hx p)
  -- the window has length at most `2δ`
  have hm : (intervalMeasure L).real S ≤ 2 * δ := by
    rw [measureReal_restrict_apply measurableSet_Ioo]
    calc volume.real (S ∩ Icc 0 L) ≤ volume.real S :=
          measureReal_mono inter_subset_left (by rw [hS_def]; exact measure_Ioo_lt_top.ne)
      _ = 2 * δ := by
        rw [hS_def, Real.volume_real_Ioo_of_le (by linarith)]
        ring
  have hs0 : 0 < alpha / (1 + alpha) := div_pos halpha hp0
  have hpinv : 0 < 1 / p := one_div_pos.mpr hp0
  have hlen := Real.rpow_le_rpow measureReal_nonneg hm hs0.le
  have hmom := Real.rpow_le_rpow hA0 hA hpinv.le
  have hJ0 : 0 ≤ ∫ x in (0 : ℝ)..L, u x ^ p :=
    intervalIntegral.integral_nonneg hL.le fun x hx => Real.rpow_nonneg (hnonneg x hx) p
  have hfirst : ∫ x in window L xstar δ, u x ≤
      (2 * δ) ^ (alpha / (1 + alpha)) * (∫ x in (0 : ℝ)..L, u x ^ p) ^ (1 / p) := by
    rw [window_integral_eq]
    calc ∫ x in S, u x ∂intervalMeasure L
        ≤ (∫ x in S, u x ^ p ∂intervalMeasure L) ^ (1 / p) *
            ((intervalMeasure L).real S) ^ (alpha / (1 + alpha)) := hH
      _ ≤ (∫ x in (0 : ℝ)..L, u x ^ p) ^ (1 / p) * (2 * δ) ^ (alpha / (1 + alpha)) :=
          mul_le_mul hmom hlen (Real.rpow_nonneg measureReal_nonneg _)
            (Real.rpow_nonneg hJ0 _)
      _ = (2 * δ) ^ (alpha / (1 + alpha)) * (∫ x in (0 : ℝ)..L, u x ^ p) ^ (1 / p) :=
          mul_comm _ _
  refine ⟨hfirst, hfirst.trans_lt ?_⟩
  -- the strict global moment bound of Lemma 4.1(1)
  obtain ⟨-, -, -, hJ⟩ := logistic_interval_bounds a b alpha L u ha hb halpha hL hcont hpos
    hnonconst hmass
  set uStar := (a / b) ^ (1 / alpha)
  have huStar : 0 < uStar := Real.rpow_pos_of_pos (div_pos ha hb) _
  have hstrict := Real.rpow_lt_rpow hJ0 hJ hpinv
  have heval : (L * uStar ^ p) ^ (1 / p) = L ^ (1 / p) * uStar := by
    rw [Real.mul_rpow hL.le (Real.rpow_nonneg huStar.le p), one_div,
      Real.rpow_rpow_inv huStar.le hp0.ne']
  rw [heval] at hstrict
  have hδpow : 0 < (2 * δ) ^ (alpha / (1 + alpha)) := Real.rpow_pos_of_pos (by positivity) _
  calc (2 * δ) ^ (alpha / (1 + alpha)) * (∫ x in (0 : ℝ)..L, u x ^ p) ^ (1 / p)
      < (2 * δ) ^ (alpha / (1 + alpha)) * (L ^ (1 / p) * uStar) :=
        mul_lt_mul_of_pos_left hstrict hδpow
    _ = uStar * L ^ (1 / p) * (2 * δ) ^ (alpha / (1 + alpha)) := by ring

/-- **Remark 1.3(2), the conclusion.** For a family `u_n` of such densities
(common `a, b, α, L`), the mass in `(x*-δ, x*+δ) ∩ (0,L)` tends to zero as
`δ → 0+`, uniformly in `n` and in the center `x*`. -/
theorem window_mass_tendstoUniformly
    (a b alpha L : ℝ) {ι : Type*} (u : ι → ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hpos : ∀ n, ∀ x ∈ Icc 0 L, 0 < u n x)
    (hnonconst : ∀ n, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u n x ≠ u n y)
    (hmass : ∀ n,
      a * ∫ x in (0 : ℝ)..L, u n x = b * ∫ x in (0 : ℝ)..L, u n x ^ (1 + alpha)) :
    TendstoUniformly (fun δ (nx : ι × ℝ) => ∫ x in window L nx.2 δ, u nx.1 x) (fun _ => 0)
      (𝓝[>] 0) := by
  refine tendstoUniformly_zero_of_nonneg (fun (nx : ι × ℝ) δ => ∫ x in window L nx.2 δ, u nx.1 x)
    (fun nx δ => setIntegral_nonneg (measurableSet_Ioo.inter measurableSet_Ioo)
      fun x hx => (hpos nx.1 x (Ioo_subset_Icc_self hx.2)).le) ?_
  intro ε hε
  set K := (a / b) ^ (1 / alpha) * L ^ (1 / (1 + alpha))
  have hg : Tendsto (fun δ : ℝ => K * (2 * δ) ^ (alpha / (1 + alpha))) (𝓝[>] 0) (𝓝 0) := by
    have hbase : Tendsto (fun δ : ℝ => 2 * δ) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun δ : ℝ => 2 * δ) (𝓝 0) (𝓝 (2 * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    simpa using tendsto_const_nhds.mul (hbase.rpow_const_nhds_zero (div_pos halpha (by linarith)))
  filter_upwards [hg.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with δ hδε hδ nx
  exact ((window_mass_bounds a b alpha L (u nx.1) ha hb halpha hL (hcont nx.1) (hpos nx.1)
    (hnonconst nx.1) (hmass nx.1) nx.2 δ hδ).2).trans hδε

end ChemotaxisBifurcation.NoDiracMass
