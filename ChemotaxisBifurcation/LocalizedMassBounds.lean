module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic

@[expose] public section

/-!
# Uniform local mass control

Hölder is applied to an actual restricted measure. Uniformity is represented
by an arbitrary family index, not by a single selected neighborhood. A weak
limit/no-atom application still needs its separate measure-convergence bridge.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.LocalizedMassBounds

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X]

/-- Hölder's bound on every measurable neighborhood (indeed any set). -/
theorem local_mass_le_power_moment
    (mu : Measure X) [IsFiniteMeasure mu] (s : Set X)
    (u : X → ℝ) (p q : ℝ) (hpq : p.HolderConjugate q)
    (hnonneg : ∀ᵐ x ∂mu, 0 ≤ u x)
    (hu : MemLp u (ENNReal.ofReal p) mu) :
    (∫ x in s, u x ∂mu) ≤
      (∫ x in s, u x ^ p ∂mu) ^ (1 / p) * (mu.real s) ^ (1 / q) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_restrict_of_ae hnonneg)
    (Filter.Eventually.of_forall (fun _ : X => (show (0 : ℝ) ≤ 1 by norm_num)))
    (hu.restrict s) (memLp_const (1 : ℝ) : MemLp (fun _ : X => (1 : ℝ))
      (ENNReal.ofReal q) (mu.restrict s))
  simpa only [mul_one, Real.one_rpow, integral_const,
    MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul] using h

/-- Preserve the explicit neighborhood length and common moment constants. -/
theorem local_mass_le_uniform_bound
    (mu : Measure X) [IsFiniteMeasure mu] (s : Set X)
    (u : X → ℝ) (p q K c r : ℝ) (hpq : p.HolderConjugate q)
    (hnonneg : ∀ᵐ x ∂mu, 0 ≤ u x)
    (hu : MemLp u (ENNReal.ofReal p) mu)
    (hK : (∫ x in s, u x ^ p ∂mu) ≤ K)
    (hlen : mu.real s ≤ c * r) :
    (∫ x in s, u x ∂mu) ≤ K ^ (1 / p) * (c * r) ^ (1 / q) := by
  have hmoment : 0 ≤ ∫ x in s, u x ^ p ∂mu :=
    integral_nonneg_of_ae
      ((ae_restrict_of_ae hnonneg).mono fun x hx => Real.rpow_nonneg hx p)
  have hpower := Real.rpow_le_rpow hmoment hK hpq.one_div_nonneg
  have hlenpower := Real.rpow_le_rpow (measureReal_nonneg) hlen hpq.symm.one_div_nonneg
  exact (local_mass_le_power_moment mu s u p q hpq hnonneg hu).trans
    (mul_le_mul hpower hlenpower (Real.rpow_nonneg measureReal_nonneg _)
      (Real.rpow_nonneg (hmoment.trans hK) _))

/-- A common moment bound and a shrinking length bound control the ENTIRE
family uniformly. The filter may represent positive radii tending to zero. -/
theorem uniform_small_mass
    {I T : Type*} (l : Filter T) (r : T → ℝ) (K c p q : ℝ)
    (hpq : p.HolderConjugate q) (hr : Tendsto r l (𝓝 0))
    (mass : I → T → ℝ)
    (hbound : ∀ i t, mass i t ≤ K ^ (1 / p) * (c * r t) ^ (1 / q)) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ t in l, ∀ i, mass i t < epsilon := by
  have hzero : Tendsto (fun t => K ^ (1 / p) * (c * r t) ^ (1 / q)) l (𝓝 0) := by
    have hbase : Tendsto (fun t => c * r t) l (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hr
    simpa using tendsto_const_nhds.mul
      (hbase.rpow_const_nhds_zero hpq.symm.one_div_pos)
  intro epsilon hepsilon
  filter_upwards [hzero.eventually (gt_mem_nhds hepsilon)] with t ht i
  exact (hbound i t).trans_lt ht

/-- The signal factors in Lemma 4.1(2), p.27, after the maximum-principle
and signal-equation inputs. Neither analytic input is proved here. -/
theorem signal_parameter_factors
    (mu nu B gamma vmax secondBound : ℝ) (hmu : 0 < mu)
    (hmax : mu * vmax ≤ nu * B ^ gamma)
    (hsecond : secondBound ≤ mu * vmax + nu * B ^ gamma) :
    vmax ≤ (nu / mu) * B ^ gamma ∧ secondBound ≤ 2 * nu * B ^ gamma := by
  constructor
  · have hv : vmax ≤ (nu * B ^ gamma) / mu :=
      (le_div_iff₀ hmu).mpr (by simpa [mul_comm] using hmax)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hv
  · linarith

end ChemotaxisBifurcation.LocalizedMassBounds
