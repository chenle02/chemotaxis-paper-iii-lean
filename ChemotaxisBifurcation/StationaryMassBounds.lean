module
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic

@[expose] public section

/-!
# Stationary mass deductions for the October 8 manuscript

The scalar logistic consumer keeps the exact mass identity and the strict
moment inequality as separate inputs. The integral lemmas below prove Jensen
and its strict counterpart for genuine finite measures. Stationarity, boundary
conditions, and the passage from continuous nonconstancy to a.e. nonconstancy
enter only as explicit hypotheses or stay outside this file.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.StationaryMassBounds

open MeasureTheory

/-- Lemma 4.1(1), p.27: algebra after the mass identity and strict Hölder. -/
theorem logistic_moment_bounds
    (a b L alpha uStar I J : ℝ)
    (hb : 0 < b) (hL : 0 < L) (halpha : 0 < alpha)
    (hu : 0 < uStar) (hI : 0 < I)
    (hequilibrium : uStar ^ alpha = a / b)
    (hmass : a * I = b * J)
    (hstrict : I ^ (1 + alpha) < L ^ alpha * J) :
    I < L * uStar ∧ J < L * uStar ^ (1 + alpha) := by
  have ha : a = b * uStar ^ alpha := by
    have h := (eq_div_iff hb.ne').mp hequilibrium
    simpa [mul_comm] using h.symm
  have hJ : J = uStar ^ alpha * I := by
    apply mul_left_cancel₀ hb.ne'
    calc
      b * J = a * I := hmass.symm
      _ = b * (uStar ^ alpha * I) := by rw [ha]; ring
  have hfactor : I * I ^ alpha < I * (L * uStar) ^ alpha := by
    rw [Real.rpow_add hI, Real.rpow_one, hJ] at hstrict
    rw [Real.mul_rpow hL.le hu.le]
    convert hstrict using 1
    ring
  have hpower : I ^ alpha < (L * uStar) ^ alpha :=
    lt_of_mul_lt_mul_left hfactor hI.le
  have hmean : I < L * uStar :=
    (Real.rpow_lt_rpow_iff hI.le (mul_pos hL hu).le halpha).mp hpower
  refine ⟨hmean, ?_⟩
  rw [hJ, Real.rpow_add hu, Real.rpow_one]
  have h := mul_lt_mul_of_pos_left hmean (Real.rpow_pos_of_pos hu alpha)
  convert h using 1
  ring

section Integral

variable {X : Type*} [MeasurableSpace X]
variable (mu : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure mu] [NeZero mu]

/-- Fixed-mean Jensen on an actual finite measure, before restoring its mass. -/
theorem fixed_mean_power_average
    (u : X → ℝ) (gamma uStar : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hnonneg : ∀ᵐ x ∂mu, 0 ≤ u x)
    (hu : MeasureTheory.Integrable u mu)
    (hpow : MeasureTheory.Integrable (fun x => u x ^ gamma) mu)
    (hmean : MeasureTheory.average mu u = uStar) :
    MeasureTheory.average mu (fun x => u x ^ gamma) ≤ uStar ^ gamma := by
  have h := (Real.concaveOn_rpow hgamma0 hgamma1).le_map_average
    (Real.continuous_rpow_const hgamma0).continuousOn isClosed_Ici
    hnonneg hu hpow
  simpa only [hmean] using h

/-- Lemma 4.2, p.29: the Jensen moment bound with literal total mass `L`. -/
theorem fixed_mass_power_integral
    (u : X → ℝ) (L gamma uStar : ℝ)
    (hL : 0 < L) (hvolume : mu.real Set.univ = L)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hnonneg : ∀ᵐ x ∂mu, 0 ≤ u x)
    (hu : MeasureTheory.Integrable u mu)
    (hpow : MeasureTheory.Integrable (fun x => u x ^ gamma) mu)
    (hmass : (∫ x, u x ∂mu) = L * uStar) :
    (∫ x, u x ^ gamma ∂mu) ≤ L * uStar ^ gamma := by
  have hmean : MeasureTheory.average mu u = uStar := by
    rw [MeasureTheory.average_eq, hvolume, hmass]
    simp [smul_eq_mul, hL.ne']
  have h := fixed_mean_power_average mu u gamma uStar hgamma0 hgamma1
    hnonneg hu hpow hmean
  rw [MeasureTheory.average_eq, hvolume, smul_eq_mul] at h
  have hmul := mul_le_mul_of_nonneg_left h hL.le
  simpa [hL.ne', mul_assoc] using hmul

omit [NeZero mu] in
/-- Strict Jensen supplies strictness from a.e. nonconstancy, not stationarity. -/
theorem strict_power_average
    (u : X → ℝ) (p : ℝ) (hp : 1 < p)
    (hnonneg : ∀ᵐ x ∂mu, 0 ≤ u x)
    (hu : MeasureTheory.Integrable u mu)
    (hpow : MeasureTheory.Integrable (fun x => u x ^ p) mu)
    (hnonconstant : ¬ u =ᵐ[mu] Function.const X (MeasureTheory.average mu u)) :
    (MeasureTheory.average mu u) ^ p <
      MeasureTheory.average mu (fun x => u x ^ p) := by
  exact ((strictConvexOn_rpow hp).ae_eq_const_or_map_average_lt
    (Real.continuous_rpow_const (by linarith : 0 ≤ p)).continuousOn
    isClosed_Ici hnonneg hu hpow).resolve_left hnonconstant

end Integral

end ChemotaxisBifurcation.StationaryMassBounds
