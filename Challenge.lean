module
public import Mathlib

@[expose] public section

/-!
# Comparator Challenge: Mathlib-only statements (trusted)

Trusted statement module of the comparator tier (Palomar layout). It imports
Mathlib and nothing from this project. Every statement below is written in
Mathlib vocabulary only, and every proof is `sorry`; `Solution.lean` restates
each theorem with the same name and type and proves it from the project.

Each statement was copied verbatim from the project declaration named in its
docstring (same binders, same `open` context), the project declaration's
elaborated type was checked to use only constants from Mathlib and its
dependencies, and `Solution.lean` closes each restated type with the project
declaration itself (`apply` + `assumption`), so the two types are
definitionally equal. Paper labels refer to the October 8 Paper III
manuscript, as recorded in the project docstrings.

The Wave 7D additions (after the first 25 entries) also cover project
theorems whose statements mention project definitions: there each project
definition is unfolded by hand into Mathlib terms, the docstring names the
definitions unfolded, and the restated type is checked to be definitionally
equal to the project type (equal as an expression after unfolding, up to
closed proof terms).
-/

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.TrigIntegrals

/-- Lemma 2.1, display `E:cosine-sine-sine`: for an absolutely summable
cosine-coefficient sequence `u` and `n, k ≥ 1`,
`∫₀ᴸ (∑ uᵢ cos(iπx/L)) sin(nπx/L) sin(kπx/L) dx
  = L/4 (u_{|n-k|} - u_{n+k} + [n = k] u₀)`.
Project: `ChemotaxisBifurcation.TrigIntegrals.cosine_sine_sine`. -/
theorem cosine_sine_sine (L : ℝ) (hL : 0 < L) (u : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (u (Int.natAbs ((n : ℤ) - k)) - u (n + k) +
        (if n = k then u 0 else 0)) := by
  sorry

/-- Lemma 2.1, display `E:two-cosines-two-sines`: the integral of two
absolutely convergent cosine series against `sin(nπx/L) sin(kπx/L)`
(`n, k ≥ 1`) is `L/8` times the stated signed sum of convolution sums.
Project: `ChemotaxisBifurcation.TrigIntegrals.two_cosines_two_sines`. -/
theorem two_cosines_two_sines (L : ℝ) (hL : 0 < L) (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) + k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2)) := by
  sorry

/-- Lemma 2.1, display `E:cos-cos-cos` (`k ≥ 0`): the integral of two
absolutely convergent cosine series against `cos(kπx/L)`.
Project: `ChemotaxisBifurcation.TrigIntegrals.cos_cos_cos`. -/
theorem cos_cos_cos (L : ℝ) (hL : 0 < L) (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k}, u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -(k : ℤ)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = k}, u p.1.1 * v p.1.2)) +
        L / 4 * (if k = 0 then u 0 * v 0 else 0) := by
  sorry

/-- Lemma 2.1, display `E:cos-cos-cos-cos` (`k ≥ 0`): the integral of three
absolutely convergent cosine series against `cos(kπx/L)`.
Project: `ChemotaxisBifurcation.TrigIntegrals.cos_cos_cos_cos`. -/
theorem cos_cos_cos_cos (L : ℝ) (hL : 0 < L) (u v w : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖)
    (hw : Summable fun l => ‖w l‖) (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          (∑' l : ℕ, w l * Real.cos ((l : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2)) +
        L / 8 * (if k = 0 then u 0 * v 0 * w 0 else 0) := by
  sorry

/-- Lemma 2.1, display `E:cosine-sine-sine`, for `u ∈ ℓ¹(ℕ₀)`
(`lp (fun _ : ℕ => ℝ) 1`).
Project: `ChemotaxisBifurcation.TrigIntegrals.cosine_sine_sine_lp`. -/
theorem cosine_sine_sine_lp (L : ℝ) (hL : 0 < L)
    (u : lp (fun _ : ℕ => ℝ) 1) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (u (Int.natAbs ((n : ℤ) - k)) - u (n + k) +
        (if n = k then u 0 else 0)) := by
  sorry

/-- Lemma 2.1, display `E:two-cosines-two-sines`, for `u, v ∈ ℓ¹(ℕ₀)`.
Project: `ChemotaxisBifurcation.TrigIntegrals.two_cosines_two_sines_lp`. -/
theorem two_cosines_two_sines_lp (L : ℝ) (hL : 0 < L)
    (u v : lp (fun _ : ℕ => ℝ) 1) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) + k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2)) := by
  sorry

/-- Lemma 2.1, display `E:cos-cos-cos`, for `u, v ∈ ℓ¹(ℕ₀)`.
Project: `ChemotaxisBifurcation.TrigIntegrals.cos_cos_cos_lp`. -/
theorem cos_cos_cos_lp (L : ℝ) (hL : 0 < L) (u v : lp (fun _ : ℕ => ℝ) 1)
    (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k}, u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -(k : ℤ)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = k}, u p.1.1 * v p.1.2)) +
        L / 4 * (if k = 0 then u 0 * v 0 else 0) := by
  sorry

/-- Lemma 2.1, display `E:cos-cos-cos-cos`, for `u, v, w ∈ ℓ¹(ℕ₀)`.
Project: `ChemotaxisBifurcation.TrigIntegrals.cos_cos_cos_cos_lp`. -/
theorem cos_cos_cos_cos_lp (L : ℝ) (hL : 0 < L)
    (u v w : lp (fun _ : ℕ => ℝ) 1) (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          (∑' l : ℕ, w l * Real.cos ((l : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2)) +
        L / 8 * (if k = 0 then u 0 * v 0 * w 0 else 0) := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.TrigIntegrals

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.StationaryMassBounds

open MeasureTheory

/-- Lemma 4.1(1), p.27, the algebra after the mass identity and strict
Hölder: from `u*^α = a/b`, `a I = b J` and `I^(1+α) < L^α J` (with
`b, L, α, u*, I > 0`) it follows that `I < L u*` and `J < L u*^(1+α)`.
Project: `ChemotaxisBifurcation.StationaryMassBounds.logistic_moment_bounds`. -/
theorem logistic_moment_bounds
    (a b L alpha uStar I J : ℝ)
    (hb : 0 < b) (hL : 0 < L) (halpha : 0 < alpha)
    (hu : 0 < uStar) (hI : 0 < I)
    (hequilibrium : uStar ^ alpha = a / b)
    (hmass : a * I = b * J)
    (hstrict : I ^ (1 + alpha) < L ^ alpha * J) :
    I < L * uStar ∧ J < L * uStar ^ (1 + alpha) := by
  sorry

section Integral

variable {X : Type*} [MeasurableSpace X]
variable (mu : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure mu] [NeZero mu]

/-- Fixed-mean Jensen on a nonzero finite measure: for `0 ≤ γ ≤ 1`, a
nonnegative integrable `u` with `u^γ` integrable and average `u*` has
`⨍ u^γ ≤ u*^γ`.
Project: `ChemotaxisBifurcation.StationaryMassBounds.fixed_mean_power_average`. -/
theorem fixed_mean_power_average
    (u : X → ℝ) (gamma uStar : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hnonneg : ∀ᵐ x ∂mu, 0 ≤ u x)
    (hu : MeasureTheory.Integrable u mu)
    (hpow : MeasureTheory.Integrable (fun x => u x ^ gamma) mu)
    (hmean : MeasureTheory.average mu u = uStar) :
    MeasureTheory.average mu (fun x => u x ^ gamma) ≤ uStar ^ gamma := by
  sorry

/-- Lemma 4.2, p.29, the Jensen moment bound with total mass `L`: if
`μ(X) = L > 0`, `0 ≤ γ ≤ 1` and `∫ u = L u*`, then `∫ u^γ ≤ L u*^γ`.
Project: `ChemotaxisBifurcation.StationaryMassBounds.fixed_mass_power_integral`. -/
theorem fixed_mass_power_integral
    (u : X → ℝ) (L gamma uStar : ℝ)
    (hL : 0 < L) (hvolume : mu.real Set.univ = L)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hnonneg : ∀ᵐ x ∂mu, 0 ≤ u x)
    (hu : MeasureTheory.Integrable u mu)
    (hpow : MeasureTheory.Integrable (fun x => u x ^ gamma) mu)
    (hmass : (∫ x, u x ∂mu) = L * uStar) :
    (∫ x, u x ^ gamma ∂mu) ≤ L * uStar ^ gamma := by
  sorry

omit [NeZero mu] in
/-- Strict Jensen for `p > 1` on a finite measure: a nonnegative integrable
`u`, with `u^p` integrable, that is not a.e. equal to its average satisfies
`(⨍ u)^p < ⨍ u^p`.
Project: `ChemotaxisBifurcation.StationaryMassBounds.strict_power_average`. -/
theorem strict_power_average
    (u : X → ℝ) (p : ℝ) (hp : 1 < p)
    (hnonneg : ∀ᵐ x ∂mu, 0 ≤ u x)
    (hu : MeasureTheory.Integrable u mu)
    (hpow : MeasureTheory.Integrable (fun x => u x ^ p) mu)
    (hnonconstant : ¬ u =ᵐ[mu] Function.const X (MeasureTheory.average mu u)) :
    (MeasureTheory.average mu u) ^ p <
      MeasureTheory.average mu (fun x => u x ^ p) := by
  sorry

end Integral

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.StationaryMassBounds

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.IntervalMoments

open MeasureTheory Set

/-- Strict Jensen on `[0,L]` in the manuscript's form: for `p > 1` and a
continuous, nonnegative, nonconstant `u` on `[0,L]`,
`(∫₀ᴸ u)^p < L^(p-1) ∫₀ᴸ u^p`.
Project: `ChemotaxisBifurcation.IntervalMoments.strict_power_integral`. -/
theorem strict_power_integral {L p : ℝ} (hL : 0 < L) (hp : 1 < p) {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Icc 0 L)) (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y) :
    (∫ x in (0 : ℝ)..L, u x) ^ p < L ^ (p - 1) * ∫ x in (0 : ℝ)..L, u x ^ p := by
  sorry

/-- Lemma 4.1(1) on `[0,L]`: for `a, b, α > 0` and `u* = (a/b)^(1/α)`, a
continuous, positive, nonconstant density on `[0,L]` satisfying the logistic
mass identity `a ∫₀ᴸ u = b ∫₀ᴸ u^(1+α)` (TeX `E:mass-identity`, the PDE
input) obeys `0 < min u < u* < max u`, `∫₀ᴸ u < L u*` and
`∫₀ᴸ u^(1+α) < L (u*)^(1+α)`.
Project: `ChemotaxisBifurcation.IntervalMoments.logistic_interval_bounds`. -/
theorem logistic_interval_bounds
    (a b alpha L : ℝ) (u : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y)
    (hmass : a * ∫ x in (0 : ℝ)..L, u x = b * ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha)) :
    (∃ x₀ ∈ Icc 0 L, IsMinOn u (Icc 0 L) x₀ ∧ 0 < u x₀ ∧
        u x₀ < (a / b) ^ (1 / alpha)) ∧
      (∃ x₁ ∈ Icc 0 L, IsMaxOn u (Icc 0 L) x₁ ∧ (a / b) ^ (1 / alpha) < u x₁) ∧
      ∫ x in (0 : ℝ)..L, u x < L * (a / b) ^ (1 / alpha) ∧
      ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) < L * ((a / b) ^ (1 / alpha)) ^ (1 + alpha) := by
  sorry

/-- Lemma 4.2(2), TeX `L:minimal-spike-bounds`: a continuous, positive,
nonconstant density on `[0,L]` with prescribed mass `∫₀ᴸ u = L u*` obeys
`0 < min u < u* < max u` and `∫₀ᴸ u² > L (u*)²`.
Project: `ChemotaxisBifurcation.IntervalMoments.minimal_interval_bounds`. -/
theorem minimal_interval_bounds
    (L uStar : ℝ) (u : ℝ → ℝ) (hL : 0 < L)
    (hcont : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y)
    (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) :
    (∃ x₀ ∈ Icc 0 L, IsMinOn u (Icc 0 L) x₀ ∧ 0 < u x₀ ∧ u x₀ < uStar) ∧
      (∃ x₁ ∈ Icc 0 L, IsMaxOn u (Icc 0 L) x₁ ∧ uStar < u x₁) ∧
      L * uStar ^ 2 < ∫ x in (0 : ℝ)..L, u x ^ 2 := by
  sorry

/-- The Jensen step of Lemma 4.2 (TeX lines 3002 and 3331–3334): with the
prescribed mass `∫₀ᴸ u = L u*` and `0 ≤ γ ≤ 1`, a continuous nonnegative `u`
on `[0,L]` satisfies `∫₀ᴸ u^γ ≤ L (u*)^γ`.
Project: `ChemotaxisBifurcation.IntervalMoments.minimal_power_integral_le`. -/
theorem minimal_power_integral_le
    (L uStar gamma : ℝ) (u : ℝ → ℝ) (hL : 0 < L)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hcont : ContinuousOn u (Icc 0 L)) (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) :
    ∫ x in (0 : ℝ)..L, u x ^ gamma ≤ L * uStar ^ gamma := by
  sorry

/-- The first estimate in the proof of Lemma 4.1(2) (TeX lines 2832–2833):
for `0 < γ ≤ 1 + α`, the moment bound `∫₀ᴸ u^(1+α) ≤ L (u*)^(1+α)` gives
`∫₀ᴸ u^γ ≤ L (u*)^γ`.
Project: `ChemotaxisBifurcation.IntervalMoments.logistic_power_integral_le`. -/
theorem logistic_power_integral_le
    (L uStar alpha gamma : ℝ) (u : ℝ → ℝ) (hL : 0 < L) (halpha : 0 < alpha)
    (huStar : 0 ≤ uStar) (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1 + alpha)
    (hcont : ContinuousOn u (Icc 0 L)) (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha)) :
    ∫ x in (0 : ℝ)..L, u x ^ gamma ≤ L * uStar ^ gamma := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.IntervalMoments

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.LocalizedMassBounds

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X]

/-- Hölder's bound on any set `s` for a finite measure: for Hölder-conjugate
`p, q` and nonnegative `u ∈ L^p`,
`∫_s u ≤ (∫_s u^p)^(1/p) μ(s)^(1/q)`.
Project: `ChemotaxisBifurcation.LocalizedMassBounds.local_mass_le_power_moment`. -/
theorem local_mass_le_power_moment
    (mu : Measure X) [IsFiniteMeasure mu] (s : Set X)
    (u : X → ℝ) (p q : ℝ) (hpq : p.HolderConjugate q)
    (hnonneg : ∀ᵐ x ∂mu, 0 ≤ u x)
    (hu : MemLp u (ENNReal.ofReal p) mu) :
    (∫ x in s, u x ∂mu) ≤
      (∫ x in s, u x ^ p ∂mu) ^ (1 / p) * (mu.real s) ^ (1 / q) := by
  sorry

/-- The localized Hölder bound with explicit moment constant `K` and
neighborhood length `c r`: `∫_s u ≤ K^(1/p) (c r)^(1/q)`.
Project: `ChemotaxisBifurcation.LocalizedMassBounds.local_mass_le_uniform_bound`. -/
theorem local_mass_le_uniform_bound
    (mu : Measure X) [IsFiniteMeasure mu] (s : Set X)
    (u : X → ℝ) (p q K c r : ℝ) (hpq : p.HolderConjugate q)
    (hnonneg : ∀ᵐ x ∂mu, 0 ≤ u x)
    (hu : MemLp u (ENNReal.ofReal p) mu)
    (hK : (∫ x in s, u x ^ p ∂mu) ≤ K)
    (hlen : mu.real s ≤ c * r) :
    (∫ x in s, u x ∂mu) ≤ K ^ (1 / p) * (c * r) ^ (1 / q) := by
  sorry

/-- A common moment bound and a length bound `r → 0` along `l` make the
whole family of masses eventually smaller than every `ε > 0`, uniformly in
the index.
Project: `ChemotaxisBifurcation.LocalizedMassBounds.uniform_small_mass`. -/
theorem uniform_small_mass
    {I T : Type*} (l : Filter T) (r : T → ℝ) (K c p q : ℝ)
    (hpq : p.HolderConjugate q) (hr : Tendsto r l (𝓝 0))
    (mass : I → T → ℝ)
    (hbound : ∀ i t, mass i t ≤ K ^ (1 / p) * (c * r t) ^ (1 / q)) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ t in l, ∀ i, mass i t < epsilon := by
  sorry

/-- The signal factors in Lemma 4.1(2), p.27, after the maximum-principle
and signal-equation inputs (assumed as hypotheses `hmax`, `hsecond`):
`v_max ≤ (ν/μ) B^γ` and `secondBound ≤ 2 ν B^γ`.
Project: `ChemotaxisBifurcation.LocalizedMassBounds.signal_parameter_factors`. -/
theorem signal_parameter_factors
    (mu nu B gamma vmax secondBound : ℝ) (hmu : 0 < mu)
    (hmax : mu * vmax ≤ nu * B ^ gamma)
    (hsecond : secondBound ≤ mu * vmax + nu * B ^ gamma) :
    vmax ≤ (nu / mu) * B ^ gamma ∧ secondBound ≤ 2 * nu * B ^ gamma := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.LocalizedMassBounds

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.EndpointConcentration

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

/-- Finite measures of fixed positive mass whose mass outside every open
neighborhood of `endpoint` vanishes converge weakly to `mass • δ_endpoint`.
Project:
`ChemotaxisBifurcation.EndpointConcentration.tendsto_mass_smul_dirac_of_vanishing_tails`. -/
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
  sorry

/-- The same concentration at the level of bounded continuous real test
functions: `∫ f dμₙ → mass · f(endpoint)`.
Project:
`ChemotaxisBifurcation.EndpointConcentration.tendsto_integral_test_of_vanishing_tails`. -/
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
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.EndpointConcentration

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.MinimalFlux

open Set

/-- Lemma 4.2(5), the exponential representation for `m = 1`: if `u` is
positive and continuous on `[0,L]`, has derivative `du` on `(0,L)`, satisfies
the flux identity `u_x = χ₀ u/(1+v)^β v_x` there, and
`g = χ₀ v_x/(1+v)^β` is continuous on `[0,L]`, then
`u(x) = u(x₀) exp(∫_{x₀}^x g)` for all `x₀, x ∈ [0,L]`.
Project: `ChemotaxisBifurcation.MinimalFlux.minimal_exp_representation`. -/
theorem minimal_exp_representation (L chi0 beta : ℝ) (u v du dv : ℝ → ℝ)
    (hu_cont : ContinuousOn u (Icc 0 L)) (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hflux : ∀ x ∈ Ioo 0 L, du x = chi0 * (u x / (1 + v x) ^ beta) * dv x)
    (hg_cont : ContinuousOn (fun y => chi0 * dv y / (1 + v y) ^ beta) (Icc 0 L)) :
    ∀ x₀ ∈ Icc 0 L, ∀ x ∈ Icc 0 L,
      u x = u x₀ * Real.exp (∫ y in x₀..x, chi0 * dv y / (1 + v y) ^ beta) := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.MinimalFlux

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.NoDiracMass

open MeasureTheory Set Filter
open scoped Topology

/-- Nonnegativity upgrade: nonnegative masses that are eventually below every
`ε > 0`, uniformly in the index, converge to zero uniformly.
Project: `ChemotaxisBifurcation.NoDiracMass.tendstoUniformly_zero_of_nonneg`. -/
theorem tendstoUniformly_zero_of_nonneg {I T : Type*} {l : Filter T} (mass : I → T → ℝ)
    (hnonneg : ∀ i t, 0 ≤ mass i t)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in l, ∀ i, mass i t < ε) :
    TendstoUniformly (fun t i => mass i t) (fun _ => 0) l := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.NoDiracMass

/-! ## Wave 7D additions

The statements below restate project theorems whose types mention project
definitions (`MixedRemainder.absorbedConst`, `MixedRemainder.reducedField`,
`MinimalFlux.flux`, `NoDiracMass.window`, `InfiniteCosineProjection.cosinePhase`,
`FourierKernels.sinePhase`, `FourierKernels.ind`,
`SpecializedPolynomial.coefficient`) with those definitions unfolded by hand
into Mathlib terms, plus a few project theorems that were already in Mathlib
vocabulary. Each is definitionally equal to the project statement; the
docstring names the project declaration and the unfolded definitions. -/

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.MixedRemainder

open Filter Topology

/-- Eq. 2.43 implies the weaker (Remark 1.1 / Eq. 2.48) value bound: if
`|s| ≤ 1` and `|R| ≤ C (s² η² + |s|³ |η| + s⁴)` with `C ≥ 0`, then
`|R| ≤ C (|s| η² + |s|³ |η| + s⁴)`.
Project: `ChemotaxisBifurcation.MixedRemainder.center_ODE_final_value_bound_weak`
(no project definition in the statement). -/
theorem center_ODE_final_value_bound_weak (eta s R C : ℝ)
    (hC : 0 ≤ C) (hs1 : |s| ≤ 1)
    (hR : |R| ≤ C * (s ^ 2 * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4)) :
    |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4) := by
  sorry

/-- The derivative form of the Eq. 2.43 remainder, `|s| η² + s² |η| + |s|³`,
implies the weaker derivative bound `η² + s² |η| + |s|³` when `|s| ≤ 1`.
Project: `ChemotaxisBifurcation.MixedRemainder.center_ODE_final_deriv_bound_weak`
(no project definition in the statement). -/
theorem center_ODE_final_deriv_bound_weak (eta s Rs C : ℝ)
    (hC : 0 ≤ C) (hs1 : |s| ≤ 1)
    (hRs : |Rs| ≤ C * (|s| * eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3)) :
    |Rs| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := by
  sorry

/-- Step 5 / Step 4' scalar conclusions under the weak mixed remainder
(Remark 1.1, Eq. 2.48): for a nonzero small equilibrium `s` of
`α η s - β s³ + R = 0` with `|R| ≤ C (|s| η² + |s|³ |η| + s⁴)` and derivative
`ds = α η - 3 β s² + Rs` with `|Rs| ≤ C (η² + s² |η| + |s|³)`, under the
rectangle condition `C' (|η| + |s|) ≤ |β|/2` with
`C' = C (2 (|β| + 2C)/α + 1)`: the side condition `η β > 0`, the derivative
sign `ds β < 0`, and `||s| - √(α η / β)| ≤ (2 α C' (3|β|/(2α) + 1)/|β|²) |η|`.
Project: `ChemotaxisBifurcation.MixedRemainder.mixed_equilibrium_core`, with
`absorbedConst α β C = C * (ampConst α β C + 1)` and
`ampConst α β C = 2 * (|β| + 2 * C) / α` unfolded. -/
theorem mixed_equilibrium_core (alpha beta eta s R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : s ≠ 0) (hC : 0 ≤ C)
    (hs1 : |s| ≤ 1) (heta1 : |eta| ≤ 1) (hetaC : 2 * C * |eta| ≤ alpha)
    (hroot : alpha * eta * s - beta * s ^ 3 + R = 0)
    (hderiv : ds = alpha * eta - 3 * beta * s ^ 2 + Rs)
    (hR : |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4))
    (hRs : |Rs| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3))
    (hrectangle :
      C * (2 * (|beta| + 2 * C) / alpha + 1) * (|eta| + |s|) ≤ |beta| / 2) :
    0 < eta * beta ∧ ds * beta < 0 ∧
      abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
        (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| := by
  sorry

/-- The same conclusions as `mixed_equilibrium_core` from the Eq. 2.43 bounds
(`s² η²` in the value bound, `|s| η²` in the derivative bound).
Project: `ChemotaxisBifurcation.MixedRemainder.center_ODE_final_equilibrium_core`,
with `absorbedConst` and `ampConst` unfolded as above. -/
theorem center_ODE_final_equilibrium_core (alpha beta eta s R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : s ≠ 0) (hC : 0 ≤ C)
    (hs1 : |s| ≤ 1) (heta1 : |eta| ≤ 1) (hetaC : 2 * C * |eta| ≤ alpha)
    (hroot : alpha * eta * s - beta * s ^ 3 + R = 0)
    (hderiv : ds = alpha * eta - 3 * beta * s ^ 2 + Rs)
    (hR : |R| ≤ C * (s ^ 2 * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4))
    (hRs : |Rs| ≤ C * (|s| * eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3))
    (hrectangle :
      C * (2 * (|beta| + 2 * C) / alpha + 1) * (|eta| + |s|) ≤ |beta| / 2) :
    0 < eta * beta ∧ ds * beta < 0 ∧
      abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
        (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
            (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| := by
  sorry

/-- Theorem 1.1 part 1 / Remark 1.1 / Step 5, scalar core under the weak mixed
remainder, along `η → 0`. Let `R(η, s)` have `s`-derivative `Rs(η, s)` on the
box `|η|, |s| ≤ r ≤ 1`, with `|R| ≤ C (|s| η² + |s|³ |η| + s⁴)` and
`|Rs| ≤ C (η² + s² |η| + |s|³)` there. Then for all `η` near `0` with
`η β > 0` the reduced field `F_η(s) = α η s - β s³ + R(η, s)` has a zero `s`
of each sign, with `||s| - √(α η / β)| ≤ K |η|`
(`K = 2 α C' (3|β|/(2α) + 1)/|β|²`, `C' = C (2 (|β| + 2C)/α + 1)`) and
`F_η'(s) β < 0`.
Project: `ChemotaxisBifurcation.MixedRemainder.mixed_branch_eventually`, with
`reducedField α β R η = fun s => α * η * s - β * s ^ 3 + R η s`,
`absorbedConst` and `ampConst` unfolded. -/
theorem mixed_branch_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) :
    ∀ᶠ eta in 𝓝 (0 : ℝ), 0 < eta * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ s, 0 < sgn * s ∧
        alpha * eta * s - beta * s ^ 3 + R eta s = 0 ∧
        abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
          (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| ∧
        deriv (fun s => alpha * eta * s - beta * s ^ 3 + R eta s) s * beta < 0 := by
  sorry

/-- Side condition (Step 5, `β_{n₀} χ̃ > 0`): under the hypotheses of
`mixed_branch_eventually`, near `(η, s) = (0, 0)` every nontrivial zero `s`
of the reduced field `F_η(s) = α η s - β s³ + R(η, s)` lies on the side
`η β > 0`, and `F_η'(s) β < 0`.
Project: `ChemotaxisBifurcation.MixedRemainder.mixed_side_condition_eventually`,
with `reducedField` unfolded. -/
theorem mixed_side_condition_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), p.2 ≠ 0 →
      alpha * p.1 * p.2 - beta * p.2 ^ 3 + R p.1 p.2 = 0 →
        0 < p.1 * beta ∧
          deriv (fun s => alpha * p.1 * s - beta * s ^ 3 + R p.1 s) p.2 * beta < 0 := by
  sorry

/-- The branch theorem from the Eq. 2.43 bounds (`s² η²` in the value bound,
`|s| η²` in the derivative bound), through the weak interface; conclusions as
in `mixed_branch_eventually`.
Project: `ChemotaxisBifurcation.MixedRemainder.center_ODE_final_branch_eventually`,
with `reducedField`, `absorbedConst` and `ampConst` unfolded. -/
theorem center_ODE_final_branch_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) :
    ∀ᶠ eta in 𝓝 (0 : ℝ), 0 < eta * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ s, 0 < sgn * s ∧
        alpha * eta * s - beta * s ^ 3 + R eta s = 0 ∧
        abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
          (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| ∧
        deriv (fun s => alpha * eta * s - beta * s ^ 3 + R eta s) s * beta < 0 := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.MixedRemainder

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.MinimalFlux

open Set

/-- A function continuous on `[0,L]` with zero derivative on `(0,L)` equals
its value at `0` throughout `[0,L]` (component of Lemma 4.2(1), (5)).
Project: `ChemotaxisBifurcation.MinimalFlux.eq_left_of_hasDerivAt_zero`
(no project definition in the statement). -/
theorem eq_left_of_hasDerivAt_zero {L : ℝ} {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt F 0 x) :
    ∀ x ∈ Icc 0 L, F x = F 0 := by
  sorry

/-- Lemma 4.2(1), TeX `E:minimal-spike-flux`: if `u_x` is continuous on
`[0,L]` with derivative `u_xx` on `(0,L)`, the flux
`J = χ₀ u^m/(1+v)^β v_x` is continuous on `[0,L]` with derivative `dJ` on
`(0,L)`, the stationary minimal equation `u_xx - dJ = 0` holds on `(0,L)`, and
`u_x(0) = v_x(0) = 0`, then `u_x = χ₀ u^m/(1+v)^β v_x` on `[0,L]`.
Project: `ChemotaxisBifurcation.MinimalFlux.minimal_flux_identity`, with
`flux χ₀ m β u v dv = fun x => χ₀ * (u x ^ m / (1 + v x) ^ β) * dv x`
unfolded. -/
theorem minimal_flux_identity (L chi0 m beta : ℝ) (u v du ddu dv dJ : ℝ → ℝ)
    (hdu_cont : ContinuousOn du (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hJ_cont : ContinuousOn (fun x => chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x)
      (Icc 0 L))
    (hJ : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun x => chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x) (dJ x) x)
    (hstationary : ∀ x ∈ Ioo 0 L, ddu x - dJ x = 0)
    (hbc_u : du 0 = 0) (hbc_v : dv 0 = 0) :
    ∀ x ∈ Icc 0 L, du x = chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.MinimalFlux

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.NoDiracMass

open MeasureTheory Set Filter
open scoped Topology

/-- Uniform convergence to zero of nonnegative masses bounded by
`K^(1/p) (c r(t))^(1/q)` with `r → 0` and `p, q` Hölder conjugate
(TeX line 1018).
Project: `ChemotaxisBifurcation.NoDiracMass.uniform_mass_tendsto_zero`
(no project definition in the statement). -/
theorem uniform_mass_tendsto_zero {I T : Type*} (l : Filter T) (r : T → ℝ) (K c p q : ℝ)
    (hpq : p.HolderConjugate q) (hr : Tendsto r l (𝓝 0)) (mass : I → T → ℝ)
    (hnonneg : ∀ i t, 0 ≤ mass i t)
    (hbound : ∀ i t, mass i t ≤ K ^ (1 / p) * (c * r t) ^ (1 / q)) :
    TendstoUniformly (fun t i => mass i t) (fun _ => 0) l := by
  sorry

/-- Remark 1.3(2), the display: for `a, b, α > 0`, `L > 0` and a continuous,
positive, nonconstant density `u` on `[0,L]` with
`a ∫₀ᴸ u = b ∫₀ᴸ u^(1+α)`, every window `(x*-δ, x*+δ) ∩ (0,L)` with `δ > 0`
satisfies `∫_window u ≤ (2δ)^(α/(1+α)) (∫₀ᴸ u^(1+α))^(1/(1+α))` and
`∫_window u < (a/b)^(1/α) L^(1/(1+α)) (2δ)^(α/(1+α))`.
Project: `ChemotaxisBifurcation.NoDiracMass.window_mass_bounds`, with
`window L x* δ = Ioo (x* - δ) (x* + δ) ∩ Ioo 0 L` unfolded. -/
theorem window_mass_bounds
    (a b alpha L : ℝ) (u : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y)
    (hmass : a * ∫ x in (0 : ℝ)..L, u x = b * ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha))
    (xstar δ : ℝ) (hδ : 0 < δ) :
    ∫ x in Ioo (xstar - δ) (xstar + δ) ∩ Ioo 0 L, u x ≤
        (2 * δ) ^ (alpha / (1 + alpha)) *
          (∫ x in (0 : ℝ)..L, u x ^ (1 + alpha)) ^ (1 / (1 + alpha)) ∧
      ∫ x in Ioo (xstar - δ) (xstar + δ) ∩ Ioo 0 L, u x <
        (a / b) ^ (1 / alpha) * L ^ (1 / (1 + alpha)) * (2 * δ) ^ (alpha / (1 + alpha)) := by
  sorry

/-- Remark 1.3(2), the conclusion: for a family `u_n` of such densities
(common `a, b, α, L`), the mass of `u_n` in `(x*-δ, x*+δ) ∩ (0,L)` tends to
zero as `δ → 0+`, uniformly in `n` and in the center `x*`.
Project: `ChemotaxisBifurcation.NoDiracMass.window_mass_tendstoUniformly`,
with `window` unfolded. -/
theorem window_mass_tendstoUniformly
    (a b alpha L : ℝ) {ι : Type*} (u : ι → ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hpos : ∀ n, ∀ x ∈ Icc 0 L, 0 < u n x)
    (hnonconst : ∀ n, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u n x ≠ u n y)
    (hmass : ∀ n,
      a * ∫ x in (0 : ℝ)..L, u n x = b * ∫ x in (0 : ℝ)..L, u n x ^ (1 + alpha)) :
    TendstoUniformly
      (fun δ (nx : ι × ℝ) => ∫ x in Ioo (nx.2 - δ) (nx.2 + δ) ∩ Ioo 0 L, u nx.1 x)
      (fun _ => 0) (𝓝[>] 0) := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.NoDiracMass

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.IntervalConcentration

open MeasureTheory Set Filter
open scoped Topology

variable {L : ℝ}

/-- Theorem 1.3(3), left endpoint, TeX lines 3381–3385: nonnegative continuous
densities `u_j` on `[0,L]` with mass `∫₀ᴸ u_j = L u*` (`u* > 0`) whose tails
`∫_δ^L u_j` vanish for every `δ ∈ (0,L)` satisfy
`∫₀ᴸ f u_j → L u* f(0)` for every `f` continuous on `[0,L]`.
Project: `ChemotaxisBifurcation.IntervalConcentration.tendsto_integral_left`
(no project definition in the statement). -/
theorem tendsto_integral_left (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in δ..L, u n x) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) :
    Tendsto (fun n => ∫ x in (0 : ℝ)..L, f x * u n x) atTop (𝓝 (L * uStar * f 0)) := by
  sorry

/-- Theorem 1.3(3), right endpoint: with vanishing heads `∫₀^δ u_j`,
`∫₀ᴸ f u_j → L u* f(L)`.
Project: `ChemotaxisBifurcation.IntervalConcentration.tendsto_integral_right`
(no project definition in the statement). -/
theorem tendsto_integral_right (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in (0 : ℝ)..δ, u n x) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) :
    Tendsto (fun n => ∫ x in (0 : ℝ)..L, f x * u n x) atTop (𝓝 (L * uStar * f L)) := by
  sorry

/-- Theorem 1.3(3) along `C_1^+`, from the PDE inputs: decreasing
nonnegative continuous densities on `[0,L]` with mass `L u*` and
`u_j(δ) → 0` for every `δ ∈ (0,L)` satisfy `∫₀ᴸ f u_j → L u* f(0)` for every
`f` continuous on `[0,L]`.
Project:
`ChemotaxisBifurcation.IntervalConcentration.tendsto_integral_left_of_antitoneOn`
(no project definition in the statement). -/
theorem tendsto_integral_left_of_antitoneOn (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x) (hanti : ∀ n, AntitoneOn (u n) (Icc 0 L))
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (hpoint : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => u n δ) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) :
    Tendsto (fun n => ∫ x in (0 : ℝ)..L, f x * u n x) atTop (𝓝 (L * uStar * f 0)) := by
  sorry

/-- Theorem 1.3(3) along `C_1^-`, from the PDE inputs: increasing densities
concentrate at `L`, `∫₀ᴸ f u_j → L u* f(L)`.
Project:
`ChemotaxisBifurcation.IntervalConcentration.tendsto_integral_right_of_monotoneOn`
(no project definition in the statement). -/
theorem tendsto_integral_right_of_monotoneOn (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x) (hmono : ∀ n, MonotoneOn (u n) (Icc 0 L))
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (hpoint : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => u n δ) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) :
    Tendsto (fun n => ∫ x in (0 : ℝ)..L, f x * u n x) atTop (𝓝 (L * uStar * f L)) := by
  sorry

/-- Theorem 1.3(3), "in particular" (TeX lines 950 and 3390), left endpoint:
under the hypotheses of `tendsto_integral_left`, any `peak j` bounding `u_j`
on `[0,L]` tends to `+∞`.
Project: `ChemotaxisBifurcation.IntervalConcentration.peak_tendsto_atTop_left`
(no project definition in the statement). -/
theorem peak_tendsto_atTop_left (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in δ..L, u n x) atTop (𝓝 0))
    (peak : ℕ → ℝ) (hpeak : ∀ n, ∀ x ∈ Icc 0 L, u n x ≤ peak n) :
    Tendsto peak atTop atTop := by
  sorry

/-- Theorem 1.3(3), "in particular", right endpoint: under the hypotheses of
`tendsto_integral_right`, any `peak j` bounding `u_j` on `[0,L]` tends to `+∞`.
Project: `ChemotaxisBifurcation.IntervalConcentration.peak_tendsto_atTop_right`
(no project definition in the statement). -/
theorem peak_tendsto_atTop_right (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in (0 : ℝ)..δ, u n x) atTop (𝓝 0))
    (peak : ℕ → ℝ) (hpeak : ∀ n, ∀ x ∈ Icc 0 L, u n x ≤ peak n) :
    Tendsto peak atTop atTop := by
  sorry

/-- The maximum of `u_j` on `[0,L]` tends to `+∞` (left-endpoint branch):
`xmax j` is a maximizer of `u_j` on `[0,L]`.
Project: `ChemotaxisBifurcation.IntervalConcentration.max_tendsto_atTop_left`
(no project definition in the statement). -/
theorem max_tendsto_atTop_left (hL : 0 < L) (uStar : ℝ) (huStar : 0 < uStar)
    (u : ℕ → ℝ → ℝ) (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hnonneg : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x = L * uStar)
    (htail : ∀ δ ∈ Ioo 0 L, Tendsto (fun n => ∫ x in δ..L, u n x) atTop (𝓝 0))
    (xmax : ℕ → ℝ) (hmax : ∀ n, IsMaxOn (u n) (Icc 0 L) (xmax n)) :
    Tendsto (fun n => u n (xmax n)) atTop atTop := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.IntervalConcentration

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.FourierKernels

/-- Kernel of Lemma 2.1, `E:cosine-sine-sine` (TeX line 1179): for `L > 0`
and `n, k ≥ 1`,
`∫₀ᴸ cos(iπx/L) sin(nπx/L) sin(kπx/L) dx
  = (L/4)(1_{i=|n-k|} - 1_{i=n+k} + 1_{n=k ∧ i=0})`.
Project: `ChemotaxisBifurcation.FourierKernels.integral_cos_sin_sin`, with
`cosinePhase L i x = Real.cos (i * π * x / L)`,
`sinePhase L n x = Real.sin (n * π * x / L)` and
`ind P = if P then 1 else 0` unfolded. -/
theorem integral_cos_sin_sin (L : ℝ) (hL : 0 < L) (i n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.sin ((n : ℝ) * Real.pi * x / L) *
        Real.sin ((k : ℝ) * Real.pi * x / L)) =
      L / 4 * ((if i = Int.natAbs ((n : ℤ) - k) then 1 else 0) -
        (if i = n + k then 1 else 0) +
        (if n = k ∧ i = 0 then 1 else 0)) := by
  sorry

/-- Kernel of Lemma 2.1, `E:cos-cos-cos` (TeX line 1204): for `L > 0` and all
`i, j, k ≥ 0`,
`∫₀ᴸ cos(iπx/L) cos(jπx/L) cos(kπx/L) dx
  = (L/4)(1_{i-j=k} + 1_{i-j=-k} + 1_{i+j=k}) + (L/4) 1_{k=i=j=0}`
(differences in `ℤ`).
Project: `ChemotaxisBifurcation.FourierKernels.integral_cos_cos_cos`, with
`cosinePhase` and `ind` unfolded. -/
theorem integral_cos_cos_cos (L : ℝ) (hL : 0 < L) (i j k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.cos ((j : ℝ) * Real.pi * x / L) *
        Real.cos ((k : ℝ) * Real.pi * x / L)) =
      L / 4 * ((if (i : ℤ) - j = k then 1 else 0) + (if (i : ℤ) - j = -k then 1 else 0) +
        (if (i : ℤ) + j = k then 1 else 0)) +
        L / 4 * (if k = 0 ∧ i = 0 ∧ j = 0 then 1 else 0) := by
  sorry

/-- Kernel of Lemma 2.1, `E:two-cosines-two-sines` (TeX line 1190): for
`L > 0` and `n, k ≥ 1`, `∫₀ᴸ cos(iπx/L) cos(jπx/L) sin(nπx/L) sin(kπx/L) dx`
is `(L/8)` times the seven signed indicators of the manuscript display
(differences in `ℤ`).
Project: `ChemotaxisBifurcation.FourierKernels.integral_cos_cos_sin_sin`, with
`cosinePhase`, `sinePhase` and `ind` unfolded. -/
theorem integral_cos_cos_sin_sin (L : ℝ) (hL : 0 < L) (i j n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.cos ((j : ℝ) * Real.pi * x / L) *
        Real.sin ((n : ℝ) * Real.pi * x / L) * Real.sin ((k : ℝ) * Real.pi * x / L)) =
      L / 8 * ((if (i : ℤ) - j = (n : ℤ) - k then 1 else 0) +
        (if (i : ℤ) - j = -((n : ℤ) - k) then 1 else 0) +
        (if (i : ℤ) + j = (n : ℤ) - k then 1 else 0) +
        (if (i : ℤ) + j = -((n : ℤ) - k) then 1 else 0) -
        (if (i : ℤ) - j = (n : ℤ) + k then 1 else 0) -
        (if (i : ℤ) - j = -((n : ℤ) + k) then 1 else 0) -
        (if (i : ℤ) + j = (n : ℤ) + k then 1 else 0)) := by
  sorry

/-- Kernel of Lemma 2.1, `E:cos-cos-cos-cos` (TeX line 1220): for `L > 0` and
all indices, `∫₀ᴸ cos(iπx/L) cos(jπx/L) cos(lπx/L) cos(kπx/L) dx` is `(L/8)`
times the seven signed indicators of the manuscript display plus
`(L/8) 1_{k=i=j=l=0}` (sums and differences in `ℤ`).
Project: `ChemotaxisBifurcation.FourierKernels.integral_cos_cos_cos_cos`, with
`cosinePhase` and `ind` unfolded. -/
theorem integral_cos_cos_cos_cos (L : ℝ) (hL : 0 < L) (i j l k : ℕ) :
    (∫ x in (0 : ℝ)..L,
      Real.cos ((i : ℝ) * Real.pi * x / L) * Real.cos ((j : ℝ) * Real.pi * x / L) *
        Real.cos ((l : ℝ) * Real.pi * x / L) * Real.cos ((k : ℝ) * Real.pi * x / L)) =
      L / 8 * ((if (i : ℤ) + j + l = k then 1 else 0) +
        (if (i : ℤ) + j - l = k then 1 else 0) +
        (if (i : ℤ) + j - l = -k then 1 else 0) +
        (if (i : ℤ) - j + l = k then 1 else 0) +
        (if (i : ℤ) - j + l = -k then 1 else 0) +
        (if (i : ℤ) - j - l = k then 1 else 0) +
        (if (i : ℤ) - j - l = -k then 1 else 0)) +
        L / 8 * (if k = 0 ∧ i = 0 ∧ j = 0 ∧ l = 0 then 1 else 0) := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.FourierKernels

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.NormalizedAsymptotic

open Filter Asymptotics

/-- Eq. 3.7, explicit bound (`a = b = μ = ν = m = α = γ = 1`): with
`P(λ) = (224 - 96β)λ⁴ + (192 - 152β)λ³ + (8 - 104β - 16β²)λ²
  + (96 - 28β - 8β²)λ + 56 + 11β - β²` and `Q(λ) = 96(1+λ)(4λ² - 1)`,
for `λ ≥ 1`, `|P(λ)/Q(λ) - (7/12 - β/4)λ| ≤ (|c₃| + |c₂| + |c₁| + |c₀|)/288`
with the coefficients `cᵢ` of the cubic remainder.
Project: `ChemotaxisBifurcation.NormalizedAsymptotic.abs_coefficient_sub_linear_le`,
with `SpecializedPolynomial.coefficient λ β = numerator λ β / denominator λ`,
`numerator`, `denominator` and `NormalizedAsymptotic.slope β = 7/12 - β/4`
unfolded. -/
theorem abs_coefficient_sub_linear_le {lambda beta : ℝ} (hlambda : 1 ≤ lambda) :
    |((224 - 96 * beta) * lambda ^ 4
        + (192 - 152 * beta) * lambda ^ 3
        + (8 - 104 * beta - 16 * beta ^ 2) * lambda ^ 2
        + (96 - 28 * beta - 8 * beta ^ 2) * lambda
        + 56 + 11 * beta - beta ^ 2) /
        (96 * (1 + lambda) * (4 * lambda ^ 2 - 1)) - (7 / 12 - beta / 4) * lambda| ≤
      (|-32 - 56 * beta| + |64 - 128 * beta - 16 * beta ^ 2|
        + |152 - 52 * beta - 8 * beta ^ 2| + |56 + 11 * beta - beta ^ 2|) / 288 := by
  sorry

/-- Eq. 3.7 (`E:new-beta-eq1`) for the normalized coefficient
(`a = b = μ = ν = m = α = γ = 1`): `P(λ)/Q(λ) - (7/12 - β/4)λ = O(1)` as
`λ → ∞`, with `P`, `Q` as in `abs_coefficient_sub_linear_le`.
Project: `ChemotaxisBifurcation.NormalizedAsymptotic.coefficient_sub_linear_isBigO`,
with `coefficient`, `numerator`, `denominator` and `slope` unfolded. -/
theorem coefficient_sub_linear_isBigO (beta : ℝ) :
    (fun lambda : ℝ =>
        ((224 - 96 * beta) * lambda ^ 4
          + (192 - 152 * beta) * lambda ^ 3
          + (8 - 104 * beta - 16 * beta ^ 2) * lambda ^ 2
          + (96 - 28 * beta - 8 * beta ^ 2) * lambda
          + 56 + 11 * beta - beta ^ 2) /
          (96 * (1 + lambda) * (4 * lambda ^ 2 - 1)) - (7 / 12 - beta / 4) * lambda)
      =O[atTop] (fun _ => (1 : ℝ)) := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.NormalizedAsymptotic

/-! ## Wave 10A additions

Statements from the Wave 8–9 modules (`NoAtomLimit`, `GlobalBranch`,
`SpikeLimit`, `SpikeLimitBlowup` (namespace `SpikeLimit`), `MonotoneLocus`,
`WeakDerivative1D`, `RemainderFromJet`, `AmbientClosure`). Most are copied
verbatim (already Mathlib-only); in the rest the project definitions
`Eigenmodes.mode` (with `Eigenmodes.waveNumber`),
`GlobalBranch.GlobalAlternatives` (with `AltNoncompact`, `AltOtherTrivial`,
`AltComplement`) and `WeakDerivative1D.IsTestFunction` are unfolded by hand.
Each docstring names the project declaration and the unfolded definitions. -/

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.NoAtomLimit

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

/-- **Abstract no-atom criterion** (Remark 1.3(2), TeX lines 1005–1019): on a
pseudo-metric space, if `μ_i → μ` weakly along a nontrivial filter and for
every `ε > 0` some ball around `x` eventually has `μ_i`-mass at most `ε`, then
`μ {x} = 0`.
Project: `ChemotaxisBifurcation.NoAtomLimit.measure_singleton_eq_zero_of_small_balls`
(no project definition in the statement). -/
theorem measure_singleton_eq_zero_of_small_balls
    {X ι : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {l : Filter ι} [l.NeBot] {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    (hlim : Tendsto μs l (𝓝 μ)) (x : X)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 0 < r ∧ ∀ᶠ i in l, (μs i : Measure X) (Metric.ball x r) ≤ ENNReal.ofReal ε) :
    (μ : Measure X) {x} = 0 := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.NoAtomLimit

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.GlobalBranch

open Set Filter Topology MeasureTheory intervalIntegral

/-- **Alternative elimination** (Theorem 1.3(3), TeX lines 935–938 and 3306):
if the component `C` satisfies one of the three global alternatives
(non-compact; meets the trivial branch at another sensitivity; contains a
point `(χ, u* + w)` with `w ∈ W \ {0}`) and alternatives (ii) and (iii) fail,
then `C` is not compact.
Project: `ChemotaxisBifurcation.GlobalBranch.not_isCompact_of_alternatives`,
with `GlobalAlternatives`, `AltNoncompact`, `AltOtherTrivial` and
`AltComplement` unfolded. -/
theorem not_isCompact_of_alternatives {E : Type*} [TopologicalSpace E] [Add E] [Zero E]
    {C : Set (ℝ × E)} {chiStar : ℝ} {uStar : E} {W : Set E}
    (hAlt : ¬ IsCompact C ∨ (∃ chi : ℝ, chi ≠ chiStar ∧ (chi, uStar) ∈ C) ∨
      ∃ chi : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (chi, uStar + w) ∈ C)
    (hNotII : ¬ ∃ chi : ℝ, chi ≠ chiStar ∧ (chi, uStar) ∈ C)
    (hNotIII : ¬ ∃ chi : ℝ, ∃ w : E, w ∈ W ∧ w ≠ 0 ∧ (chi, uStar + w) ∈ C) :
    ¬ IsCompact C := by
  sorry

/-- **Compact slices** (Theorem 1.3(2), TeX lines 3163–3198): a closed
component in the closure of a set `S` whose bounded-sensitivity pieces are
relatively compact has compact bounded-sensitivity slices.
Project: `ChemotaxisBifurcation.GlobalBranch.isCompact_slice`
(no project definition in the statement). -/
theorem isCompact_slice {E : Type*} [TopologicalSpace E] {C S : Set (ℝ × E)}
    (hClosed : IsClosed C)
    (hCS : C ⊆ closure S)
    (hPrecompact : ∀ Xbar : ℝ, IsCompact (closure (S ∩ {p | p.1 ≤ Xbar})))
    (Xbar : ℝ) :
    IsCompact (C ∩ {p | p.1 ≤ Xbar}) := by
  sorry

/-- **Unbounded sensitivity from non-compactness** (Theorem 1.3(2), TeX lines
925–933 and 3163–3198): if every bounded-sensitivity slice is compact, a
non-compact component has unbounded sensitivity.
Project: `ChemotaxisBifurcation.GlobalBranch.unbounded_of_not_isCompact`
(no project definition in the statement). -/
theorem unbounded_of_not_isCompact {E : Type*} [TopologicalSpace E] {C : Set (ℝ × E)}
    (hSlice : ∀ Xbar : ℝ, IsCompact (C ∩ {p | p.1 ≤ Xbar}))
    (hNC : ¬ IsCompact C) :
    ∀ M : ℝ, ∃ p ∈ C, M < p.1 := by
  sorry

/-- Unbounded sensitivity as the display `sup {χ₀ : (χ₀,u) ∈ C} = +∞` (TeX lines
929–932, `E:bifurcation-branches`), supremum in the extended reals.
Project: `ChemotaxisBifurcation.GlobalBranch.sSup_eq_top_of_unbounded`
(no project definition in the statement). -/
theorem sSup_eq_top_of_unbounded {E : Type*} {C : Set (ℝ × E)}
    (hUnb : ∀ M : ℝ, ∃ p ∈ C, M < p.1) :
    sSup ((fun p : ℝ × E => (p.1 : EReal)) '' C) = ⊤ := by
  sorry

/-- **`cos(πx/L)` is strictly decreasing on `[0,L]`** (the `k = 1` case of TeX
lines 3275–3277).
Project: `ChemotaxisBifurcation.GlobalBranch.mode_one_strictAntiOn`, with
`Eigenmodes.mode L n x = Real.cos (waveNumber L n * x)` and
`Eigenmodes.waveNumber L n = n * π / L` unfolded (`n = 1`, kept as the cast
`((1 : ℕ) : ℝ)`). -/
theorem mode_one_strictAntiOn {L : ℝ} (hL : 0 < L) :
    StrictAntiOn (fun x : ℝ => Real.cos (((1 : ℕ) : ℝ) * Real.pi / L * x)) (Icc 0 L) := by
  sorry

/-- **Higher modes are not monotone, stably** (TeX lines 3270–3277): if
`u_j = c + s_j cos(nπx/L) + r_j` with `s_j ≠ 0`, `sup_{[0,L]} |r_j| ≤ ε_j |s_j|`,
`ε_j → 0` and `n ≥ 2`, the `u_j` cannot all be monotone on `[0,L]`.
Project: `ChemotaxisBifurcation.GlobalBranch.not_monotone_of_higher_mode`, with
`Eigenmodes.mode` and `Eigenmodes.waveNumber` unfolded. -/
theorem not_monotone_of_higher_mode {L c : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
    (u r : ℕ → ℝ → ℝ) (s ε : ℕ → ℝ)
    (hu : ∀ j x, u j x = c + s j * Real.cos ((n : ℝ) * Real.pi / L * x) + r j x)
    (hs : ∀ j, s j ≠ 0)
    (hr : ∀ j, ∀ x ∈ Icc 0 L, |r j x| ≤ ε j * |s j|)
    (hε : Tendsto ε atTop (𝓝 0))
    (hmono : ∀ j, MonotoneOn (u j) (Icc 0 L) ∨ AntitoneOn (u j) (Icc 0 L)) :
    False := by
  sorry

/-- **`cos(nπx/L)` is not monotone on `[0,L]` for `n ≥ 2`** (TeX line 3275),
neither nondecreasing nor nonincreasing.
Project: `ChemotaxisBifurcation.GlobalBranch.mode_not_monotoneOn`, with
`Eigenmodes.mode` and `Eigenmodes.waveNumber` unfolded. -/
theorem mode_not_monotoneOn {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n) :
    ¬ MonotoneOn (fun x : ℝ => Real.cos ((n : ℝ) * Real.pi / L * x)) (Icc 0 L) ∧
      ¬ AntitoneOn (fun x : ℝ => Real.cos ((n : ℝ) * Real.pi / L * x)) (Icc 0 L) := by
  sorry

/-- **Constant limits of monotone solutions occur only at the first mode**
(TeX lines 3265–3279): if monotone `u_j = c + s_j cos(nπx/L) + r_j` (`n ≥ 1`,
`s_j ≠ 0`, `|r_j| ≤ ε_j |s_j|` on `[0,L]`, `ε_j → 0`), then `n = 1`. The
local bifurcation representation is an explicit hypothesis.
Project: `ChemotaxisBifurcation.GlobalBranch.mode_eq_one_of_monotone_limit`,
with `Eigenmodes.mode` and `Eigenmodes.waveNumber` unfolded. -/
theorem mode_eq_one_of_monotone_limit {L c : ℝ} (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n)
    (u r : ℕ → ℝ → ℝ) (s ε : ℕ → ℝ)
    (hu : ∀ j x, u j x = c + s j * Real.cos ((n : ℝ) * Real.pi / L * x) + r j x)
    (hs : ∀ j, s j ≠ 0)
    (hr : ∀ j, ∀ x ∈ Icc 0 L, |r j x| ≤ ε j * |s j|)
    (hε : Tendsto ε atTop (𝓝 0))
    (hmono : ∀ j, MonotoneOn (u j) (Icc 0 L) ∨ AntitoneOn (u j) (Icc 0 L)) :
    n = 1 := by
  sorry

/-- **The first Fourier coefficient of a strictly decreasing profile is
positive** (TeX lines 3299–3305): for `g` continuous and strictly decreasing
on `[0,L]`, `∫_0^L g(x) cos(πx/L) dx > 0`.
Project: `ChemotaxisBifurcation.GlobalBranch.integral_mul_mode_one_pos`, with
`Eigenmodes.mode` and `Eigenmodes.waveNumber` unfolded (`n = 1`). -/
theorem integral_mul_mode_one_pos {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 L)) (hanti : StrictAntiOn g (Icc 0 L)) :
    0 < ∫ x in (0 : ℝ)..L, g x * Real.cos (((1 : ℕ) : ℝ) * Real.pi / L * x) := by
  sorry

/-- Mirror of `integral_mul_mode_one_pos` for strictly increasing profiles:
`∫_0^L g(x) cos(πx/L) dx < 0`.
Project: `ChemotaxisBifurcation.GlobalBranch.integral_mul_mode_one_neg`, with
`Eigenmodes.mode` and `Eigenmodes.waveNumber` unfolded (`n = 1`). -/
theorem integral_mul_mode_one_neg {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 L)) (hmono : StrictMonoOn g (Icc 0 L)) :
    ∫ x in (0 : ℝ)..L, g x * Real.cos (((1 : ℕ) : ℝ) * Real.pi / L * x) < 0 := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.GlobalBranch

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.SpikeLimit

open Set Filter Topology MeasureTheory
open scoped Interval

/-- **Lemma 5.1, TeX line 3458.** If `χ_n k a_n ≤ C` eventually, with
`a_n ≥ 0`, `k > 0` and `χ_n → ∞`, then `a_n → 0`.
Project: `ChemotaxisBifurcation.SpikeLimit.tendsto_zero_of_mul_le`
(no project definition in the statement). -/
theorem tendsto_zero_of_mul_le {chi a : ℕ → ℝ} {k C : ℝ} (hk : 0 < k)
    (hchi : Tendsto chi atTop atTop) (ha : ∀ n, 0 ≤ a n)
    (hle : ∀ᶠ n in atTop, chi n * k * a n ≤ C) :
    Tendsto a atTop (𝓝 0) := by
  sorry

/-- The pointwise three-term bound of TeX lines 3459–3462: for `0 < γ < r`,
`m > 0`, `ε, η > 0` there is `C ≥ 0` with `t^γ ≤ ε^γ + η t^r + C t^m` for all
`t ≥ 0`.
Project: `ChemotaxisBifurcation.SpikeLimit.rpow_le_three_term`
(no project definition in the statement). -/
theorem rpow_le_three_term {gamma m r ε η : ℝ} (hγ : 0 < gamma) (hγr : gamma < r)
    (hm : 0 < m) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ^ gamma ≤ ε ^ gamma + η * t ^ r + C * t ^ m := by
  sorry

/-- **Lemma 5.1, TeX lines 3470–3473.** If `V ≥ 0` on `[0,L]`, `μ > 0`,
`V_x(0) = V_x(L) = 0` and `V_x² - μ V²` is constant on `[0,L]`, then `V` is
constant.
Project: `ChemotaxisBifurcation.SpikeLimit.eq_const_of_energy`
(no project definition in the statement). -/
theorem eq_const_of_energy {L mu : ℝ} {V dV : ℝ → ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (hV : ContinuousOn V (Icc 0 L)) (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x)
    (hV0 : ∀ x ∈ Icc 0 L, 0 ≤ V x) (hbc0 : dV 0 = 0) (hbcL : dV L = 0)
    (hE : ∃ E, ∀ x ∈ Icc 0 L, dV x ^ 2 - mu * V x ^ 2 = E) :
    ∀ x ∈ Icc 0 L, V x = V 0 := by
  sorry

/-- **Lemma 5.1, TeX lines 3465–3469.** If `V` is `C¹` on `[0,L]`,
`V_x(x) = ∫_0^x (μ V - ν W)` (`E:lm2-v-limit`), `W ∈ L¹(0,L)` and `W V_x = 0`
a.e., then `V_x² - μ V²` is constant on `[0,L]`.
Project: `ChemotaxisBifurcation.SpikeLimit.energy_const`
(no project definition in the statement). -/
theorem energy_const {L mu nu : ℝ} {V dV W : ℝ → ℝ} (hL : 0 ≤ L)
    (hV : ContinuousOn V (Icc 0 L)) (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x)
    (hdV_cont : ContinuousOn dV (Icc 0 L)) (hW : IntervalIntegrable W volume 0 L)
    (heq : ∀ x ∈ Icc 0 L, dV x = ∫ y in (0 : ℝ)..x, (mu * V y - nu * W y))
    (hWdV : ∀ᵐ x, x ∈ Ioo 0 L → W x * dV x = 0) :
    ∃ E, ∀ x ∈ Icc 0 L, dV x ^ 2 - mu * V x ^ 2 = E := by
  sorry

/-- **Lemma 5.1, TeX lines 3464–3474: the limit is constant.** For `μ, ν > 0`,
`V ≥ 0` `C¹` on `[0,L]` with `V_x(L) = 0`, `W ∈ L¹(0,L)`,
`V_x(x) = ∫_0^x (μ V - ν W)` on `[0,L]` and `W V_x = 0` a.e. on `(0,L)`, there
is `c ≥ 0` with `V = (ν/μ) c` on `[0,L]` and `W = c` a.e. on `[0,L]`.
Project: `ChemotaxisBifurcation.SpikeLimit.limit_eq_const`
(no project definition in the statement). -/
theorem limit_eq_const {L mu nu : ℝ} {V dV W : ℝ → ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (hnu : 0 < nu) (hV : ContinuousOn V (Icc 0 L))
    (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x) (hdV_cont : ContinuousOn dV (Icc 0 L))
    (hV0 : ∀ x ∈ Icc 0 L, 0 ≤ V x) (hW : IntervalIntegrable W volume 0 L)
    (heq : ∀ x ∈ Icc 0 L, dV x = ∫ y in (0 : ℝ)..x, (mu * V y - nu * W y))
    (hbcL : dV L = 0) (hWdV : ∀ᵐ x, x ∈ Ioo 0 L → W x * dV x = 0) :
    ∃ c, 0 ≤ c ∧ (∀ x ∈ Icc 0 L, V x = nu / mu * c) ∧ ∀ᵐ x, x ∈ Icc 0 L → W x = c := by
  sorry

/-- **Theorem 1.4, the contradiction in the proof of `E:spiky-thm-eq2`** (TeX
lines 3527–3539): continuous `u_n ≥ 0` on `[0,L]` with `∫_0^L u_n ≤ L u*`,
`u* > 0`, maximum points `x_n → x*` and maxima `u_n(x_n) → ℓ > u*`, with
`x_n ∈ [a,b] ⊆ [0,L]` eventually, `u_n → U` uniformly on `[a,b]` and
`∫_p^q u_n^γ → c (q-p)` for `0 ≤ p ≤ q ≤ L` (`γ > 0`) is impossible. The
analytic inputs (Arzelà–Ascoli, Lemma 5.1) are hypotheses.
Project: `ChemotaxisBifurcation.SpikeLimit.blowup_contradiction` (module
`SpikeLimitBlowup`; no project definition in the statement). -/
theorem blowup_contradiction {L uStar gamma ell xstar a b c : ℝ} {u : ℕ → ℝ → ℝ}
    {x : ℕ → ℝ} {U : ℝ → ℝ} (hL : 0 < L) (huStar : 0 < uStar) (hγ : 0 < gamma)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ y ∈ Icc 0 L, 0 ≤ u n y)
    (hmass : ∀ n, ∫ y in (0 : ℝ)..L, u n y ≤ L * uStar)
    (hmax : ∀ n, IsMaxOn (u n) (Icc 0 L) (x n))
    (hxlim : Tendsto x atTop (𝓝 xstar)) (hell : Tendsto (fun n => u n (x n)) atTop (𝓝 ell))
    (hell_gt : uStar < ell) (hab : a < b) (habL : Icc a b ⊆ Icc 0 L)
    (hxab : ∀ᶠ n in atTop, x n ∈ Icc a b) (hU : ContinuousOn U (Icc a b))
    (hconv : TendstoUniformlyOn u U atTop (Icc a b))
    (hweak : ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
      Tendsto (fun n => ∫ y in p..q, u n y ^ gamma) atTop (𝓝 (c * (q - p)))) :
    False := by
  sorry

/-- **Theorem 1.4, the exponents of `E:spiky-thm-eq3`** (TeX lines 979–985,
3544–3549): for `α > 0` and `0 < γ < 1 + α`, `max{1, γ} < 1 + α` and
`(1+α)/γ > 1`.
Project: `ChemotaxisBifurcation.SpikeLimit.exponent_admissible` (module
`SpikeLimitBlowup`; no project definition in the statement). -/
theorem exponent_admissible {alpha gamma : ℝ} (halpha : 0 < alpha) (hγ : 0 < gamma)
    (hγα : gamma < 1 + alpha) : max 1 gamma < 1 + alpha ∧ 1 < (1 + alpha) / gamma := by
  sorry

/-- **Theorem 1.4, the bound `0 ≤ c ≤ (u*)^γ` in `E:spiky-thm-eq3`** (TeX lines
3546–3553): continuous `u_n ≥ 0` with `∫_0^L u_n^{1+α} ≤ L (u*)^{1+α}` and
`∫_0^L u_n^γ → c L`, `0 < γ ≤ 1 + α`, give `0 ≤ c ≤ (u*)^γ`.
Project: `ChemotaxisBifurcation.SpikeLimit.spike_limit_constant_le` (module
`SpikeLimitBlowup`; no project definition in the statement). -/
theorem spike_limit_constant_le {L uStar alpha gamma c : ℝ} {u : ℕ → ℝ → ℝ} (hL : 0 < L)
    (halpha : 0 < alpha) (huStar : 0 ≤ uStar) (hγ : 0 < gamma) (hγα : gamma ≤ 1 + alpha)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ y ∈ Icc 0 L, 0 ≤ u n y)
    (hmoment : ∀ n, ∫ y in (0 : ℝ)..L, u n y ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha))
    (hweak : Tendsto (fun n => ∫ y in (0 : ℝ)..L, u n y ^ gamma) atTop (𝓝 (c * L))) :
    0 ≤ c ∧ c ≤ uStar ^ gamma := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.SpikeLimit

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.MonotoneLocus

open Set Filter Topology

/-- **Uniqueness for the linear second-order system** (TeX lines 3251–3258): if
`y' = z`, `z' = a y` on `[0,L]` (one-sided at the ends), `a` continuous, and
`y(x₀) = z(x₀) = 0` for some `x₀ ∈ [0,L]`, then `y ≡ z ≡ 0` on `[0,L]`.
Project: `ChemotaxisBifurcation.MonotoneLocus.linear_eq_zero`
(no project definition in the statement). -/
theorem linear_eq_zero {L : ℝ} {y z a : ℝ → ℝ}
    (hy : ∀ x ∈ Icc 0 L, HasDerivWithinAt y (z x) (Icc 0 L) x)
    (hz : ∀ x ∈ Icc 0 L, HasDerivWithinAt z (a x * y x) (Icc 0 L) x)
    (ha : ContinuousOn a (Icc 0 L)) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc 0 L)
    (hy0 : y x₀ = 0) (hz0 : z x₀ = 0) :
    ∀ x ∈ Icc 0 L, y x = 0 ∧ z x = 0 := by
  sorry

/-- **Mean-value bound with Neumann data** (TeX lines 3213–3217): if
`g(0) = g(L) = 0` and `|g'| ≤ δ` on `[0,L]`, then `|g(x)| ≤ δ min(x, L-x)`.
Project: `ChemotaxisBifurcation.MonotoneLocus.abs_le_mul_min`
(no project definition in the statement). -/
theorem abs_le_mul_min {L δ : ℝ} {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc 0 L, HasDerivWithinAt g (g' x) (Icc 0 L) x)
    (h0 : g 0 = 0) (hL0 : g L = 0) (hbound : ∀ x ∈ Icc 0 L, |g' x| ≤ δ) :
    ∀ x ∈ Icc 0 L, |g x| ≤ δ * min x (L - x) := by
  sorry

/-- **Simple endpoint zeros give a linear margin** (TeX lines 3259–3264,
3291–3292): if `f(0) = f(L) = 0`, `f < 0` on `(0,L)`, `f'` is continuous on
`[0,L]` and `f'(0) ≠ 0 ≠ f'(L)`, then `f(x) ≤ -c min(x, L-x)` for some `c > 0`.
Project: `ChemotaxisBifurcation.MonotoneLocus.exists_margin`
(no project definition in the statement). -/
theorem exists_margin {L : ℝ} (hL : 0 < L) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 L, HasDerivWithinAt f (f' x) (Icc 0 L) x)
    (hf'c : ContinuousOn f' (Icc 0 L)) (h0 : f 0 = 0) (hL0 : f L = 0)
    (hneg : ∀ x ∈ Ioo 0 L, f x < 0) (hd0 : f' 0 ≠ 0) (hdL : f' L ≠ 0) :
    ∃ c > 0, ∀ x ∈ Icc 0 L, f x ≤ -c * min x (L - x) := by
  sorry

/-- **Openness, quantitative form**: if `f₀ ≤ -c min(x, L-x)` on `[0,L]`, both
`f₀` and `f` vanish at `0` and `L`, and `|f' - f₀'| ≤ δ < c` on `[0,L]`, then
`f < 0` on `(0,L)`.
Project: `ChemotaxisBifurcation.MonotoneLocus.neg_of_perturb`
(no project definition in the statement). -/
theorem neg_of_perturb {L c δ : ℝ} {f₀ f₀' f f' : ℝ → ℝ}
    (hf₀ : ∀ x ∈ Icc 0 L, HasDerivWithinAt f₀ (f₀' x) (Icc 0 L) x)
    (hf : ∀ x ∈ Icc 0 L, HasDerivWithinAt f (f' x) (Icc 0 L) x)
    (h00 : f₀ 0 = 0) (h0L : f₀ L = 0) (h0 : f 0 = 0) (hL0 : f L = 0)
    (hmargin : ∀ x ∈ Icc 0 L, f₀ x ≤ -c * min x (L - x))
    (hclose : ∀ x ∈ Icc 0 L, |f' x - f₀' x| ≤ δ) (hδc : δ < c) :
    ∀ x ∈ Ioo 0 L, f x < 0 := by
  sorry

/-- **Jordan's inequality on `[0,L]`**: `sin(πx/L) ≥ (2/L) min(x, L-x)` (TeX
line 3218).
Project: `ChemotaxisBifurcation.MonotoneLocus.two_div_mul_min_le_sin`
(no project definition in the statement). -/
theorem two_div_mul_min_le_sin {L x : ℝ} (hL : 0 < L) (hx : x ∈ Icc 0 L) :
    2 / L * min x (L - x) ≤ Real.sin (Real.pi / L * x) := by
  sorry

/-- Mirror of `exists_margin` for a positive function: `f > 0` on `(0,L)` with
simple endpoint zeros gives `-f(x) ≤ -c min(x, L-x)` for some `c > 0`.
Project: `ChemotaxisBifurcation.MonotoneLocus.exists_margin_pos`
(no project definition in the statement). -/
theorem exists_margin_pos {L : ℝ} (hL : 0 < L) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 L, HasDerivWithinAt f (f' x) (Icc 0 L) x)
    (hf'c : ContinuousOn f' (Icc 0 L)) (h0 : f 0 = 0) (hL0 : f L = 0)
    (hpos : ∀ x ∈ Ioo 0 L, 0 < f x) (hd0 : f' 0 ≠ 0) (hdL : f' L ≠ 0) :
    ∃ c > 0, ∀ x ∈ Icc 0 L, -f x ≤ -c * min x (L - x) := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.MonotoneLocus

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.WeakDerivative1D

open MeasureTheory Set Real Filter Topology Function
open scoped Interval ContDiff

/-- **du Bois-Reymond lemma.** If `h ∈ L¹(0,L)` and `∫₀ᴸ h φ' = 0` for every
`φ ∈ C_c^∞(0,L)` (smooth, compactly supported, `tsupport φ ⊆ (0,L)`), then `h`
is a.e. equal to a constant on `(0,L)`.
Project: `ChemotaxisBifurcation.WeakDerivative1D.ae_eq_const_of_integral_mul_deriv_eq_zero`,
with `IsTestFunction L φ = ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L`
unfolded. -/
theorem ae_eq_const_of_integral_mul_deriv_eq_zero {L : ℝ} (hL : 0 < L) {h : ℝ → ℝ}
    (hh : IntervalIntegrable h volume 0 L)
    (H : ∀ φ : ℝ → ℝ, (ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 L) →
      ∫ x in (0 : ℝ)..L, h x * deriv φ x = 0) :
    ∃ c : ℝ, ∀ᵐ x, x ∈ Ioo 0 L → h x = c := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.WeakDerivative1D

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.RemainderFromJet

open Filter Topology

/-- One mean-value step on the segment `[-|x|, |x|]`: if `φ' = ψ` and
`|ψ| ≤ B` there, then `|φ(x) - φ(0)| ≤ B |x|`.
Project: `ChemotaxisBifurcation.RemainderFromJet.abs_sub_le_of_deriv_bound`
(no project definition in the statement). -/
theorem abs_sub_le_of_deriv_bound (φ ψ : ℝ → ℝ) (x B : ℝ)
    (hd : ∀ t, |t| ≤ |x| → HasDerivAt φ (ψ t) t)
    (hb : ∀ t, |t| ≤ |x| → |ψ t| ≤ B) :
    |φ x - φ 0| ≤ B * |x| := by
  sorry

/-- Converse step for Eq. 2.43: a function differentiable at `0` with
`|φ s| ≤ K s²` near `0` has derivative `0` at `0`.
Project: `ChemotaxisBifurcation.RemainderFromJet.deriv_zero_of_sq_bound`
(no project definition in the statement). -/
theorem deriv_zero_of_sq_bound (φ : ℝ → ℝ) (d K δ : ℝ) (hδ : 0 < δ)
    (hd : HasDerivAt φ d 0) (hb : ∀ s, |s| ≤ δ → |φ s| ≤ K * s ^ 2) : d = 0 := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.RemainderFromJet

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.AmbientClosure

open Set Filter Topology MeasureTheory

/-- A continuous profile on `[0,L]` with `∫_0^L u = L u*` attains a value
`≥ u*` (TeX line 3121, `a = b = 0`).
Project: `ChemotaxisBifurcation.AmbientClosure.exists_ge_mean`
(no project definition in the statement). -/
theorem exists_ge_mean (L uStar : ℝ) (u : ℝ → ℝ) (hL : 0 < L)
    (hu : ContinuousOn u (Icc 0 L)) (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) :
    ∃ y ∈ Icc 0 L, uStar ≤ u y := by
  sorry

/-- For `a, b, α > 0`, a continuous positive profile on `[0,L]` with the
logistic mass identity `a ∫_0^L u = b ∫_0^L u^(1+α)` (`E:mass-identity`)
attains a value `≥ (a/b)^(1/α) = u*` (use of Lemma 4.1(1) at TeX line 3121).
Project: `ChemotaxisBifurcation.AmbientClosure.logistic_exists_ge_uStar`
(no project definition in the statement). -/
theorem logistic_exists_ge_uStar (a b alpha L : ℝ) (u : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hmass : a * ∫ x in (0 : ℝ)..L, u x = b * ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha)) :
    ∃ x ∈ Icc 0 L, (a / b) ^ (1 / alpha) ≤ u x := by
  sorry

/-- **Zero-sensitivity uniqueness, minimal model** (TeX line 3142): a `C²`
profile with `u_xx = 0` on `(0,L)`, `u_x(0) = 0` and `∫_0^L u = L u*` is
identically `u*` on `[0,L]`.
Project: `ChemotaxisBifurcation.AmbientClosure.minimal_zero_sensitivity_eq`
(no project definition in the statement). -/
theorem minimal_zero_sensitivity_eq (L uStar : ℝ) (u du ddu : ℝ → ℝ) (hL : 0 < L)
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hdu_cont : ContinuousOn du (Icc 0 L)) (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hstat : ∀ x ∈ Ioo 0 L, ddu x = 0) (hbc0 : du 0 = 0)
    (hmass : ∫ x in (0 : ℝ)..L, u x = L * uStar) :
    ∀ x ∈ Icc 0 L, u x = uStar := by
  sorry

/-- Nonnegativity is closed in `C(K, ℝ)` (compact-open topology).
Project: `ChemotaxisBifurcation.AmbientClosure.isClosed_setOf_forall_nonneg`
(no project definition in the statement). -/
theorem isClosed_setOf_forall_nonneg {K : Type*} [TopologicalSpace K] :
    IsClosed {f : C(K, ℝ) | ∀ x, 0 ≤ f x} := by
  sorry

/-- "`max f ≥ c`" is closed in `C(K, ℝ)` over a compact `K` (TeX line 3122:
uniform convergence gives `max ū ≥ u*`).
Project: `ChemotaxisBifurcation.AmbientClosure.isClosed_setOf_exists_ge`
(no project definition in the statement). -/
theorem isClosed_setOf_exists_ge {K : Type*} [TopologicalSpace K] [CompactSpace K] (c : ℝ) :
    IsClosed {f : C(K, ℝ) | ∃ x, c ≤ f x} := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.AmbientClosure

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.V2
open Real Set MeasureTheory

noncomputable def cosineCoeff (L : ℝ) (R : ℝ → ℝ) (k : ℕ) : ℝ :=
  (if k = 0 then 1 / L else 2 / L) * ∫ x in (0 : ℝ)..L, R x * cos (k * Real.pi * x / L)

noncomputable def signalRemainder (L mu : ℝ) (R : ℝ → ℝ) (k : ℕ) : ℝ :=
  cosineCoeff L R k / (mu + (k * Real.pi / L) ^ 2)

/-- Zero-mode signal normalization in the frozen v2 manuscript. -/
theorem signalRemainder_zero (L mu : ℝ) (R : ℝ → ℝ) :
    signalRemainder L mu R 0 = (mu * L)⁻¹ * ∫ x in (0 : ℝ)..L, R x := by
  sorry

/-- Positive-mode signal normalization in the frozen v2 manuscript. -/
theorem signalRemainder_pos (L mu : ℝ) (R : ℝ → ℝ) {k : ℕ} (hk : k ≠ 0) :
    signalRemainder L mu R k = 2 * (L * (mu + (k * Real.pi / L) ^ 2))⁻¹ *
      ∫ x in (0 : ℝ)..L, R x * cos (k * Real.pi * x / L) := by
  sorry

/-- Fourth-order signal estimates from an explicit uniform Taylor-source bound. -/
theorem signalRemainder_quartic {L mu C N : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    {R : ℝ → ℝ} (hR : ∀ x ∈ Icc 0 L, |R x| ≤ C * N ^ 4) :
    |signalRemainder L mu R 0| ≤ C * N ^ 4 / mu ∧
      ∀ k : ℕ, k ≠ 0 → |signalRemainder L mu R k| ≤
        2 * (C * N ^ 4) / (mu + (k * Real.pi / L) ^ 2) := by
  sorry

/-- Summability of signal coefficients from a uniform source bound and resolvent denominator. -/
theorem summable_norm_signalRemainder {L mu B : ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (hB0 : 0 ≤ B) {R : ℝ → ℝ} (hB : ∀ x ∈ Icc 0 L, |R x| ≤ B) :
    Summable fun k => ‖signalRemainder L mu R k‖ := by
  sorry

/-- Normalized population estimate from explicit source, flux, boundary and elliptic bounds. -/
theorem population_remainder_quartic {L C K N : ℝ} (hL : 0 < L) (k : ℕ) (hC : 0 ≤ C)
    {R0 R1 dR1 U V Vx : ℝ → ℝ}
    (hR0 : IntervalIntegrable R0 volume 0 L)
    (hR1c : ContinuousOn R1 (Icc 0 L))
    (hR1d : ∀ x ∈ Ioo 0 L, HasDerivAt R1 (dR1 x) x)
    (hdR1 : IntervalIntegrable dR1 volume 0 L)
    (hR0b : ∀ x ∈ Icc 0 L, |R0 x| ≤ C * |U x| ^ 4)
    (hR1b : ∀ x ∈ Icc 0 L, |R1 x| ≤ C * (|U x| + |V x|) ^ 3 * |Vx x|)
    (hVx0 : Vx 0 = 0) (hVxL : Vx L = 0)
    (hM : ∀ x ∈ Icc 0 L, |U x| + |V x| + |Vx x| ≤ K * N) :
    |cosineCoeff L (fun x => R0 x + dR1 x) k| ≤
      (if k = 0 then 1 / L else 2 / L) * (((L + k * Real.pi) * C * K ^ 4) * N ^ 4) := by
  sorry

/-- Strictly decreasing nonconstant profiles from the stationary power-flux ODE and weak order. -/
theorem general_m_strictAnti {χ μ ν γ β m L : ℝ} {u v y : ℝ → ℝ}
    (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hv_pos : ∀ x ∈ Icc 0 L, 0 < 1 + v x)
    (hu : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (χ * (u x ^ m / (1 + v x) ^ β) * y x) (Icc 0 L) x)
    (hv : ∀ x ∈ Icc 0 L, HasDerivWithinAt v (y x) (Icc 0 L) x)
    (hy : ∀ x ∈ Icc 0 L, HasDerivWithinAt y (μ * v x - ν * u x ^ γ) (Icc 0 L) x)
    (h0 : y 0 = 0) (hL : y L = 0) (hχ : 0 < χ)
    (horder : AntitoneOn u (Icc 0 L))
    (hnc : ¬ ∀ x ∈ Icc 0 L, u x = u 0) : StrictAntiOn u (Icc 0 L) := by
  sorry

/-- Strictly increasing nonconstant profiles from the stationary power-flux ODE and weak order. -/
theorem general_m_strictMono {χ μ ν γ β m L : ℝ} {u v y : ℝ → ℝ}
    (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hv_pos : ∀ x ∈ Icc 0 L, 0 < 1 + v x)
    (hu : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (χ * (u x ^ m / (1 + v x) ^ β) * y x) (Icc 0 L) x)
    (hv : ∀ x ∈ Icc 0 L, HasDerivWithinAt v (y x) (Icc 0 L) x)
    (hy : ∀ x ∈ Icc 0 L, HasDerivWithinAt y (μ * v x - ν * u x ^ γ) (Icc 0 L) x)
    (h0 : y 0 = 0) (hL : y L = 0) (hχ : 0 < χ)
    (horder : MonotoneOn u (Icc 0 L))
    (hnc : ¬ ∀ x ∈ Icc 0 L, u x = u 0) : StrictMonoOn u (Icc 0 L) := by
  sorry

/-- The stationary power-flux ODE excludes double signal-derivative zeros on a nonconstant profile. -/
theorem general_m_simple_zeros {χ μ ν γ β m L : ℝ} {u v y : ℝ → ℝ}
    (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hv_pos : ∀ x ∈ Icc 0 L, 0 < 1 + v x)
    (hu : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (χ * (u x ^ m / (1 + v x) ^ β) * y x) (Icc 0 L) x)
    (hv : ∀ x ∈ Icc 0 L, HasDerivWithinAt v (y x) (Icc 0 L) x)
    (hy : ∀ x ∈ Icc 0 L, HasDerivWithinAt y (μ * v x - ν * u x ^ γ) (Icc 0 L) x)
    (h0 : y 0 = 0) (hL : y L = 0)
    (hnc : ¬ ∀ x ∈ Icc 0 L, u x = u 0) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc 0 L) (hy0 : y x₀ = 0) : μ * v x₀ - ν * u x₀ ^ γ ≠ 0 := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.V2

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.V2Derivative
open Real

/-- The equilibrium equation cancels the leading derivative error. -/
theorem equilibrium_derivative_error (alpha beta eta s R Rs ds C : ℝ)
    (hs : s ≠ 0)
    (hroot : alpha * eta * s - beta * s ^ 3 + R = 0)
    (hderiv : ds = alpha * eta - 3 * beta * s ^ 2 + Rs)
    (hR : |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4))
    (hRs : |Rs| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3)) :
    |ds + 2 * alpha * eta| ≤ 4 * C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := by
  sorry

/-- A square-amplitude bound turns the mixed error into an explicit little-o majorant. -/
theorem equilibrium_derivative_error_window (alpha beta eta s R Rs ds C D : ℝ)
    (hs : s ≠ 0) (hC : 0 ≤ C)
    (hroot : alpha * eta * s - beta * s ^ 3 + R = 0)
    (hderiv : ds = alpha * eta - 3 * beta * s ^ 2 + Rs)
    (hR : |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4))
    (hRs : |Rs| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3))
    (hwindow : s ^ 2 ≤ D * |eta|) :
    |ds + 2 * alpha * eta| ≤ 4 * C * ((1 + D) * |eta| + D * |s|) * |eta| := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.V2Derivative

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.Campaign20261021
open Real Set MeasureTheory Filter Topology

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.StationaryMassIdentity.logistic_mass_identity_of_stationary`. -/
theorem mass_identity {L a b alpha : ℝ}
    (hL : 0 ≤ L) (halpha : 0 ≤ alpha) {u du ddu J dJ : ℝ → ℝ}
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ContinuousOn du (Icc 0 L))
    (hJ : ContinuousOn J (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hdJ : ∀ x ∈ Ioo 0 L, HasDerivAt J (dJ x) x)
    (heq : ∀ x ∈ Ioo 0 L, ddu x - dJ x + a * u x - b * u x ^ (1 + alpha) = 0)
    (hdu0 : du 0 = 0) (hduL : du L = 0) (hJ0 : J 0 = 0) (hJL : J L = 0) :
    a * (∫ x in (0 : ℝ)..L, u x) =
      b * (∫ x in (0 : ℝ)..L, u x ^ (1 + alpha)) := by
  sorry

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.SpikeEstimates.signal_testing_rpow_pos`. -/
theorem actual_signal_testing (L mu nu gamma q : ℝ) (u v dv ddv : ℝ → ℝ)
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
  sorry

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.SpikeEstimates.sup_le_of_derivative_power_bound`. -/
theorem actual_gronwall (L uStar A H m M : ℝ) (u du : ℝ → ℝ)
    (hL : 0 < L) (hA : 0 ≤ A) (hH : 0 ≤ H) (hm : 1 ≤ m)
    (hu : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo 0 L, |du x| ≤ A * u x ^ m + H)
    (hmean : ∫ x in (0 : ℝ)..L, u x ≤ L * uStar)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ (m - 1) ≤ M) :
    ∀ x ∈ Icc 0 L, u x ≤ (uStar + 1) * Real.exp (A * M + H * L) := by
  sorry

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.SignalCompactness.exists_C1_subsequence_of_W2q_bound`. -/
theorem actual_C1_extraction (L q W : ℝ) (v dv ddv : ℕ → ℝ → ℝ)
    (hL : 0 < L) (hq : 1 < q) (hW : 0 ≤ W)
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hddv : ∀ n, ContinuousOn (ddv n) (Icc 0 L))
    (hderiv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x)
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (hbound : ∀ n,
      (∫ x in (0 : ℝ)..L, |v n x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |dv n x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |ddv n x| ^ q) ^ (1 / q) ≤ W) :
    ∃ V DV : ℝ → ℝ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ContinuousOn V (Icc 0 L) ∧ ContinuousOn DV (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => v (phi n)) V atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => dv (phi n)) DV atTop (Icc 0 L) ∧
      ∀ x ∈ Ioo 0 L, HasDerivAt V (DV x) x := by
  sorry

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.SignalPowerMoment.W2q_bound_of_power_moment`. -/
theorem actual_arbitrary_r_W2q (L mu nu gamma r R : ℝ) (u v dv ddv : ℝ → ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma)
    (hr : 1 < r) (hgamma_r : gamma < r) (hR : 0 ≤ R)
    (hu : ContinuousOn u (Icc 0 L)) (hu0 : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hv : ContinuousOn v (Icc 0 L)) (hvpos : ∀ x ∈ Icc 0 L, 0 < v x)
    (hdv : ContinuousOn dv (Icc 0 L)) (hddv : ContinuousOn ddv (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x)
    (hderiv2 : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (heq : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ r ≤ R) :
    (∫ x in (0 : ℝ)..L, |v x| ^ (r / gamma)) ^ (1 / (r / gamma)) +
      (∫ x in (0 : ℝ)..L, |dv x| ^ (r / gamma)) ^ (1 / (r / gamma)) +
      (∫ x in (0 : ℝ)..L, |ddv x| ^ (r / gamma)) ^ (1 / (r / gamma)) ≤
      L ^ (1 / (r / gamma)) * ((R / L) ^ (1 / r)) ^ gamma *
        (nu / mu + 2 * nu + 2 * nu * L) := by
  sorry

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.SignalPowerMoment.exists_C1_subsequence_of_power_moment`. -/
theorem actual_arbitrary_r_C1_extraction (L mu nu gamma r R : ℝ)
    (u v dv ddv : ℕ → ℝ → ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma)
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
    (hmoment : ∀ n, ∫ x in (0 : ℝ)..L, u n x ^ r ≤ R) :
    ∃ V DV : ℝ → ℝ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ContinuousOn V (Icc 0 L) ∧ ContinuousOn DV (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => v (phi n)) V atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => dv (phi n)) DV atTop (Icc 0 L) ∧
      DV 0 = 0 ∧ DV L = 0 ∧ (∀ x ∈ Icc 0 L, 0 ≤ V x) ∧
      ∀ x ∈ Ioo 0 L, HasDerivAt V (DV x) x := by
  sorry

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.SignalDirectLimit.gradient_eq_zero_of_local_signal_ode`. -/
theorem gradient_zero {L mu : ℝ} {V dV : ℝ → ℝ}
    (hL : 0 < L) (hmu : 0 < mu)
    (_hV : ContinuousOn V (Icc 0 L)) (hdV : ContinuousOn dV (Icc 0 L))
    (hV0 : ∀ x ∈ Icc 0 L, 0 ≤ V x)
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x)
    (hlocal : ∀ x ∈ Ioo 0 L, dV x ≠ 0 → HasDerivAt dV (mu * V x) x)
    (hbc0 : dV 0 = 0) (hbcL : dV L = 0) :
    ∀ x ∈ Icc 0 L, dV x = 0 := by
  sorry

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.SignalDirectLimit.constant_limit_without_weak_source`. -/
theorem constant_signal_limit {L gamma m r beta kappa mu nu M Fb R : ℝ}
    {chi : ℕ → ℝ} {u du v dv ddv F : ℕ → ℝ → ℝ} {V dV : ℝ → ℝ}
    (hL : 0 < L) (hγ : 0 < gamma) (hγr : gamma < r) (hm : 0 < m) (hkappa : 0 < kappa)
    (hmu : 0 < mu) (hnu : 0 < nu) (hchi : Tendsto chi atTop atTop)
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
    (hV : ContinuousOn V (Icc 0 L)) (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x)
    (hdV_cont : ContinuousOn dV (Icc 0 L)) (hV0 : ∀ x ∈ Icc 0 L, 0 ≤ V x)
    (hdvconv : TendstoUniformlyOn dv dV atTop (Icc 0 L))
    (hvconv : TendstoUniformlyOn v V atTop (Icc 0 L))
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (hsignal : ∀ n x, x ∈ Ioo 0 L → ddv n x - mu * v n x + nu * u n x ^ gamma = 0)
    (hbc0 : dV 0 = 0) (hbcL : dV L = 0) :
    ∃ c, 0 ≤ c ∧ (∀ x ∈ Icc 0 L, V x = nu / mu * c) ∧
      (∀ x ∈ Icc 0 L, dV x = 0) ∧
      ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
        Tendsto (fun n => ∫ x in p..q, u n x ^ gamma) atTop (𝓝 (c * (q - p))) := by
  sorry

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.SpikeLimit.source_integral_tendsto_zero_of_nonzero_limit_gradient`. -/
theorem actual_source_vanishing {L p q p' q' gamma m r beta kappa M Fb R : ℝ}
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
  sorry

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.IntervalStrongPositivity.positive_of_nonnegative`. -/
theorem positive_profile {L : ℝ} (_hL : 0 < L)
    {u du a b : ℝ → ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (du x) (Icc 0 L) x)
    (hdu : ∀ x ∈ Icc 0 L,
      HasDerivWithinAt du (a x * u x + b x * du x) (Icc 0 L) x)
    (ha : ContinuousOn a (Icc 0 L)) (hb : ContinuousOn b (Icc 0 L))
    (h0 : du 0 = 0) (h1 : du L = 0)
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hpos : ∃ x ∈ Icc 0 L, 0 < u x) :
    ∀ x ∈ Icc 0 L, 0 < u x := by
  sorry

/-- New actual analytic consumer; full type governs scope. Project: `ChemotaxisBifurcation.rpow_quadratic_remainder`. -/
theorem actual_rpow_Taylor (u q : ℝ) (hu : 0 < u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ u / 2 →
      |(u+s)^q - u^q - q*u^(q-1)*s - q*(q-1)*u^(q-2)/2*s^2|
        ≤ C * |s|^3 := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.Campaign20261021

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.Campaign20261021
open Real Set MeasureTheory Filter Topology

/-- Actual original stationary-system constant-subsequence and all weak tests. -/
theorem classical_all_test_subsequence
    (L a b alpha gamma mu nu m beta r R : ℝ) (chi : ℕ → ℝ)
    (u du ddu v dv ddv dJ : ℕ → ℝ → ℝ)
    (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hmu : 0 < mu) (hnu : 0 < nu)
    (hm : 0 < m) (hbeta : 0 ≤ beta) (hr : 1 < r) (hgr : gamma < r) (hR : 0 ≤ R)
    (hchi : Tendsto chi atTop atTop)
    (huc : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hduc : ∀ n, ContinuousOn (du n) (Icc 0 L))
    (hvc : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hdvc : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hddvc : ∀ n, ContinuousOn (ddv n) (Icc 0 L))
    (hup : ∀ n x, x ∈ Icc 0 L → 0 < u n x)
    (hvp : ∀ n x, x ∈ Icc 0 L → 0 < v n x)
    (hdu : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (u n) (du n x) x)
    (hddu : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (du n) (ddu n x) x)
    (hdv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x)
    (hddv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (hdJ : ∀ n x, x ∈ Ioo 0 L →
      HasDerivAt (fun y => chi n*(u n y^m/(1+v n y)^beta)*dv n y) (dJ n x) x)
    (hpop : ∀ n x, x ∈ Ioo 0 L → ddu n x-dJ n x+a*u n x-b*u n x^(1+alpha)=0)
    (hsig : ∀ n x, x ∈ Ioo 0 L → ddv n x-mu*v n x+nu*u n x^gamma=0)
    (hu0 : ∀ n, du n 0=0) (huL : ∀ n, du n L=0)
    (hv0 : ∀ n, dv n 0=0) (hvL : ∀ n, dv n L=0)
    (hbound : ∀ n, ∫ x in (0 : ℝ)..L, u n x^r ≤ R) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ c : ℝ, 0 ≤ c ∧
      TendstoUniformlyOn (fun n => v (phi n)) (fun _ => nu/mu*c) atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => dv (phi n)) (fun _ => 0) atTop (Icc 0 L) ∧
      (∀ x y, 0 ≤ x → x ≤ y → y ≤ L →
        Tendsto (fun n => ∫ z in x..y, u (phi n) z^gamma) atTop (𝓝 (c*(y-x)))) ∧
      ∀ g : Lp ℝ (ENNReal.ofReal ((r/gamma)/(r/gamma-1))) ((Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume)),
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, u (phi n) x^gamma*g x
          ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume)) atTop
          (𝓝 (∫ x : Icc (0 : ℝ) L, c*g x ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume))) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, v (phi n) x*g x
          ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume)) atTop
          (𝓝 (∫ x : Icc (0 : ℝ) L, (nu/mu*c)*g x ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume))) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, dv (phi n) x*g x
          ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume)) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, ddv (phi n) x*g x
          ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume)) atTop (𝓝 0) := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.Campaign20261021

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.HolderCampaign20261021
open Real Set MeasureTheory

theorem logistic_uniform_norm_bound (L a b alpha m beta mu nu gamma X : ℝ)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hg : 0 < gamma) (hg1 : gamma ≤ 1+alpha) :
    ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
      ∀ (chi : ℝ) (u du ddu v dv ddv : ℝ → ℝ),
      (∀ x ∈ Icc 0 L, HasDerivWithinAt u (du x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt du (ddu x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt v (dv x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt dv (ddv x) (Icc 0 L) x) →
      ContinuousOn ddu (Icc 0 L) → ContinuousOn ddv (Icc 0 L) →
      (∀ x ∈ Ioo 0 L,
        ddu x-deriv (fun y => chi*(u y^m/(1+v y)^beta)*dv y) x+a*u x-b*u x^(1+alpha)=0) →
      du 0=0 → du L=0 → (∀ x ∈ Icc 0 L, 0 ≤ v x) → dv 0=0 → dv L=0 →
      (∀ x ∈ Ioo 0 L, ddv x-mu*v x+nu*u x^gamma=0) →
      |chi| ≤ X → (∀ x ∈ Icc 0 L, 0 < u x) → (∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y) →
      let norm := fun f df ddf : ℝ → ℝ =>
        sSup ((fun x => |f x|) '' Icc 0 L)+
        sSup ((fun x => |df x|) '' Icc 0 L)+
        sSup ((fun x => |ddf x|) '' Icc 0 L)+
        sSup {q : ℝ | ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L,
          x ≠ y ∧ q=|ddf y-ddf x|/|y-x|^theta}
      norm u du ddu ≤ C ∧ norm v dv ddv ≤ C := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.HolderCampaign20261021

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.HolderCampaign20261021
open Real Set MeasureTheory

theorem minimal_uniform_norm_bound (L m beta mu nu gamma X uStar : ℝ)
    (hL : 0 < L) (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
      ∀ (chi : ℝ) (u du ddu v dv ddv : ℝ → ℝ),
      (∀ x ∈ Icc 0 L, HasDerivWithinAt u (du x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt du (ddu x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt v (dv x) (Icc 0 L) x) →
      (∀ x ∈ Icc 0 L, HasDerivWithinAt dv (ddv x) (Icc 0 L) x) →
      ContinuousOn ddu (Icc 0 L) → ContinuousOn ddv (Icc 0 L) →
      (∀ x ∈ Ioo 0 L,
        ddu x-deriv (fun y => chi*(u y^m/(1+v y)^beta)*dv y) x=0) →
      du 0=0 → du L=0 → (∀ x ∈ Icc 0 L, 0 ≤ v x) → dv 0=0 → dv L=0 →
      (∀ x ∈ Ioo 0 L, ddv x-mu*v x+nu*u x^gamma=0) →
      |chi| ≤ X → (∀ x ∈ Icc 0 L, 0 < u x) → (∫ x in (0 : ℝ)..L, u x) = L*uStar →
      let norm := fun f df ddf : ℝ → ℝ =>
        sSup ((fun x => |f x|) '' Icc 0 L)+
        sSup ((fun x => |df x|) '' Icc 0 L)+
        sSup ((fun x => |ddf x|) '' Icc 0 L)+
        sSup {q : ℝ | ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L,
          x ≠ y ∧ q=|ddf y-ddf x|/|y-x|^theta}
      norm u du ddu ≤ C ∧ norm v dv ddv ≤ C := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.HolderCampaign20261021

namespace ChemotaxisBifurcationAudit.ChemotaxisBifurcation.ResponseJetCampaign20261021
open Real Set MeasureTheory Filter Topology

theorem actual_modal_derivative (L mu nu gamma uStar vStar : ℝ)
    (hL : 0 < L) (hu : 0 < uStar) (hmu : 0 < mu)
    (hsig : mu*vStar=nu*uStar^gamma)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc 0 L)) (k : ℕ)
    (V dV : ℝ → ℝ → ℝ)
    (hsol : ∀ᶠ t in 𝓝 (0 : ℝ),
      AbsolutelyContinuousOnInterval (V t) 0 L ∧
      (∀ x ∈ Ioo 0 L, HasDerivAt (V t) (dV t x) x) ∧
      AbsolutelyContinuousOnInterval (dV t) 0 L ∧ dV t 0=0 ∧ dV t L=0 ∧
      ∀ x ∈ Ioo 0 L, deriv (dV t) x-mu*(vStar+V t x)+nu*(uStar+t*w x)^gamma=0) :
    let coeff := fun f : ℝ → ℝ =>
      (if k=0 then 1/L else 2/L)*(∫ x in (0 : ℝ)..L, f x*cos ((k:ℝ)*Real.pi*x/L))
    HasDerivAt (fun t => coeff (V t))
      ((mu*gamma*vStar/uStar)/(mu+(k*Real.pi/L)^2)*coeff w) 0 := by
  sorry

end ChemotaxisBifurcationAudit.ChemotaxisBifurcation.ResponseJetCampaign20261021
