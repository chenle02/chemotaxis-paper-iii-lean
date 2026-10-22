module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.

Reused from the Paper III verification subtree, audited against the corrected
September 26 manuscript (source SHA recorded in data/source-baseline.json).
The arbitrary face flux at index i represents the physical face i + 1/2.

# Paper III -- exact conservation of the trapezoidal discrete mass

This file formalizes the telescoping assertion immediately after equation
(5.2), label `E:main-DIS-conservative`.  The face fluxes are arbitrary: only
the conservative endpoint weights and the interior flux differences matter.

The theorem is an exact finite-dimensional rate identity.  It does not assert
existence or differentiability of a semidiscrete trajectory; if a trajectory
satisfies the displayed node equations, linearity of differentiation identifies
the expression below with the derivative of its trapezoidal mass.
-/

public import Mathlib

@[expose] public section

namespace ChemotaxisBifurcation.ConservativeMass

open scoped BigOperators

/-- The weighted rate associated with the manuscript's trapezoidal mass.

For `N` mesh intervals, the interior nodes are `i + 1` with
`i in Finset.range (N - 1)`. -/
noncomputable def trapezoidalMassRate
    (h : ℝ) (N : ℕ) (nodeRate : ℕ → ℝ) : ℝ :=
  h * (nodeRate 0 / 2
    + ∑ i ∈ Finset.range (N - 1), nodeRate (i + 1)
    + nodeRate N / 2)

/-- The interior conservative flux differences telescope from the left face
to the right face. -/
theorem flux_difference_telescope (flux : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (flux (i + 1) - flux i)) =
      flux N - flux 0 := by
  exact Finset.sum_range_sub flux N

/-- Direct algebraic form of exact mass conservation for `N > 0` mesh
intervals.  The factors `2` at the endpoint nodes cancel their half control
volumes, while the interior flux differences telescope. -/
theorem conservative_flux_mass_rate_zero
    (h : ℝ) (flux : ℕ → ℝ) (N : ℕ) (hh : h ≠ 0) (_hN : 0 < N) :
    h * ((2 * flux 0 / h) / 2
      + ∑ i ∈ Finset.range (N - 1),
          (flux (i + 1) - flux i) / h
      + (-2 * flux (N - 1) / h) / 2) = 0 := by
  rw [← Finset.sum_div, flux_difference_telescope]
  field_simp
  ring

/-- Manuscript-facing form: any node-rate vector satisfying equation (5.2)
has zero trapezoidal mass rate. -/
theorem conservative_scheme_preserves_trapezoidal_mass
    (h : ℝ) (flux nodeRate : ℕ → ℝ) (N : ℕ)
    (hh : h ≠ 0) (hN : 0 < N)
    (hleft : nodeRate 0 = 2 * flux 0 / h)
    (hinterior : ∀ i < N - 1,
      nodeRate (i + 1) = (flux (i + 1) - flux i) / h)
    (hright : nodeRate N = -2 * flux (N - 1) / h) :
    trapezoidalMassRate h N nodeRate = 0 := by
  unfold trapezoidalMassRate
  rw [hleft, hright]
  have hinteriorSum :
      (∑ i ∈ Finset.range (N - 1), nodeRate (i + 1)) =
        ∑ i ∈ Finset.range (N - 1),
          (flux (i + 1) - flux i) / h := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hinterior i (Finset.mem_range.mp hi)
  rw [hinteriorSum]
  exact conservative_flux_mass_rate_zero h flux N hh hN

end ChemotaxisBifurcation.ConservativeMass
