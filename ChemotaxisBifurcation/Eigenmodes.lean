module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
Reused from the Paper III finite-verification subtree; historical numbering
is not evidence of current manuscript coverage.

# Concrete Neumann eigenmodes and linearized substitution

This module proves the cosine derivative, endpoint and coupled-equation
identities used by the current modal linearization. It does not assert spectral
completeness or construct an unbounded PDE operator.
-/

public import Mathlib

@[expose] public section

namespace ChemotaxisBifurcation.Eigenmodes

/-- Wave number `n*pi/L` of the `n`th Neumann cosine mode. -/
noncomputable def waveNumber (L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.pi / L

/-- Continuum eigenvalue `(n*pi/L)^2`. -/
noncomputable def eigenvalue (L : ℝ) (n : ℕ) : ℝ :=
  waveNumber L n ^ 2

/-- The `n`th Neumann cosine mode on `(0,L)`. -/
noncomputable def mode (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos (waveNumber L n * x)

/-- First derivative of a cosine mode. -/
theorem hasDerivAt_mode (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (mode L n)
      (-Real.sin (waveNumber L n * x) * waveNumber L n) x := by
  unfold mode
  have h := (Real.hasDerivAt_cos (waveNumber L n * x)).comp x
    ((hasDerivAt_id x).const_mul (waveNumber L n))
  simpa only [Function.comp_def, id_eq, mul_one, neg_mul] using h

/-- The second derivative is `-lambda_n` times the mode. -/
theorem second_deriv_mode (L : ℝ) (n : ℕ) (x : ℝ) :
    deriv (fun y => deriv (mode L n) y) x =
      -eigenvalue L n * mode L n x := by
  have hfirst : (fun y => deriv (mode L n) y) =
      fun y => -Real.sin (waveNumber L n * y) * waveNumber L n := by
    funext y
    exact (hasDerivAt_mode L n y).deriv
  rw [hfirst]
  have hinner : HasDerivAt (fun y : ℝ => waveNumber L n * y)
      (waveNumber L n) x :=
    by simpa using (hasDerivAt_id x).const_mul (waveNumber L n)
  have hsin := (Real.hasDerivAt_sin (waveNumber L n * x)).comp x hinner
  have hscaled := hsin.neg.mul_const (waveNumber L n)
  have hd := hscaled.deriv
  change deriv (fun y => -Real.sin (waveNumber L n * y) * waveNumber L n) x =
    -(Real.cos (waveNumber L n * x) * waveNumber L n) * waveNumber L n at hd
  rw [hd]
  unfold eigenvalue mode
  ring

/-- The cosine modes satisfy the two Neumann boundary conditions. -/
theorem mode_neumann_boundary (L : ℝ) (n : ℕ) (hL : L ≠ 0) :
    deriv (mode L n) 0 = 0 ∧ deriv (mode L n) L = 0 := by
  constructor
  · rw [(hasDerivAt_mode L n 0).deriv]
    simp
  · rw [(hasDerivAt_mode L n L).deriv]
    have hphase : waveNumber L n * L = (n : ℝ) * Real.pi := by
      unfold waveNumber
      field_simp
    rw [hphase, Real.sin_nat_mul_pi]
    simp

/-- Manuscript coefficient relating the elliptic `v` mode to the `u` mode. -/
noncomputable def ellipticCoefficient (rho mu lam : ℝ) : ℝ :=
  rho / (mu + lam)

/-- Growth rate obtained after eliminating the elliptic mode. Here `chem` is
the full chemotactic prefactor, `rho = nu*gamma*(u*)^(gamma-1)`, and `reaction`
is `a*alpha`. -/
noncomputable def growthRate (chem rho mu reaction lam : ℝ) : ℝ :=
  -lam + chem * rho * lam / (mu + lam) - reaction

/-- Algebraic substitution of `u = phi` and
`v = rho/(mu+lambda) * phi` into both equations of the coupled linearization.
The hypothesis `phiXX = -lambda*phi` is supplied by `second_deriv_mode` for the
actual cosine mode. -/
theorem coupled_mode_substitution (chem rho mu reaction lam phi phiXX : ℝ)
    (hdenom : mu + lam ≠ 0) (hphi : phiXX = -lam * phi) :
    ellipticCoefficient rho mu lam * phiXX -
        mu * (ellipticCoefficient rho mu lam * phi) + rho * phi = 0 ∧
      phiXX - chem *
          (mu * (ellipticCoefficient rho mu lam * phi) - rho * phi) -
        reaction * phi = growthRate chem rho mu reaction lam * phi := by
  constructor
  · unfold ellipticCoefficient
    rw [hphi]
    field_simp
    ring
  · unfold ellipticCoefficient growthRate
    rw [hphi]
    field_simp
    ring

/-- Pointwise coupled-mode calculation for the actual Neumann cosine mode. -/
theorem cosine_mode_linearized_residuals (L : ℝ) (n : ℕ)
    (chem rho mu reaction x : ℝ) (hmu : 0 < mu) :
    let lam := eigenvalue L n
    let phi := mode L n x
    let phiXX := deriv (fun y => deriv (mode L n) y) x
    ellipticCoefficient rho mu lam * phiXX -
        mu * (ellipticCoefficient rho mu lam * phi) + rho * phi = 0 ∧
      phiXX - chem *
          (mu * (ellipticCoefficient rho mu lam * phi) - rho * phi) -
        reaction * phi = growthRate chem rho mu reaction lam * phi := by
  dsimp only
  apply coupled_mode_substitution
  · have hlam : 0 ≤ eigenvalue L n := sq_nonneg _
    positivity
  · exact second_deriv_mode L n x

end ChemotaxisBifurcation.Eigenmodes
