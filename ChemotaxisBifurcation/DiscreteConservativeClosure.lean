module
public import ChemotaxisBifurcation.DiscreteLinearization

@[expose] public section

/-!
# Conservative reflected-stencil closure

This module identifies the nodewise divergence of the linearized face flux in
Equation 5.2 with the reflected population stencil.  The conservative scheme
has no logistic reaction, so its connection to the shared population residual
is made only when `logisticSlope = 0`, in particular for the fixed-mass model.

These are finite algebraic and directional-derivative statements.  They do not
assert existence of a semidiscrete trajectory or nonlinear stability.
-/

namespace ChemotaxisBifurcation.DiscreteLinearization

open DiscreteEigenmodes
open ChemotaxisBifurcation.Semidiscrete

noncomputable section

private theorem firstFace_left_eq
    (N : ℕ) (hN : 0 < N) (i : Grid N) (hi0 : i.val = 0) :
    faceLeft (firstFace N hN) = i := by
  apply Fin.ext
  simp [faceLeft, firstFace, hi0]

private theorem firstFace_right_eq_prev
    (N : ℕ) (hN : 0 < N) (i : Grid N) (hi0 : i.val = 0) :
    faceRight (firstFace N hN) = reflectedPrev N hN i := by
  apply Fin.ext
  simp [faceRight, firstFace, reflectedPrev, hi0]

private theorem firstFace_right_eq_next
    (N : ℕ) (hN : 0 < N) (i : Grid N) (hi0 : i.val = 0) :
    faceRight (firstFace N hN) = reflectedNext N hN i := by
  apply Fin.ext
  simp [faceRight, firstFace, reflectedNext, hi0, (Nat.ne_of_gt hN).symm]

private theorem lastFace_right_eq
    (N : ℕ) (hN : 0 < N) (i : Grid N) (hiN : i.val = N) :
    faceRight (lastFace N hN) = i := by
  apply Fin.ext
  simp [faceRight, lastFace, hiN]
  omega

private theorem lastFace_left_eq_prev
    (N : ℕ) (hN : 0 < N) (i : Grid N)
    (hi0 : i.val ≠ 0) (hiN : i.val = N) :
    faceLeft (lastFace N hN) = reflectedPrev N hN i := by
  apply Fin.ext
  simp [faceLeft, lastFace, reflectedPrev, hi0, hiN, Nat.ne_of_gt hN]

private theorem lastFace_left_eq_next
    (N : ℕ) (hN : 0 < N) (i : Grid N) (hiN : i.val = N) :
    faceLeft (lastFace N hN) = reflectedNext N hN i := by
  apply Fin.ext
  simp [faceLeft, lastFace, reflectedNext, hiN]

private theorem rightFace_left_eq
    (N : ℕ) (i : Grid N) (hiN : i.val ≠ N) :
    faceLeft (rightFaceOfInterior N i hiN) = i := by
  apply Fin.ext
  simp [faceLeft, rightFaceOfInterior]

private theorem rightFace_right_eq_next
    (N : ℕ) (hN : 0 < N) (i : Grid N) (hiN : i.val ≠ N) :
    faceRight (rightFaceOfInterior N i hiN) = reflectedNext N hN i := by
  apply Fin.ext
  simp [faceRight, rightFaceOfInterior, reflectedNext, hiN]

private theorem leftFace_right_eq
    (N : ℕ) (i : Grid N) (hi0 : i.val ≠ 0) :
    faceRight (leftFaceOfInterior N i hi0) = i := by
  apply Fin.ext
  simp [faceRight, leftFaceOfInterior]
  omega

private theorem leftFace_left_eq_prev
    (N : ℕ) (hN : 0 < N) (i : Grid N) (hi0 : i.val ≠ 0) :
    faceLeft (leftFaceOfInterior N i hi0) = reflectedPrev N hN i := by
  apply Fin.ext
  simp [faceLeft, leftFaceOfInterior, reflectedPrev, hi0]

/-- At every grid node, including both reflected endpoints, the divergence of
the linearized conservative face flux is the shared reflected population
stencil without a logistic reaction term. -/
theorem linearizedConservativeNodeRate_eq_reflected
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ) (hN : 0 < N)
    (phi psi : GridFunction N) (i : Grid N) (hL : L ≠ 0) :
    linearizedConservativeNodeRate p beta chi L N hN phi psi i =
      -(reflectedNegLaplacian L N hN phi i) +
        chi * p.mobilityB0 beta * reflectedNegLaplacian L N hN psi i := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmesh : meshWidth L N ≠ 0 := by
    exact div_ne_zero hL hNR
  by_cases hi0 : i.val = 0
  · have hleft := firstFace_left_eq N hN i hi0
    have hrightPrev := firstFace_right_eq_prev N hN i hi0
    have hrightNext := firstFace_right_eq_next N hN i hi0
    unfold linearizedConservativeNodeRate
    rw [dif_pos hi0]
    unfold linearizedFaceFlux
    rw [hleft, hrightPrev]
    simp only [reflectedNegLaplacian, LinearMap.coe_mk, AddHom.coe_mk]
    unfold reflectedNegLaplacianApply
    rw [← hrightPrev, ← hrightNext]
    field_simp [hmesh]
    ring
  · by_cases hiN : i.val = N
    · have hright := lastFace_right_eq N hN i hiN
      have hleftPrev := lastFace_left_eq_prev N hN i hi0 hiN
      have hleftNext := lastFace_left_eq_next N hN i hiN
      unfold linearizedConservativeNodeRate
      rw [dif_neg hi0, dif_pos hiN]
      unfold linearizedFaceFlux
      rw [hright, hleftPrev]
      simp only [reflectedNegLaplacian, LinearMap.coe_mk, AddHom.coe_mk]
      unfold reflectedNegLaplacianApply
      rw [← hleftPrev, ← hleftNext]
      field_simp [hmesh]
      ring
    · have hrightLeft := rightFace_left_eq N i hiN
      have hrightRight := rightFace_right_eq_next N hN i hiN
      have hleftRight := leftFace_right_eq N i hi0
      have hleftLeft := leftFace_left_eq_prev N hN i hi0
      unfold linearizedConservativeNodeRate
      rw [dif_neg hi0, dif_neg hiN]
      unfold linearizedFaceFlux
      rw [hrightLeft, hrightRight, hleftRight, hleftLeft]
      simp only [reflectedNegLaplacian, LinearMap.coe_mk, AddHom.coe_mk]
      unfold reflectedNegLaplacianApply
      field_simp [hmesh]
      ring

/-- The conservative reflected stencil is the shared population residual
exactly when the logistic reaction slope vanishes. -/
theorem linearizedConservativeNodeRate_eq_populationResidual_of_slope_zero
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ) (hN : 0 < N)
    (phi psi : GridFunction N) (i : Grid N) (hL : L ≠ 0)
    (hslope : p.logisticSlope = 0) :
    linearizedConservativeNodeRate p beta chi L N hN phi psi i =
      populationResidual p beta chi L N hN phi psi i := by
  rw [linearizedConservativeNodeRate_eq_reflected p beta chi L N hN phi psi i hL]
  unfold populationResidual
  rw [hslope]
  ring

theorem fixedMass_logisticSlope_eq_zero
    (p : PhysicalParams) (hp : p.FixedMassAdmissible) :
    p.logisticSlope = 0 := by
  simp [PhysicalParams.logisticSlope, hp.1]

/-- The fixed-mass assumptions supply the zero-reaction boundary required for
the conservative and shared population linearizations to agree. -/
theorem linearizedConservativeNodeRate_eq_populationResidual_fixedMass
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ) (hN : 0 < N)
    (phi psi : GridFunction N) (i : Grid N) (hL : L ≠ 0)
    (hp : p.FixedMassAdmissible) :
    linearizedConservativeNodeRate p beta chi L N hN phi psi i =
      populationResidual p beta chi L N hN phi psi i := by
  exact linearizedConservativeNodeRate_eq_populationResidual_of_slope_zero
    p beta chi L N hN phi psi i hL (fixedMass_logisticSlope_eq_zero p hp)

/-- The literal conservative node rate has the shared population residual as
its directional derivative in the fixed-mass model. -/
theorem conservativeNodeRate_directionalDerivative_eq_populationResidual_fixedMass
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ) (hN : 0 < N)
    (phi psi : GridFunction N) (i : Grid N) (hL : L ≠ 0)
    (hp : p.FixedMassAdmissible) :
    HasDerivAt
      (fun t => conservativeNodeRate p beta chi L N hN
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i)
      (populationResidual p beta chi L N hN phi psi i) 0 := by
  have hpositive := PhysicalModeGuards.fixedMass_positive_parameters p hp
  have hderiv := conservativeNodeRate_directionalDerivative p beta chi L N hN
    phi psi i hpositive.u_pos (PhysicalModeGuards.signalOffset_pos p hpositive)
  rw [linearizedConservativeNodeRate_eq_populationResidual_fixedMass
    p beta chi L N hN phi psi i hL hp] at hderiv
  exact hderiv

/-- For every represented cosine mode, the directional derivative of the
literal conservative scheme is the same finite modal growth vector used by
the threshold chain. -/
theorem conservative_coupled_mode_directionalDerivative
    (p : PhysicalParams) (beta chi L : ℝ) (N n : ℕ)
    (hL : L ≠ 0) (hN : 0 < N) (hnN : n ≤ N)
    (hden : p.mu + discLam L n N ≠ 0)
    (hp : p.FixedMassAdmissible) :
    let lam := discLam L n N
    let phi := discreteCosineMode N n
    let psi := Eigenmodes.ellipticCoefficient p.signalC1Physical p.mu lam • phi
    ∀ i : Grid N,
      HasDerivAt
        (fun t => conservativeNodeRate p beta chi L N hN
          (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i)
        (((Eigenmodes.growthRate (chi * p.mobilityB0 beta)
          p.signalC1Physical p.mu p.logisticSlope lam) • phi) i) 0 := by
  dsimp only
  intro i
  have hderiv :=
    conservativeNodeRate_directionalDerivative_eq_populationResidual_fixedMass
      p beta chi L N hN (discreteCosineMode N n)
        (Eigenmodes.ellipticCoefficient p.signalC1Physical p.mu (discLam L n N) •
          discreteCosineMode N n) i hL hp
  have hpopulation := (discrete_coupled_mode_residuals
    p beta chi L N n hL hN hnN hden).2
  rw [hpopulation] at hderiv
  exact hderiv

end

end ChemotaxisBifurcation.DiscreteLinearization
