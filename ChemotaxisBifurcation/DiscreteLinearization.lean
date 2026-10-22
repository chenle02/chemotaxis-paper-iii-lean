module
public import ChemotaxisBifurcation.DiscreteEigenmodes
public import ChemotaxisBifurcation.LogisticDerivatives
public import ChemotaxisBifurcation.SignalDerivatives
public import ChemotaxisBifurcation.PhysicalLinearRegime
public import ChemotaxisBifurcation.SemidiscreteLimit

@[expose] public section

/-!
# Finite modal linearization of the reflected schemes

This module connects the concrete reflected stencil to the two first-order
population--signal equations.  Directional derivatives of the nonlinear
schemes are proved below this modal layer; no ODE trajectory or nonlinear
stability statement is made.
-/

namespace ChemotaxisBifurcation.DiscreteLinearization

open DiscreteEigenmodes
open ChemotaxisBifurcation.Semidiscrete
open scoped Topology

noncomputable section

def constantGrid (N : ℕ) (c : ℝ) : GridFunction N := fun _ => c

def affineGrid (N : ℕ) (base : ℝ) (direction : GridFunction N) (t : ℝ) :
    GridFunction N := fun i => base + t * direction i

/-- The paper's `Delta_h`, with sign opposite to the positive reflected
operator used for the spectral proof. -/
def reflectedLaplacian (L : ℝ) (N : ℕ) (hN : 0 < N) :
    GridFunction N →ₗ[ℝ] GridFunction N :=
  -(reflectedNegLaplacian L N hN)

/-- Centered reflected first difference from Equation 5.1. It vanishes at the
two endpoints because both reflected neighbors coincide there. -/
def centeredGradient (L : ℝ) (N : ℕ) (hN : 0 < N) :
    GridFunction N →ₗ[ℝ] GridFunction N where
  toFun u := fun i =>
    (u (reflectedNext N hN i) - u (reflectedPrev N hN i)) /
      (2 * meshWidth L N)
  map_add' u v := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem reflectedLaplacian_constant (L : ℝ) (N : ℕ) (hN : 0 < N) (c : ℝ) :
    reflectedLaplacian L N hN (constantGrid N c) = 0 := by
  funext i
  change -((2 * c - c - c) / meshWidth L N ^ 2) = 0
  ring

theorem centeredGradient_constant (L : ℝ) (N : ℕ) (hN : 0 < N) (c : ℝ) :
    centeredGradient L N hN (constantGrid N c) = 0 := by
  funext i
  unfold centeredGradient constantGrid
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  ring

theorem linearMap_affine_apply_hasDerivAt
    (N : ℕ) (T : GridFunction N →ₗ[ℝ] GridFunction N)
    (base : ℝ) (direction : GridFunction N) (i : Grid N)
    (hconst : T (constantGrid N base) = 0) :
    HasDerivAt (fun t => T (affineGrid N base direction t) i)
      (T direction i) 0 := by
  have hdecomp : ∀ t : ℝ,
      affineGrid N base direction t =
        constantGrid N base + t • direction := by
    intro t
    funext j
    simp [affineGrid, constantGrid]
  have hfun : (fun t => T (affineGrid N base direction t) i) =
      fun t => t * T direction i := by
    funext t
    rw [hdecomp, map_add, map_smul, hconst]
    simp
  rw [hfun]
  simpa using (hasDerivAt_id 0).mul_const (T direction i)

theorem linearMap_affine_apply_eq_mul
    (N : ℕ) (T : GridFunction N →ₗ[ℝ] GridFunction N)
    (base : ℝ) (direction : GridFunction N) (i : Grid N)
    (hconst : T (constantGrid N base) = 0) (t : ℝ) :
    T (affineGrid N base direction t) i = t * T direction i := by
  have hdecomp : affineGrid N base direction t =
      constantGrid N base + t • direction := by
    funext j
    simp [affineGrid, constantGrid]
  rw [hdecomp, map_add, map_smul, hconst]
  simp

theorem scalarAffine_hasDerivAt (base slope : ℝ) :
    HasDerivAt (fun t : ℝ => base + t * slope) slope 0 := by
  simpa using ((hasDerivAt_id 0).mul_const slope).const_add base

noncomputable def mobilityPower
    (power beta u v : ℝ) : ℝ :=
  u ^ power * (1 + v) ^ (-beta)

theorem mobilityPower_at_equilibrium_eq_B0
    (p : PhysicalParams) (beta : ℝ) (hw : 0 < p.signalOffset) :
    mobilityPower p.m beta p.uStar p.vStar = p.mobilityB0 beta := by
  unfold mobilityPower PhysicalParams.mobilityB0
  have hw' : 0 ≤ 1 + p.vStar := by
    simpa [PhysicalParams.signalOffset] using hw.le
  rw [Real.rpow_neg hw']
  unfold PhysicalParams.signalOffset
  rfl

theorem mobilityPower_affine_hasDerivAt
    (power beta u v du dv : ℝ) (hu : 0 < u) (hw : 0 < 1 + v) :
    HasDerivAt
      (fun t => mobilityPower power beta (u + t * du) (v + t * dv))
      (power * u ^ (power - 1) * du * (1 + v) ^ (-beta) +
        u ^ power * ((-beta) * (1 + v) ^ (-beta - 1) * dv)) 0 := by
  have huinner : HasDerivAt (fun t : ℝ => u + t * du) du 0 := by
    exact scalarAffine_hasDerivAt u du
  have hwinner : HasDerivAt (fun t : ℝ => 1 + (v + t * dv)) dv 0 := by
    rw [show (fun t : ℝ => 1 + (v + t * dv)) =
      fun t => (1 + v) + t * dv by funext t; ring]
    exact scalarAffine_hasDerivAt (1 + v) dv
  have hupow := HasDerivAt.comp_of_eq (x := (0 : ℝ)) (y := u)
    (rpow_hasDerivAt power u hu) huinner (by simp)
  have hwpow := HasDerivAt.comp_of_eq (x := (0 : ℝ)) (y := 1 + v)
    (rpow_hasDerivAt (-beta) (1 + v) hw) hwinner (by simp)
  have h := hupow.mul hwpow
  have hvalue :
      power * u ^ (power - 1) * du * (1 + v) ^ (-beta) +
          u ^ power * ((-beta) * (1 + v) ^ (-beta - 1) * dv) =
        power * u ^ (power - 1) * du * (1 + v) ^ (-beta) +
          -(u ^ power * (beta * (1 + v) ^ (-beta - 1) * dv)) := by ring
  rw [hvalue]
  have hev : (fun t => mobilityPower power beta (u + t * du) (v + t * dv))
      =ᶠ[𝓝 0] (((fun y => y ^ power) ∘ fun t => u + t * du) *
        (fun y => y ^ (-beta)) ∘ fun t => 1 + (v + t * dv)) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have h' := h.congr_of_eventuallyEq hev
  exact h'.congr_deriv (by simp)

theorem coefficient_mul_two_linear_hasDerivAt
    (f : ℝ → ℝ) (f' a b : ℝ) (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun t => f t * (t * a) * (t * b)) 0 0 := by
  have ha : HasDerivAt (fun t : ℝ => t * a) a 0 := by
    simpa using (hasDerivAt_id 0).mul_const a
  have hb : HasDerivAt (fun t : ℝ => t * b) b 0 := by
    simpa using (hasDerivAt_id 0).mul_const b
  change HasDerivAt ((f * fun t : ℝ => t * a) * fun t => t * b) 0 0
  simpa only [Pi.mul_apply, zero_mul, add_zero, mul_zero] using (hf.mul ha).mul hb

theorem coefficient_mul_zero_value_hasDerivAt
    (f g : ℝ → ℝ) (f' g' : ℝ)
    (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0)
    (hg0 : g 0 = 0) :
    HasDerivAt (fun t => f t * g t) (f 0 * g') 0 := by
  change HasDerivAt (f * g) (f 0 * g') 0
  have h := hf.mul hg
  rw [hg0] at h
  simpa only [mul_zero, zero_mul, zero_add] using h

noncomputable def signalDefect
    (p : PhysicalParams) (u v : ℝ) : ℝ :=
  p.mu * v - p.nu * u ^ p.gamma

theorem signalDefect_at_equilibrium
    (p : PhysicalParams) (heq : p.SignalEquilibrium) :
    signalDefect p p.uStar p.vStar = 0 := by
  unfold PhysicalParams.SignalEquilibrium at heq
  unfold signalDefect
  linarith

theorem signalDefect_affine_hasDerivAt
    (p : PhysicalParams) (du dv : ℝ) (hu : 0 < p.uStar) :
    HasDerivAt
      (fun t => signalDefect p (p.uStar + t * du) (p.vStar + t * dv))
      (p.mu * dv - p.signalC1Physical * du) 0 := by
  have huinner : HasDerivAt (fun t : ℝ => p.uStar + t * du) du 0 := by
    exact scalarAffine_hasDerivAt p.uStar du
  have hvinner : HasDerivAt (fun t : ℝ => p.vStar + t * dv) dv 0 := by
    exact scalarAffine_hasDerivAt p.vStar dv
  have hvterm := hvinner.const_mul p.mu
  have huterm := HasDerivAt.comp_of_eq (x := (0 : ℝ)) (y := p.uStar)
    (signal_source_hasDerivAt p.nu p.gamma p.uStar hu) huinner (by simp)
  have h := hvterm.sub huterm
  have hvalue : p.mu * dv - p.signalC1Physical * du =
      p.mu * dv - p.nu * (p.gamma * (p.uStar ^ (p.gamma - 1) * du)) := by
    unfold PhysicalParams.signalC1Physical
    ring
  rw [hvalue]
  have hev :
      (fun t => signalDefect p (p.uStar + t * du) (p.vStar + t * dv)) =ᶠ[𝓝 0]
        ((fun y => p.mu * (p.vStar + y * dv)) -
          (fun y => p.nu * y ^ p.gamma) ∘ fun t => p.uStar + t * du) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have h' := h.congr_of_eventuallyEq hev
  exact h'.congr_deriv (by ring)

noncomputable def populationReaction
    (p : PhysicalParams) (u : ℝ) : ℝ :=
  p.a * u - p.b * u ^ (1 + p.alpha)

theorem populationReaction_affine_hasDerivAt
    (p : PhysicalParams) (du : ℝ) (hu : 0 < p.uStar)
    (heq : p.LogisticEquilibrium) :
    HasDerivAt
      (fun t => populationReaction p (p.uStar + t * du))
      (-p.logisticSlope * du) 0 := by
  have huinner : HasDerivAt (fun t : ℝ => p.uStar + t * du) du 0 := by
    exact scalarAffine_hasDerivAt p.uStar du
  have hnorm := HasDerivAt.comp_of_eq (x := (0 : ℝ)) (y := p.uStar)
    (normalizedLogistic_hasDerivAt p.alpha p.uStar hu) huinner (by simp)
  have hscaled := hnorm.const_mul (-p.b)
  have hfun : (fun t => populationReaction p (p.uStar + t * du)) =
      fun t => -p.b * normalizedLogistic p.alpha p.uStar (p.uStar + t * du) := by
    funext t
    unfold populationReaction normalizedLogistic
    have heq' := heq
    unfold PhysicalParams.LogisticEquilibrium at heq'
    rw [heq']
    ring
  rw [hfun]
  have hcompfun :
      (fun t => -p.b * normalizedLogistic p.alpha p.uStar (p.uStar + t * du)) =
        fun t => -p.b *
          (normalizedLogistic p.alpha p.uStar ∘ fun s => p.uStar + s * du) t := by
    funext t
    rfl
  rw [hcompfun]
  have hvalue : -p.logisticSlope * du =
      -p.b * (p.alpha * p.uStar ^ p.alpha * du) := by
    unfold PhysicalParams.LogisticEquilibrium at heq
    unfold PhysicalParams.logisticSlope
    rw [heq]
    ring
  rw [hvalue]
  exact hscaled

/-- Linearized elliptic residual, with the reflected operator representing
`-Delta_h`. -/
def ellipticResidual (p : PhysicalParams) (L : ℝ) (N : ℕ) (hN : 0 < N)
    (phi psi : GridFunction N) : GridFunction N :=
  fun i => -(reflectedNegLaplacian L N hN psi i) - p.mu * psi i +
    p.signalC1Physical * phi i

/-- Linearized population residual after differentiating either scheme at a
constant equilibrium. -/
def populationResidual (p : PhysicalParams) (beta chi L : ℝ)
    (N : ℕ) (hN : 0 < N) (phi psi : GridFunction N) : GridFunction N :=
  fun i => -(reflectedNegLaplacian L N hN phi i) +
    chi * p.mobilityB0 beta * reflectedNegLaplacian L N hN psi i -
    p.logisticSlope * phi i

/-- The expanded non-minimal node equation (5.1), written with the concrete
reflected operators. -/
noncomputable def expandedPopulationNode
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ) (hN : 0 < N)
    (u v : GridFunction N) (i : Grid N) : ℝ :=
  reflectedLaplacian L N hN u i +
    beta * chi * mobilityPower p.m (beta + 1) (u i) (v i) *
      centeredGradient L N hN v i ^ 2 -
    p.m * chi * mobilityPower (p.m - 1) beta (u i) (v i) *
      centeredGradient L N hN u i * centeredGradient L N hN v i -
    chi * mobilityPower p.m beta (u i) (v i) * signalDefect p (u i) (v i) +
    populationReaction p (u i)

/-- The nonlinear elliptic node residual shared by both schemes. -/
noncomputable def expandedEllipticNode
    (p : PhysicalParams) (L : ℝ) (N : ℕ) (hN : 0 < N)
    (u v : GridFunction N) (i : Grid N) : ℝ :=
  reflectedLaplacian L N hN v i - p.mu * v i + p.nu * u i ^ p.gamma

theorem expandedEllipticNode_directionalDerivative
    (p : PhysicalParams) (L : ℝ) (N : ℕ) (hN : 0 < N)
    (phi psi : GridFunction N) (i : Grid N)
    (hu : 0 < p.uStar) :
    HasDerivAt
      (fun t => expandedEllipticNode p L N hN
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i)
      (ellipticResidual p L N hN phi psi i) 0 := by
  have hlap := linearMap_affine_apply_hasDerivAt N (reflectedLaplacian L N hN)
    p.vStar psi i (reflectedLaplacian_constant L N hN p.vStar)
  have hv : HasDerivAt (fun t : ℝ => p.vStar + t * psi i) (psi i) 0 := by
    exact scalarAffine_hasDerivAt p.vStar (psi i)
  have huinner : HasDerivAt (fun t : ℝ => p.uStar + t * phi i) (phi i) 0 := by
    exact scalarAffine_hasDerivAt p.uStar (phi i)
  have hsource := HasDerivAt.comp_of_eq (x := (0 : ℝ)) (y := p.uStar)
    (signal_source_hasDerivAt p.nu p.gamma p.uStar hu) huinner (by simp)
  have h := hlap.sub (hv.const_mul p.mu) |>.add hsource
  have hvalue : ellipticResidual p L N hN phi psi i =
      reflectedLaplacian L N hN psi i - p.mu * psi i +
        p.nu * (p.gamma * (p.uStar ^ (p.gamma - 1) * phi i)) := by
    unfold ellipticResidual reflectedLaplacian PhysicalParams.signalC1Physical
    simp only [LinearMap.neg_apply, Pi.neg_apply]
    ring
  rw [hvalue]
  have hev :
      (fun t => expandedEllipticNode p L N hN
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i) =ᶠ[𝓝 0]
        (((fun t => reflectedLaplacian L N hN (affineGrid N p.vStar psi t) i) -
          fun y => p.mu * (p.vStar + y * psi i)) +
          (fun y => p.nu * y ^ p.gamma) ∘ fun t => p.uStar + t * phi i) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have h' := h.congr_of_eventuallyEq hev
  exact h'.congr_deriv (by ring)

theorem expandedPopulationNode_directionalDerivative
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ) (hN : 0 < N)
    (phi psi : GridFunction N) (i : Grid N)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset)
    (hsignal : p.SignalEquilibrium) (hlog : p.LogisticEquilibrium) :
    HasDerivAt
      (fun t => expandedPopulationNode p beta chi L N hN
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i)
      (reflectedLaplacian L N hN phi i -
        chi * p.mobilityB0 beta *
          (p.mu * psi i - p.signalC1Physical * phi i) -
        p.logisticSlope * phi i) 0 := by
  have hlap := linearMap_affine_apply_hasDerivAt N (reflectedLaplacian L N hN)
    p.uStar phi i (reflectedLaplacian_constant L N hN p.uStar)
  have hgradU := linearMap_affine_apply_hasDerivAt N (centeredGradient L N hN)
    p.uStar phi i (centeredGradient_constant L N hN p.uStar)
  have hgradV := linearMap_affine_apply_hasDerivAt N (centeredGradient L N hN)
    p.vStar psi i (centeredGradient_constant L N hN p.vStar)
  have hmPlus := mobilityPower_affine_hasDerivAt (p.m) (beta + 1)
    p.uStar p.vStar (phi i) (psi i) hu hw
  have hmMinus := mobilityPower_affine_hasDerivAt (p.m - 1) beta
    p.uStar p.vStar (phi i) (psi i) hu hw
  have hm := mobilityPower_affine_hasDerivAt p.m beta
    p.uStar p.vStar (phi i) (psi i) hu hw
  have hdefect := signalDefect_affine_hasDerivAt p (phi i) (psi i) hu
  have hreaction := populationReaction_affine_hasDerivAt p (phi i) hu hlog
  have hgradUeq : ∀ t : ℝ,
      centeredGradient L N hN (affineGrid N p.uStar phi t) i =
        t * centeredGradient L N hN phi i :=
    fun t => linearMap_affine_apply_eq_mul N (centeredGradient L N hN)
      p.uStar phi i (centeredGradient_constant L N hN p.uStar) t
  have hgradVeq : ∀ t : ℝ,
      centeredGradient L N hN (affineGrid N p.vStar psi t) i =
        t * centeredGradient L N hN psi i :=
    fun t => linearMap_affine_apply_eq_mul N (centeredGradient L N hN)
      p.vStar psi i (centeredGradient_constant L N hN p.vStar) t
  have hquadVbase := coefficient_mul_two_linear_hasDerivAt
    (fun t => mobilityPower p.m (beta + 1)
      (p.uStar + t * phi i) (p.vStar + t * psi i))
    _ (centeredGradient L N hN psi i) (centeredGradient L N hN psi i) hmPlus
  have hquadV : HasDerivAt
      (fun t => mobilityPower p.m (beta + 1)
        (p.uStar + t * phi i) (p.vStar + t * psi i) *
        centeredGradient L N hN (affineGrid N p.vStar psi t) i ^ 2)
      0 0 := by
    convert hquadVbase using 1
    funext t
    rw [hgradVeq]
    ring
  have hquadUVbase := coefficient_mul_two_linear_hasDerivAt
    (fun t => mobilityPower (p.m - 1) beta
      (p.uStar + t * phi i) (p.vStar + t * psi i))
    _ (centeredGradient L N hN phi i) (centeredGradient L N hN psi i) hmMinus
  have hquadUV : HasDerivAt
      (fun t => mobilityPower (p.m - 1) beta
        (p.uStar + t * phi i) (p.vStar + t * psi i) *
        centeredGradient L N hN (affineGrid N p.uStar phi t) i *
        centeredGradient L N hN (affineGrid N p.vStar psi t) i)
      0 0 := by
    convert hquadUVbase using 1
    funext t
    rw [hgradUeq, hgradVeq]
  have hdefect0 :
      signalDefect p p.uStar p.vStar = 0 :=
    signalDefect_at_equilibrium p hsignal
  have hchemBase := coefficient_mul_zero_value_hasDerivAt
    (fun t => mobilityPower p.m beta
      (p.uStar + t * phi i) (p.vStar + t * psi i))
    (fun t => signalDefect p
      (p.uStar + t * phi i) (p.vStar + t * psi i)) _ _ hm hdefect (by
        simpa using hdefect0)
  have hmob0 : mobilityPower p.m beta p.uStar p.vStar = p.mobilityB0 beta :=
    mobilityPower_at_equilibrium_eq_B0 p beta hw
  have hquadVscaled : HasDerivAt
      (fun t => beta * chi *
        (mobilityPower p.m (beta + 1) (p.uStar + t * phi i)
          (p.vStar + t * psi i) *
          centeredGradient L N hN (affineGrid N p.vStar psi t) i ^ 2)) 0 0 :=
    by simpa only [mul_zero] using hquadV.const_mul (beta * chi)
  have hquadUVscaled : HasDerivAt
      (fun t => p.m * chi *
        (mobilityPower (p.m - 1) beta (p.uStar + t * phi i)
          (p.vStar + t * psi i) *
          centeredGradient L N hN (affineGrid N p.uStar phi t) i *
          centeredGradient L N hN (affineGrid N p.vStar psi t) i)) 0 0 :=
    by simpa only [mul_zero] using hquadUV.const_mul (p.m * chi)
  have hchemScaled : HasDerivAt
      (fun t => chi *
        (mobilityPower p.m beta (p.uStar + t * phi i)
          (p.vStar + t * psi i) *
          signalDefect p (p.uStar + t * phi i) (p.vStar + t * psi i)))
      (chi * (mobilityPower p.m beta
        (p.uStar + 0 * phi i) (p.vStar + 0 * psi i) *
        (p.mu * psi i - p.signalC1Physical * phi i))) 0 :=
    hchemBase.const_mul chi
  have h := (((hlap.add hquadVscaled).sub hquadUVscaled).sub hchemScaled).add hreaction
  have hmobPath0 : mobilityPower p.m beta
      (p.uStar + 0 * phi i) (p.vStar + 0 * psi i) = p.mobilityB0 beta := by
    simpa using hmob0
  have hvalue :
      reflectedLaplacian L N hN phi i -
          chi * p.mobilityB0 beta *
            (p.mu * psi i - p.signalC1Physical * phi i) -
          p.logisticSlope * phi i =
        reflectedLaplacian L N hN phi i + beta * chi * 0 - p.m * chi * 0 -
          chi * (mobilityPower p.m beta
            (p.uStar + 0 * phi i) (p.vStar + 0 * psi i) *
              (p.mu * psi i - p.signalC1Physical * phi i)) +
          -p.logisticSlope * phi i := by
    rw [hmobPath0]
    ring
  rw [hvalue]
  have hev :
      (fun t => expandedPopulationNode p beta chi L N hN
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i) =ᶠ[𝓝 0]
      (((((fun t => reflectedLaplacian L N hN (affineGrid N p.uStar phi t) i) +
        fun t => beta * chi *
          (mobilityPower p.m (beta + 1) (p.uStar + t * phi i)
            (p.vStar + t * psi i) *
            centeredGradient L N hN (affineGrid N p.vStar psi t) i ^ 2)) -
        fun t => p.m * chi *
          (mobilityPower (p.m - 1) beta (p.uStar + t * phi i)
            (p.vStar + t * psi i) *
            centeredGradient L N hN (affineGrid N p.uStar phi t) i *
            centeredGradient L N hN (affineGrid N p.vStar psi t) i)) -
        fun t => chi *
          (mobilityPower p.m beta (p.uStar + t * phi i)
            (p.vStar + t * psi i) *
            signalDefect p (p.uStar + t * phi i) (p.vStar + t * psi i))) +
        fun t => populationReaction p (p.uStar + t * phi i)) :=
    Filter.Eventually.of_forall (fun t => by
      unfold expandedPopulationNode affineGrid
      simp only [Pi.add_apply, Pi.sub_apply]
      simp only [add_comm, mul_comm]
      ring)
  have h' := h.congr_of_eventuallyEq hev
  exact h'.congr_deriv (by ring)

/-- After imposing the differentiated elliptic equation, the directional
derivative of the actual expanded scheme is the finite population operator. -/
theorem expandedPopulationNode_directionalDerivative_eq_populationResidual
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ) (hN : 0 < N)
    (phi psi : GridFunction N) (i : Grid N)
    (hp : p.LogisticAdmissible)
    (hell : ellipticResidual p L N hN phi psi = 0) :
    HasDerivAt
      (fun t => expandedPopulationNode p beta chi L N hN
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i)
      (populationResidual p beta chi L N hN phi psi i) 0 := by
  rcases hp with ⟨ha, hb, halpha, hm, hgamma, hnu, hmu, hu, hv, heq⟩
  have hw : 0 < p.signalOffset := by
    unfold PhysicalParams.signalOffset
    linarith
  have hraw := expandedPopulationNode_directionalDerivative p beta chi L N hN
    phi psi i hu hw heq.2 heq.1
  have hi : -(reflectedNegLaplacian L N hN psi i) - p.mu * psi i +
      p.signalC1Physical * phi i = 0 := by
    simpa [ellipticResidual] using congrFun hell i
  have hvalue : populationResidual p beta chi L N hN phi psi i =
      reflectedLaplacian L N hN phi i -
        chi * p.mobilityB0 beta *
          (p.mu * psi i - p.signalC1Physical * phi i) -
        p.logisticSlope * phi i := by
    unfold populationResidual reflectedLaplacian
    simp only [LinearMap.neg_apply, Pi.neg_apply]
    rw [show p.mu * psi i - p.signalC1Physical * phi i =
      -(reflectedNegLaplacian L N hN psi i) by linarith]
    ring
  rw [hvalue]
  exact hraw

abbrev Face (N : ℕ) := Fin N

def faceLeft {N : ℕ} (j : Face N) : Grid N :=
  ⟨j.val, Nat.lt.step j.isLt⟩

def faceRight {N : ℕ} (j : Face N) : Grid N :=
  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩

/-- Literal complete flux in Equation 5.2. -/
noncomputable def conservativeFaceFlux
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ)
    (u v : GridFunction N) (j : Face N) : ℝ :=
  (u (faceRight j) - u (faceLeft j)) / meshWidth L N -
    chi * ((1 / 2) *
      ((mobilityPower p.m beta (u (faceLeft j)) (v (faceLeft j)) +
        mobilityPower p.m beta (u (faceRight j)) (v (faceRight j))) *
        (v (faceRight j) - v (faceLeft j)))) / meshWidth L N

theorem conservativeFaceFlux_directionalDerivative
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ)
    (phi psi : GridFunction N) (j : Face N)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) :
    HasDerivAt
      (fun t => conservativeFaceFlux p beta chi L N
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) j)
      ((phi (faceRight j) - phi (faceLeft j)) / meshWidth L N -
        chi * p.mobilityB0 beta *
          (psi (faceRight j) - psi (faceLeft j)) / meshWidth L N) 0 := by
  have hmobLeft := mobilityPower_affine_hasDerivAt p.m beta p.uStar p.vStar
    (phi (faceLeft j)) (psi (faceLeft j)) hu hw
  have hmobRight := mobilityPower_affine_hasDerivAt p.m beta p.uStar p.vStar
    (phi (faceRight j)) (psi (faceRight j)) hu hw
  have hvdiff : HasDerivAt
      (fun t : ℝ =>
        (p.vStar + t * psi (faceRight j)) -
          (p.vStar + t * psi (faceLeft j)))
      (psi (faceRight j) - psi (faceLeft j)) 0 := by
    change HasDerivAt
      ((fun t : ℝ => p.vStar + t * psi (faceRight j)) -
        fun t => p.vStar + t * psi (faceLeft j)) _ 0
    exact (scalarAffine_hasDerivAt p.vStar (psi (faceRight j))).sub
      (scalarAffine_hasDerivAt p.vStar (psi (faceLeft j)))
  have hvdiff0 :
      (p.vStar + 0 * psi (faceRight j)) -
        (p.vStar + 0 * psi (faceLeft j)) = 0 := by ring
  have hchemSum := coefficient_mul_zero_value_hasDerivAt
    ((fun t => mobilityPower p.m beta
        (p.uStar + t * phi (faceLeft j)) (p.vStar + t * psi (faceLeft j))) +
      fun t => mobilityPower p.m beta
        (p.uStar + t * phi (faceRight j)) (p.vStar + t * psi (faceRight j)))
    (fun t => (p.vStar + t * psi (faceRight j)) -
      (p.vStar + t * psi (faceLeft j))) _ _ (hmobLeft.add hmobRight) hvdiff hvdiff0
  have hchem := hchemSum.const_mul (1 / 2)
  have hudiff : HasDerivAt
      (fun t : ℝ =>
        (p.uStar + t * phi (faceRight j)) -
          (p.uStar + t * phi (faceLeft j)))
      (phi (faceRight j) - phi (faceLeft j)) 0 := by
    change HasDerivAt
      ((fun t : ℝ => p.uStar + t * phi (faceRight j)) -
        fun t => p.uStar + t * phi (faceLeft j)) _ 0
    exact (scalarAffine_hasDerivAt p.uStar (phi (faceRight j))).sub
      (scalarAffine_hasDerivAt p.uStar (phi (faceLeft j)))
  have hmob0 := mobilityPower_at_equilibrium_eq_B0 p beta hw
  have hmobLeft0 : mobilityPower p.m beta
      (p.uStar + 0 * phi (faceLeft j))
      (p.vStar + 0 * psi (faceLeft j)) = p.mobilityB0 beta := by
    simpa using hmob0
  have hmobRight0 : mobilityPower p.m beta
      (p.uStar + 0 * phi (faceRight j))
      (p.vStar + 0 * psi (faceRight j)) = p.mobilityB0 beta := by
    simpa using hmob0
  have hchemAvg : HasDerivAt
      (fun t =>
        (1 / 2) * ((mobilityPower p.m beta
            (p.uStar + t * phi (faceLeft j)) (p.vStar + t * psi (faceLeft j)) +
          mobilityPower p.m beta
            (p.uStar + t * phi (faceRight j)) (p.vStar + t * psi (faceRight j))) *
          ((p.vStar + t * psi (faceRight j)) -
            (p.vStar + t * psi (faceLeft j)))))
      (p.mobilityB0 beta * (psi (faceRight j) - psi (faceLeft j))) 0 := by
    have hvalue : p.mobilityB0 beta * (psi (faceRight j) - psi (faceLeft j)) =
        (1 / 2) *
          (((((fun y => mobilityPower p.m beta
              (p.uStar + y * phi (faceLeft j)) (p.vStar + y * psi (faceLeft j))) +
            fun y => mobilityPower p.m beta
              (p.uStar + y * phi (faceRight j)) (p.vStar + y * psi (faceRight j))) 0)) *
            (psi (faceRight j) - psi (faceLeft j))) := by
      simp only [Pi.add_apply]
      rw [hmobLeft0, hmobRight0]
      ring
    have h' := hchem.congr_deriv hvalue.symm
    have hev :
        (fun t =>
          (1 / 2) * ((mobilityPower p.m beta
              (p.uStar + t * phi (faceLeft j)) (p.vStar + t * psi (faceLeft j)) +
            mobilityPower p.m beta
              (p.uStar + t * phi (faceRight j)) (p.vStar + t * psi (faceRight j))) *
            ((p.vStar + t * psi (faceRight j)) -
              (p.vStar + t * psi (faceLeft j))))) =ᶠ[𝓝 0]
        (fun y => (1 / 2) *
          ((((fun t => mobilityPower p.m beta
              (p.uStar + t * phi (faceLeft j)) (p.vStar + t * psi (faceLeft j))) +
            fun t => mobilityPower p.m beta
              (p.uStar + t * phi (faceRight j)) (p.vStar + t * psi (faceRight j))) y) *
            (p.vStar + y * psi (faceRight j) -
              (p.vStar + y * psi (faceLeft j))))) :=
      Filter.Eventually.of_forall (fun _ => rfl)
    exact h'.congr_of_eventuallyEq hev
  have hdiffScaled := hudiff.div_const (meshWidth L N)
  have hchemScaled := (hchemAvg.const_mul chi).div_const (meshWidth L N)
  have h := hdiffScaled.sub hchemScaled
  have hvalueFinal :
      (phi (faceRight j) - phi (faceLeft j)) / meshWidth L N -
          chi * (p.mobilityB0 beta *
            (psi (faceRight j) - psi (faceLeft j))) / meshWidth L N =
        (phi (faceRight j) - phi (faceLeft j)) / meshWidth L N -
          chi * p.mobilityB0 beta *
            (psi (faceRight j) - psi (faceLeft j)) / meshWidth L N := by ring
  have h' := h.congr_deriv hvalueFinal
  let facePath : ℝ → ℝ := fun x =>
    (p.uStar + x * phi (faceRight j) -
      (p.uStar + x * phi (faceLeft j))) / meshWidth L N -
    (chi * ((1 / 2) * ((mobilityPower p.m beta
        (p.uStar + x * phi (faceLeft j)) (p.vStar + x * psi (faceLeft j)) +
      mobilityPower p.m beta
        (p.uStar + x * phi (faceRight j)) (p.vStar + x * psi (faceRight j))) *
      (p.vStar + x * psi (faceRight j) -
        (p.vStar + x * psi (faceLeft j))))) / meshWidth L N)
  change HasDerivAt facePath _ 0 at h'
  have hfun :
      (fun t => conservativeFaceFlux p beta chi L N
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) j) = facePath := by
    funext t
    unfold facePath conservativeFaceFlux affineGrid
    rfl
  rw [hfun]
  exact h' 

def firstFace (N : ℕ) (hN : 0 < N) : Face N := ⟨0, hN⟩

def lastFace (N : ℕ) (hN : 0 < N) : Face N :=
  ⟨N - 1, Nat.sub_lt hN (by omega)⟩

def rightFaceOfInterior (N : ℕ) (i : Grid N) (hiN : i.val ≠ N) : Face N :=
  ⟨i.val, by omega⟩

def leftFaceOfInterior (N : ℕ) (i : Grid N) (hi0 : i.val ≠ 0) : Face N :=
  ⟨i.val - 1, by omega⟩

/-- Literal conservative node rate from Equation 5.2. -/
noncomputable def conservativeNodeRate
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ) (hN : 0 < N)
    (u v : GridFunction N) (i : Grid N) : ℝ :=
  if hi0 : i.val = 0 then
    2 * conservativeFaceFlux p beta chi L N u v (firstFace N hN) /
      meshWidth L N
  else if hiN : i.val = N then
    -2 * conservativeFaceFlux p beta chi L N u v (lastFace N hN) /
      meshWidth L N
  else
    (conservativeFaceFlux p beta chi L N u v (rightFaceOfInterior N i hiN) -
      conservativeFaceFlux p beta chi L N u v (leftFaceOfInterior N i hi0)) /
      meshWidth L N

def linearizedFaceFlux
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ)
    (phi psi : GridFunction N) (j : Face N) : ℝ :=
  (phi (faceRight j) - phi (faceLeft j)) / meshWidth L N -
    chi * p.mobilityB0 beta *
      (psi (faceRight j) - psi (faceLeft j)) / meshWidth L N

def linearizedConservativeNodeRate
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ) (hN : 0 < N)
    (phi psi : GridFunction N) (i : Grid N) : ℝ :=
  if hi0 : i.val = 0 then
    2 * linearizedFaceFlux p beta chi L N phi psi (firstFace N hN) /
      meshWidth L N
  else if hiN : i.val = N then
    -2 * linearizedFaceFlux p beta chi L N phi psi (lastFace N hN) /
      meshWidth L N
  else
    (linearizedFaceFlux p beta chi L N phi psi (rightFaceOfInterior N i hiN) -
      linearizedFaceFlux p beta chi L N phi psi (leftFaceOfInterior N i hi0)) /
      meshWidth L N

theorem conservativeNodeRate_directionalDerivative
    (p : PhysicalParams) (beta chi L : ℝ) (N : ℕ) (hN : 0 < N)
    (phi psi : GridFunction N) (i : Grid N)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) :
    HasDerivAt
      (fun t => conservativeNodeRate p beta chi L N hN
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i)
      (linearizedConservativeNodeRate p beta chi L N hN phi psi i) 0 := by
  by_cases hi0 : i.val = 0
  · rw [show (fun t => conservativeNodeRate p beta chi L N hN
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i) =
      fun t => 2 * conservativeFaceFlux p beta chi L N
        (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t)
          (firstFace N hN) / meshWidth L N by
        funext t
        simp [conservativeNodeRate, hi0]]
    unfold linearizedConservativeNodeRate
    rw [dif_pos hi0]
    exact ((conservativeFaceFlux_directionalDerivative p beta chi L N phi psi
      (firstFace N hN) hu hw).const_mul 2).div_const (meshWidth L N)
  · by_cases hiN : i.val = N
    · rw [show (fun t => conservativeNodeRate p beta chi L N hN
          (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i) =
        fun t => -2 * conservativeFaceFlux p beta chi L N
          (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t)
            (lastFace N hN) / meshWidth L N by
          funext t
          simp [conservativeNodeRate, hi0, hiN, Nat.ne_of_gt hN]]
      unfold linearizedConservativeNodeRate
      rw [dif_neg hi0, dif_pos hiN]
      exact ((conservativeFaceFlux_directionalDerivative p beta chi L N phi psi
        (lastFace N hN) hu hw).const_mul (-2)).div_const (meshWidth L N)
    · rw [show (fun t => conservativeNodeRate p beta chi L N hN
          (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t) i) =
        fun t => (conservativeFaceFlux p beta chi L N
          (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t)
            (rightFaceOfInterior N i hiN) -
          conservativeFaceFlux p beta chi L N
            (affineGrid N p.uStar phi t) (affineGrid N p.vStar psi t)
              (leftFaceOfInterior N i hi0)) / meshWidth L N by
          funext t
          simp [conservativeNodeRate, hi0, hiN]]
      unfold linearizedConservativeNodeRate
      rw [dif_neg hi0, dif_neg hiN]
      have hr := conservativeFaceFlux_directionalDerivative p beta chi L N phi psi
        (rightFaceOfInterior N i hiN) hu hw
      have hl := conservativeFaceFlux_directionalDerivative p beta chi L N phi psi
        (leftFaceOfInterior N i hi0) hu hw
      exact (hr.sub hl).div_const (meshWidth L N)

/-- The reflected cosine mode solves the coupled finite first-order equations,
and the population equation has exactly the manuscript growth rate. -/
theorem discrete_coupled_mode_residuals
    (p : PhysicalParams) (beta chi L : ℝ) (N n : ℕ)
    (hL : L ≠ 0) (hN : 0 < N) (hnN : n ≤ N)
    (hden : p.mu + discLam L n N ≠ 0) :
    let lam := discLam L n N
    let phi := discreteCosineMode N n
    let psi := Eigenmodes.ellipticCoefficient p.signalC1Physical p.mu lam • phi
    ellipticResidual p L N hN phi psi = 0 ∧
      populationResidual p beta chi L N hN phi psi =
        Eigenmodes.growthRate (chi * p.mobilityB0 beta)
          p.signalC1Physical p.mu p.logisticSlope lam • phi := by
  dsimp only
  have heig := reflectedNegLaplacian_cosine_eigenpair L N n hL hN hnN
  constructor
  · funext i
    change ellipticResidual p L N hN
      (discreteCosineMode N n)
      (Eigenmodes.ellipticCoefficient p.signalC1Physical p.mu (discLam L n N) •
        discreteCosineMode N n) i = 0
    have heigi := congrFun heig i
    unfold ellipticResidual Eigenmodes.ellipticCoefficient
    simp only [Pi.smul_apply, smul_eq_mul, map_smul, heigi]
    field_simp [hden]
    ring
  · funext i
    have heigi := congrFun heig i
    unfold populationResidual Eigenmodes.ellipticCoefficient Eigenmodes.growthRate
    simp only [Pi.smul_apply, smul_eq_mul, map_smul, heigi]
    field_simp [hden]

theorem represented_discLam_pos
    (L : ℝ) (N n : ℕ) (hL : 0 < L) (hN : 0 < N)
    (hn : 0 < n) (hnN : n ≤ N) :
    0 < discLam L n N := by
  have hlower := discLam_lower_bound L n N hL hN hnN
  have hpositive : 0 < 4 * (n : ℝ) ^ 2 / L ^ 2 := by
    positivity
  exact lt_of_lt_of_le hpositive hlower

/-- The finite coupled growth is the already audited physical modal growth. -/
theorem discrete_growth_eq_physical_modalGrowth
    (p : PhysicalParams) (chi x beta : ℝ) :
    Eigenmodes.growthRate (chi * p.mobilityB0 beta)
        p.signalC1Physical p.mu p.logisticSlope x =
      LinearRegime.modalGrowth chi (p.thresholdK beta)
        p.logisticSlope p.mu x := by
  exact (PhysicalLinearRegime.physicalGrowth_eq_coupled p chi x beta).symm

/-- Neutral growth of a represented positive mode is equivalent to the
displayed physical discrete modal threshold. -/
theorem discrete_growth_eq_zero_iff_threshold
    (p : PhysicalParams) (beta chi L : ℝ) (N n : ℕ)
    (hp : PhysicalModeGuards.PositiveModeParameters p)
    (hL : 0 < L) (hN : 0 < N) (hn : 0 < n) (hnN : n ≤ N) :
    Eigenmodes.growthRate (chi * p.mobilityB0 beta)
        p.signalC1Physical p.mu p.logisticSlope (discLam L n N) = 0 ↔
      chi = p.chiStar (discLam L n N) beta := by
  rw [discrete_growth_eq_physical_modalGrowth]
  exact PhysicalLinearRegime.physicalGrowth_zero_iff p chi (discLam L n N) beta hp
    (represented_discLam_pos L N n hL hN hn hnN)

/-- The threshold minimized in the semidiscrete convergence theorem is the
minimum of the neutral sensitivities of the represented positive modes. -/
theorem discreteCritical_eq_physical_threshold_min
    (p : PhysicalParams) (beta L : ℝ) (N : ℕ)
    (hp : PhysicalModeGuards.PositiveModeParameters p) (hN : 0 < N) :
    Semidiscrete.discreteCritical (Semidiscrete.physicalPrefactor p beta)
        p.logisticSlope p.mu L N =
      (Semidiscrete.positiveModes N).inf' (Semidiscrete.positiveModes_nonempty hN)
        (fun n => p.chiStar (discLam L n N) beta) := by
  unfold Semidiscrete.discreteCritical
  rw [dif_pos hN]
  congr 1
  funext n
  exact (Semidiscrete.chiStar_eq_physical_modeThreshold p (discLam L n N) beta
    hp.nu_pos hp.gamma_pos hp.u_pos hp.v_pos).symm

end

end ChemotaxisBifurcation.DiscreteLinearization
