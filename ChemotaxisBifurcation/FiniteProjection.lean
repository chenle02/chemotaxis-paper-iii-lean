module
/-
Adapted from the MIT-licensed Paper III Lean package published at
chenle02/Chemataxis_Numerics, commit 5c7ef67e3c39e13daeef9321069e459b7444d04d.
-/

public import ChemotaxisBifurcation.FiniteTrig

@[expose] public section

/-!
# Finite quadratic and cubic flux projections

These generic lemmas derive the first- and third-harmonic decompositions before
any model-specific coefficient substitution.
-/

namespace ChemotaxisBifurcation

noncomputable section

structure QuadraticProjectionData where
  B0 : ℝ
  Bu : ℝ
  Bv : ℝ
  F : ℝ
  C2second : ℝ

namespace QuadraticProjectionData

def linearMobility (d : QuadraticProjectionData) : ℝ :=
  d.Bu + d.Bv * d.F

def bracket (d : QuadraticProjectionData) : ℝ :=
  4 * d.B0 * d.C2second + d.linearMobility * d.F

noncomputable def flux (d : QuadraticProjectionData) (k y : ℝ) : ℝ :=
  (-2 * k * d.B0 * d.C2second) * Real.sin (2 * (k * y)) +
    (-k * d.linearMobility * d.F) *
      (Real.cos (k * y) * Real.sin (k * y))

theorem flux_decomposition (d : QuadraticProjectionData) (k y : ℝ) :
    d.flux k y =
      -k * (2 * d.B0 * d.C2second + d.linearMobility * d.F / 2) *
        Real.sin (2 * (k * y)) := by
  unfold flux
  rw [show Real.cos (k * y) * Real.sin (k * y) =
      Real.sin (2 * (k * y)) / 2 by
        rw [Real.sin_two_mul]
        ring_nf]
  ring_nf

noncomputable def density (d : QuadraticProjectionData) (k y : ℝ) : ℝ :=
  k ^ 2 * d.bracket * Real.cos (2 * (k * y))

theorem hasDerivAt_flux (d : QuadraticProjectionData) (k y : ℝ) :
    HasDerivAt (d.flux k) (-d.density k y) y := by
  have hfun : d.flux k = fun z =>
      -k * (2 * d.B0 * d.C2second + d.linearMobility * d.F / 2) *
        Real.sin (2 * (k * z)) := by
    funext z
    exact d.flux_decomposition k z
  rw [hfun]
  have h2k : HasDerivAt (fun z : ℝ => 2 * k * z) (2 * k) y := by
    simpa using (hasDerivAt_id y).const_mul (2 * k)
  have hs := (Real.hasDerivAt_sin (2 * k * y)).comp y h2k
  have h := hs.const_mul
    (-k * (2 * d.B0 * d.C2second + d.linearMobility * d.F / 2))
  have hval :
      -k * (2 * d.B0 * d.C2second + d.linearMobility * d.F / 2) *
          (Real.cos (2 * k * y) * (2 * k)) = -d.density k y := by
    unfold density bracket
    ring_nf
  rw [hval] at h
  have hfunc :
      (fun z => -k * (2 * d.B0 * d.C2second + d.linearMobility * d.F / 2) *
        (Real.sin ∘ fun q => 2 * k * q) z) =
      (fun z => -k * (2 * d.B0 * d.C2second + d.linearMobility * d.F / 2) *
        Real.sin (2 * (k * z))) := by
    funext z
    simp only [Function.comp_apply]
    congr 1
    ring_nf
  rw [hfunc] at h
  exact h

theorem neg_deriv_flux (d : QuadraticProjectionData) (k y : ℝ) :
    -deriv (d.flux k) y = d.density k y := by
  rw [(d.hasDerivAt_flux k y).deriv]
  ring_nf

end QuadraticProjectionData

structure RawCubicProjectionData where
  B0 : ℝ
  Bu : ℝ
  Bv : ℝ
  Buu : ℝ
  Buv : ℝ
  Bvv : ℝ
  a0 : ℝ
  a2 : ℝ
  E : ℝ
  F : ℝ
  G : ℝ
  H : ℝ

namespace RawCubicProjectionData

def linearMobility (d : RawCubicProjectionData) : ℝ :=
  d.Bu + d.Bv * d.F

def Q (d : RawCubicProjectionData) : ℝ :=
  d.Buu + d.Buv * d.F + d.Bvv * d.F ^ 2

def R (d : RawCubicProjectionData) : ℝ :=
  d.Bu * d.a0 + d.Bv * d.E + d.Q / 2

def S (d : RawCubicProjectionData) : ℝ :=
  d.Bu * d.a2 + d.Bv * d.G + d.Q / 2

def criticalBracket (d : RawCubicProjectionData) : ℝ :=
  d.B0 * d.H + d.linearMobility * d.G + d.F * (d.R - d.S / 2)

def thirdBracket (d : RawCubicProjectionData) : ℝ :=
  d.linearMobility * d.G + d.F * d.S / 2

theorem mobility_collection (d : RawCubicProjectionData) (theta : ℝ) :
    d.Bu * (d.a0 + d.a2 * Real.cos (2 * theta)) +
        d.Bv * (d.E + d.G * Real.cos (2 * theta)) +
        d.Q * Real.cos theta ^ 2 =
      d.R + d.S * Real.cos (2 * theta) := by
  rw [cos_sq]
  unfold R S
  ring_nf

noncomputable def flux (d : RawCubicProjectionData) (k y : ℝ) : ℝ :=
  (-k * d.B0 * d.H) * Real.sin (k * y) +
    (-2 * k * d.linearMobility * d.G) *
      (Real.cos (k * y) * Real.sin (2 * (k * y))) +
    (-k * d.F * d.R) * Real.sin (k * y) +
    (-k * d.F * d.S) *
      (Real.cos (2 * (k * y)) * Real.sin (k * y))

/-- All four cubic channels collect into the critical and third harmonics. -/
theorem flux_decomposition (d : RawCubicProjectionData) (k y : ℝ) :
    d.flux k y =
      -k * d.criticalBracket * Real.sin (k * y) -
        k * d.thirdBracket * Real.sin (3 * (k * y)) := by
  unfold flux
  rw [cos_mul_sin_two, cos_two_mul_sin]
  unfold criticalBracket thirdBracket
  ring_nf

noncomputable def density (d : RawCubicProjectionData) (k y : ℝ) : ℝ :=
  k ^ 2 * d.criticalBracket * Real.cos (k * y) +
    3 * k ^ 2 * d.thirdBracket * Real.cos (3 * (k * y))

theorem hasDerivAt_flux (d : RawCubicProjectionData) (k y : ℝ) :
    HasDerivAt (d.flux k) (-d.density k y) y := by
  have hfun : d.flux k = fun z =>
      -k * d.criticalBracket * Real.sin (k * z) -
        k * d.thirdBracket * Real.sin (3 * (k * z)) := by
    funext z
    exact d.flux_decomposition k z
  rw [hfun]
  have hk : HasDerivAt (fun z : ℝ => k * z) k y := by
    simpa using (hasDerivAt_id y).const_mul k
  have h3k : HasDerivAt (fun z : ℝ => 3 * k * z) (3 * k) y := by
    simpa using (hasDerivAt_id y).const_mul (3 * k)
  have hs1 := (Real.hasDerivAt_sin (k * y)).comp y hk
  have hs3 := (Real.hasDerivAt_sin (3 * k * y)).comp y h3k
  have h := (hs1.const_mul (-k * d.criticalBracket)).sub
    (hs3.const_mul (k * d.thirdBracket))
  have hval :
      -k * d.criticalBracket * (Real.cos (k * y) * k) -
          k * d.thirdBracket * (Real.cos (3 * k * y) * (3 * k)) =
        -d.density k y := by
    unfold density
    ring_nf
  rw [hval] at h
  have hfunc :
      ((fun z => -k * d.criticalBracket * (Real.sin ∘ fun q => k * q) z) -
        fun z => k * d.thirdBracket * (Real.sin ∘ fun q => 3 * k * q) z) =
      (fun z => -k * d.criticalBracket * Real.sin (k * z) -
        k * d.thirdBracket * Real.sin (3 * (k * z))) := by
    funext z
    simp only [Function.comp_apply, Pi.sub_apply]
    ring_nf
  rw [hfunc] at h
  exact h

theorem neg_deriv_flux (d : RawCubicProjectionData) (k y : ℝ) :
    -deriv (d.flux k) y = d.density k y := by
  rw [(d.hasDerivAt_flux k y).deriv]
  ring_nf

end RawCubicProjectionData

end

end ChemotaxisBifurcation
