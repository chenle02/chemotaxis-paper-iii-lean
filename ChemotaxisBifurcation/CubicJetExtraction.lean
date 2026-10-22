module
public import ChemotaxisBifurcation.CubicAssembly
public import ChemotaxisBifurcation.NeumannProjection
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

/-!
# Finite cubic jet coefficient extraction

This module closes the transcription step before the four-channel cubic flux is
entered.  It extracts the amplitude-cubic coefficient from finite Taylor
polynomials.  The analytic existence of a center graph and the assertion that
its cubic correction has zero critical projection remain explicit inputs.
-/

namespace ChemotaxisBifurcation

open Polynomial

noncomputable section

/-- Scalar low-order jet data for one spatial point. -/
structure AmplitudeJetData where
  B0 : ℝ
  Bu : ℝ
  Bv : ℝ
  Buu : ℝ
  Buv : ℝ
  Bvv : ℝ
  phi : ℝ
  h2 : ℝ
  h3 : ℝ
  v1 : ℝ
  v2 : ℝ
  v3 : ℝ
  w1 : ℝ
  w2 : ℝ
  w3 : ℝ

namespace AmplitudeJetData

def duPoly (d : AmplitudeJetData) : ℝ[X] :=
  C d.phi * X + C d.h2 * X ^ 2 + C d.h3 * X ^ 3

def dvPoly (d : AmplitudeJetData) : ℝ[X] :=
  C d.v1 * X + C d.v2 * X ^ 2 + C d.v3 * X ^ 3

def vxPoly (d : AmplitudeJetData) : ℝ[X] :=
  C d.w1 * X + C d.w2 * X ^ 2 + C d.w3 * X ^ 3

/-- Quadratic Taylor polynomial of the mobility evaluated on the two jets. -/
def mobilityPoly (d : AmplitudeJetData) : ℝ[X] :=
  C d.B0 + C d.Bu * d.duPoly + C d.Bv * d.dvPoly +
    C d.Buu * d.duPoly ^ 2 + C d.Buv * d.duPoly * d.dvPoly +
    C d.Bvv * d.dvPoly ^ 2

/-- The exact four-group coefficient multiplying amplitude cubed in
`mobility * v_x`. -/
def cubicFluxCoefficient (d : AmplitudeJetData) : ℝ :=
  d.B0 * d.w3 + (d.Bu * d.phi + d.Bv * d.v1) * d.w2 +
    (d.Bu * d.h2 + d.Bv * d.v2 + d.Buu * d.phi ^ 2 +
      d.Buv * d.phi * d.v1 + d.Bvv * d.v1 ^ 2) * d.w1

set_option maxHeartbeats 800000 in
/-- Finite coefficient extraction behind the four terms of `J₃`. -/
theorem coeff_mobility_mul_vx_three (d : AmplitudeJetData) :
    (d.mobilityPoly * d.vxPoly).coeff 3 = d.cubicFluxCoefficient := by
  simp (config := { maxSteps := 200000 })
    [mobilityPoly, vxPoly, duPoly, dvPoly, cubicFluxCoefficient,
    Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X,
    Polynomial.coeff_add, pow_succ, pow_two,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] <;> ring

end AmplitudeJetData

/-- Signal-source Taylor polynomial evaluated on the population jet. -/
def signalSourcePoly
    (C1 C2 C3 phi h2 h3 : ℝ) : ℝ[X] :=
  let du := C phi * X + C h2 * X ^ 2 + C h3 * X ^ 3
  C C1 * du + C C2 * du ^ 2 + C C3 * du ^ 3

set_option maxHeartbeats 800000 in
/-- The amplitude-cubic signal-source coefficient is
`C' h₃ + 2 C'' phi h₂ + C''' phi³`. -/
theorem coeff_signalSource_three
    (C1 C2 C3 phi h2 h3 : ℝ) :
    (signalSourcePoly C1 C2 C3 phi h2 h3).coeff 3 =
      C1 * h3 + 2 * C2 * phi * h2 + C3 * phi ^ 3 := by
  simp (config := { maxSteps := 200000 })
    [signalSourcePoly, Polynomial.coeff_mul, Polynomial.coeff_C,
    Polynomial.coeff_X, Polynomial.coeff_add, pow_succ, pow_two,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] <;> ring

/-- Function-level cubic signal source. -/
def signalCubicSource
    (C1 C2 C3 : ℝ) (phi h2 h3 : ℝ → ℝ) : ℝ → ℝ :=
  fun y => C1 * h3 y + 2 * C2 * phi y * h2 y + C3 * phi y ^ 3

/-- Critical projection of the cubic signal coefficient under the named
center-graph projection input `Pi h3 = 0`.

The other two hypotheses are the finite cosine projections proved in
`NeumannProjection`. -/
theorem signalCubicSource_critical_projection
    (Pi : (ℝ → ℝ) →ₗ[ℝ] ℝ)
    (C1 C2 C3 a0 a2 : ℝ) (phi h2 h3 : ℝ → ℝ)
    (hh3 : Pi h3 = 0)
    (hphi_h2 : Pi (fun y => phi y * h2 y) = a0 + a2 / 2)
    (hphi3 : Pi (fun y => phi y ^ 3) = 3 / 4) :
    Pi (signalCubicSource C1 C2 C3 phi h2 h3) =
      C2 * (2 * a0 + a2) + 3 * C3 / 4 := by
  have hfun : signalCubicSource C1 C2 C3 phi h2 h3 =
      C1 • h3 + (2 * C2) • (fun y => phi y * h2 y) +
        C3 • (fun y => phi y ^ 3) := by
    funext y
    simp [signalCubicSource]
    ring
  rw [hfun, map_add, map_add, map_smul, map_smul, map_smul,
    hh3, hphi_h2, hphi3]
  ring

/-- Instantiate the scalar amplitude jets with the critical and second
harmonics used in the four-term flux. -/
noncomputable def amplitudeJetOfRawCubic
    (d : RawCubicProjectionData) (k theta : ℝ) : AmplitudeJetData where
  B0 := d.B0
  Bu := d.Bu
  Bv := d.Bv
  Buu := d.Buu
  Buv := d.Buv
  Bvv := d.Bvv
  phi := Real.cos theta
  h2 := d.a0 + d.a2 * Real.cos (2 * theta)
  h3 := 0
  v1 := d.F * Real.cos theta
  v2 := d.E + d.G * Real.cos (2 * theta)
  v3 := 0
  w1 := -k * d.F * Real.sin theta
  w2 := -2 * k * d.G * Real.sin (2 * theta)
  w3 := -k * d.H * Real.sin theta

/-- The amplitude-cubic coefficient extracted from primitive Taylor products
is exactly the four-term raw flux entered in `FiniteProjection`. -/
theorem cubicFluxCoefficient_eq_rawFlux
    (d : RawCubicProjectionData) (k y : ℝ) :
    (amplitudeJetOfRawCubic d k (k * y)).cubicFluxCoefficient = d.flux k y := by
  unfold amplitudeJetOfRawCubic AmplitudeJetData.cubicFluxCoefficient
    RawCubicProjectionData.flux
  have hmob := d.mobility_collection (k * y)
  have hcollection :
      d.Bu * (d.a0 + d.a2 * Real.cos (2 * (k * y))) +
          d.Bv * (d.E + d.G * Real.cos (2 * (k * y))) +
          d.Buu * Real.cos (k * y) ^ 2 +
          d.Buv * Real.cos (k * y) * (d.F * Real.cos (k * y)) +
          d.Bvv * (d.F * Real.cos (k * y)) ^ 2 =
        d.R + d.S * Real.cos (2 * (k * y)) := by
    calc
      _ = d.Bu * (d.a0 + d.a2 * Real.cos (2 * (k * y))) +
          d.Bv * (d.E + d.G * Real.cos (2 * (k * y))) +
          d.Q * Real.cos (k * y) ^ 2 := by
            unfold RawCubicProjectionData.Q
            ring
      _ = _ := hmob
  rw [hcollection]
  unfold RawCubicProjectionData.linearMobility
  ring

/-- The mobility fields used by the raw cubic projection are the primitive
Taylor coefficients, not an independent transcription. -/
theorem rawCubicProjectionData_taylor_fields
    (p : PhysicalParams) (x beta : ℝ) (jet : QuadraticJetData)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) :
    let d := rawCubicProjectionData p x beta jet
    let t := rawTaylorData p beta
    d.B0 = t.B0 ∧ d.Bu = t.Bu ∧ d.Bv = t.Bv ∧
      d.Buu = t.Buu ∧ d.Buv = t.Buv ∧ d.Bvv = t.Bvv := by
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (raw_Bu_eq_scaled p beta hu).symm
  · exact (raw_Bv_eq_scaled p beta hw).symm
  · exact (raw_Buu_eq_scaled p beta hu).symm
  · exact (raw_Buv_eq_scaled p beta hu hw).symm
  · exact (raw_Bvv_eq_scaled p beta hw).symm

/-- The manuscript's normalized positive-mode projection, restricted here to
the continuous functions used in the finite jet. -/
noncomputable def actualCriticalProjection
    (L : ℝ) (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  2 / L * (∫ y in (0 : ℝ)..L, f y * neumannMode L n y)

theorem actualCriticalProjection_add
    (L : ℝ) (n : ℕ) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    actualCriticalProjection L n (fun y => f y + g y) =
      actualCriticalProjection L n f + actualCriticalProjection L n g := by
  unfold actualCriticalProjection
  rw [show (fun y : ℝ => (f y + g y) * neumannMode L n y) =
      fun y => f y * neumannMode L n y + g y * neumannMode L n y by
        funext y
        ring]
  have hm : Continuous (neumannMode L n) := by
    unfold neumannMode waveNumber
    continuity
  rw [intervalIntegral.integral_add
    (f := fun y => f y * neumannMode L n y)
    (g := fun y => g y * neumannMode L n y)
    ((hf.mul hm).intervalIntegrable (0 : ℝ) L)
    ((hg.mul hm).intervalIntegrable (0 : ℝ) L)]
  ring

theorem actualCriticalProjection_const_mul
    (L : ℝ) (n : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    actualCriticalProjection L n (fun y => c * f y) =
      c * actualCriticalProjection L n f := by
  unfold actualCriticalProjection
  rw [show (fun y : ℝ => c * f y * neumannMode L n y) =
      fun y => c * (f y * neumannMode L n y) by
        funext y
        ring, intervalIntegral.integral_const_mul]
  ring

/-- Actual Neumann-integral version of the cubic signal projection. -/
theorem signalCubicSource_actual_projection
    (L : ℝ) (n : ℕ) (C1 C2 C3 a0 a2 : ℝ)
    (phi h2 h3 : ℝ → ℝ)
    (hphi : Continuous phi) (hh2 : Continuous h2) (hh3c : Continuous h3)
    (hh3 : actualCriticalProjection L n h3 = 0)
    (hphi_h2 : actualCriticalProjection L n (fun y => phi y * h2 y) =
      a0 + a2 / 2)
    (hphi3 : actualCriticalProjection L n (fun y => phi y ^ 3) = 3 / 4) :
    actualCriticalProjection L n (signalCubicSource C1 C2 C3 phi h2 h3) =
      C2 * (2 * a0 + a2) + 3 * C3 / 4 := by
  have hprod : Continuous (fun y => phi y * h2 y) := hphi.mul hh2
  have hcube : Continuous (fun y => phi y ^ 3) := hphi.pow 3
  have hfun : signalCubicSource C1 C2 C3 phi h2 h3 =
      fun y => C1 * h3 y +
        ((2 * C2) * (phi y * h2 y) + C3 * phi y ^ 3) := by
    funext y
    simp [signalCubicSource]
    ring
  rw [hfun, actualCriticalProjection_add L n
      (fun y => C1 * h3 y)
      (fun y => (2 * C2) * (phi y * h2 y) + C3 * phi y ^ 3)
      (continuous_const.mul hh3c)
      ((continuous_const.mul hprod).add (continuous_const.mul hcube)),
    actualCriticalProjection_add L n
      (fun y => (2 * C2) * (phi y * h2 y))
      (fun y => C3 * phi y ^ 3)
      (continuous_const.mul hprod) (continuous_const.mul hcube),
    actualCriticalProjection_const_mul,
    actualCriticalProjection_const_mul,
    actualCriticalProjection_const_mul,
    hh3, hphi_h2, hphi3]
  ring

/-- Solve the projected cubic signal balance for its critical coefficient. -/
theorem H_eq_of_projected_signal_balance
    (mu x C2 C3 a0 a2 H : ℝ) (hden : mu + x ≠ 0)
    (hbalance : (mu + x) * H = C2 * (2 * a0 + a2) + 3 * C3 / 4) :
    H = C2 / (mu + x) * (2 * a0 + a2) +
      3 * C3 / (4 * (mu + x)) := by
  field_simp [hden]
  nlinarith

/-- The projected signal balance recovers the `cubicH` used by the physical
assembly. -/
theorem cubicH_eq_of_projected_signal_balance
    (p : PhysicalParams) (x H : ℝ) (jet : QuadraticJetData)
    (hden : p.mu + x ≠ 0)
    (hbalance :
      (p.mu + x) * H =
        (mobilityScaledTaylor p 0).Csecond * (2 * jet.a0 + jet.a2) +
          3 * (mobilityScaledTaylor p 0).Cthird / 4) :
    H = cubicH p x jet := by
  have h := H_eq_of_projected_signal_balance p.mu x
    (mobilityScaledTaylor p 0).Csecond
    (mobilityScaledTaylor p 0).Cthird jet.a0 jet.a2 H hden hbalance
  rw [h]
  unfold cubicH signalMode2 signalMode3
  field_simp [hden]

/-- Additivity of the actual projection under only the weighted interval
integrability needed by the interval integral. -/
theorem actualCriticalProjection_add_of_intervalIntegrable
    (L : ℝ) (n : ℕ) (f g : ℝ → ℝ)
    (hf : IntervalIntegrable (fun y => f y * neumannMode L n y)
      MeasureTheory.volume 0 L)
    (hg : IntervalIntegrable (fun y => g y * neumannMode L n y)
      MeasureTheory.volume 0 L) :
    actualCriticalProjection L n (fun y => f y + g y) =
      actualCriticalProjection L n f + actualCriticalProjection L n g := by
  unfold actualCriticalProjection
  rw [show (fun y : ℝ => (f y + g y) * neumannMode L n y) =
      fun y => f y * neumannMode L n y + g y * neumannMode L n y by
        funext y
        ring,
    intervalIntegral.integral_add hf hg]
  ring

/-- Cubic signal projection with no global continuity requirement. -/
theorem signalCubicSource_actual_projection_of_intervalIntegrable
    (L : ℝ) (n : ℕ) (C1 C2 C3 a0 a2 : ℝ)
    (phi h2 h3 : ℝ → ℝ)
    (hIh3 : IntervalIntegrable (fun y => h3 y * neumannMode L n y)
      MeasureTheory.volume 0 L)
    (hIprod : IntervalIntegrable
      (fun y => (phi y * h2 y) * neumannMode L n y)
      MeasureTheory.volume 0 L)
    (hIcube : IntervalIntegrable
      (fun y => phi y ^ 3 * neumannMode L n y)
      MeasureTheory.volume 0 L)
    (hh3 : actualCriticalProjection L n h3 = 0)
    (hphi_h2 : actualCriticalProjection L n (fun y => phi y * h2 y) =
      a0 + a2 / 2)
    (hphi3 : actualCriticalProjection L n (fun y => phi y ^ 3) = 3 / 4) :
    actualCriticalProjection L n (signalCubicSource C1 C2 C3 phi h2 h3) =
      C2 * (2 * a0 + a2) + 3 * C3 / 4 := by
  have hIh3c : IntervalIntegrable
      (fun y => (C1 * h3 y) * neumannMode L n y)
      MeasureTheory.volume 0 L := by
    simpa [mul_assoc] using hIh3.const_mul C1
  have hIprodc : IntervalIntegrable
      (fun y => ((2 * C2) * (phi y * h2 y)) * neumannMode L n y)
      MeasureTheory.volume 0 L := by
    simpa [mul_assoc] using hIprod.const_mul (2 * C2)
  have hIcubec : IntervalIntegrable
      (fun y => (C3 * phi y ^ 3) * neumannMode L n y)
      MeasureTheory.volume 0 L := by
    simpa [mul_assoc] using hIcube.const_mul C3
  have hIsum : IntervalIntegrable
      (fun y => ((2 * C2) * (phi y * h2 y) + C3 * phi y ^ 3) *
        neumannMode L n y) MeasureTheory.volume 0 L := by
    simpa [add_mul, mul_assoc] using hIprodc.add hIcubec
  have hfun : signalCubicSource C1 C2 C3 phi h2 h3 =
      fun y => C1 * h3 y +
        ((2 * C2) * (phi y * h2 y) + C3 * phi y ^ 3) := by
    funext y
    simp [signalCubicSource]
    ring
  rw [hfun, actualCriticalProjection_add_of_intervalIntegrable L n
      (fun y => C1 * h3 y)
      (fun y => (2 * C2) * (phi y * h2 y) + C3 * phi y ^ 3)
      hIh3c hIsum,
    actualCriticalProjection_add_of_intervalIntegrable L n
      (fun y => (2 * C2) * (phi y * h2 y))
      (fun y => C3 * phi y ^ 3)
      hIprodc hIcubec,
    actualCriticalProjection_const_mul,
    actualCriticalProjection_const_mul,
    actualCriticalProjection_const_mul,
    hh3, hphi_h2, hphi3]
  ring

/-- Actual projection of `phi*(a0+a2*phi_2n)` for the verified Neumann modes. -/
theorem actual_phi_quadraticJet_projection
    (L : ℝ) (n : ℕ) (a0 a2 : ℝ) (hL : 0 < L) (hn : 0 < n) :
    actualCriticalProjection L n
      (fun y => neumannMode L n y * quadraticJetProfile a0 a2 L n y) =
        a0 + a2 / 2 := by
  unfold actualCriticalProjection quadraticJetProfile
  rw [show (fun y : ℝ =>
      neumannMode L n y *
          (a0 + a2 * neumannMode L (2 * n) y) * neumannMode L n y) =
      fun y => (a0 + a2 / 2) *
          (neumannMode L n y * neumannMode L n y) +
        (a2 / 2) *
          (neumannMode L (3 * n) y * neumannMode L n y) by
      funext y
      unfold neumannMode waveNumber
      rw [show (((2 * n : ℕ) : ℝ) * Real.pi / L) * y =
          2 * (((n : ℝ) * Real.pi / L) * y) by
        push_cast
        ring]
      rw [show (((3 * n : ℕ) : ℝ) * Real.pi / L) * y =
          3 * (((n : ℝ) * Real.pi / L) * y) by
        push_cast
        ring]
      let theta := ((n : ℝ) * Real.pi / L) * y
      change Real.cos theta * (a0 + a2 * Real.cos (2 * theta)) *
          Real.cos theta =
        (a0 + a2 / 2) * (Real.cos theta * Real.cos theta) +
          a2 / 2 * (Real.cos (3 * theta) * Real.cos theta)
      calc
        _ = a0 * Real.cos theta ^ 2 +
            a2 * (Real.cos theta * Real.cos (2 * theta)) * Real.cos theta := by
              ring
        _ = _ := by rw [cos_mul_cos_two]; ring]
  have hcont : ∀ k : ℕ, Continuous (neumannMode L k) := by
    intro k
    unfold neumannMode waveNumber
    continuity
  rw [intervalIntegral.integral_add
      (f := fun y => (a0 + a2 / 2) *
        (neumannMode L n y * neumannMode L n y))
      (g := fun y => (a2 / 2) *
        (neumannMode L (3 * n) y * neumannMode L n y))
      ((continuous_const.mul ((hcont n).mul (hcont n))).intervalIntegrable _ _)
      ((continuous_const.mul ((hcont (3 * n)).mul (hcont n))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_neumannMode_mul L hL,
    integral_neumannMode_mul L hL]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have h3n : 3 * n ≠ n := by omega
  simp [hn0, h3n]
  field_simp [ne_of_gt hL]

theorem actual_phi_cube_projection
    (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    actualCriticalProjection L n (fun y => neumannMode L n y ^ 3) = 3 / 4 := by
  exact normalized_cubic_logistic_projection L n hL hn

end

end ChemotaxisBifurcation
