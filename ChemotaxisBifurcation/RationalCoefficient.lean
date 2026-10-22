module
public import ChemotaxisBifurcation.CubicAssembly

@[expose] public section

/-!
# Generic rational form of the cubic coefficient

The symbolic family in this file clears the modal denominators before any
concrete parameter specialization.  `RationalData.numerator` is constructed
from the quadratic and cubic coefficient chain; it is not an assumed answer.
-/

namespace ChemotaxisBifurcation.RationalCoefficient

open ChemotaxisBifurcation

noncomputable section

/-- Mobility-scaled physical constants that do not depend on the eigenvalue. -/
structure RationalData where
  d : ℝ
  mu : ℝ
  K : ℝ
  C2 : ℝ
  C3 : ℝ
  bA2 : ℝ
  bA3 : ℝ
  bu : ℝ
  bv : ℝ
  buu : ℝ
  buv : ℝ
  bvv : ℝ
  a0 : ℝ

namespace RationalData

def p1 (r : RationalData) (x : ℝ) : ℝ := r.mu + x
def q (r : RationalData) (x : ℝ) : ℝ := r.mu + 4 * x
def s (r : RationalData) (x : ℝ) : ℝ := x + r.d
def delta (r : RationalData) (x : ℝ) : ℝ := r.d * r.mu - 4 * x ^ 2

def chiB0 (r : RationalData) (x : ℝ) : ℝ :=
  s r x * p1 r x / (r.K * x)

def sigma2 (r : RationalData) (x : ℝ) : ℝ :=
  -4 * x - r.d + 4 * s r x * p1 r x / q r x

def F (r : RationalData) (x : ℝ) : ℝ := r.K / p1 r x

def chiGamma2 (r : RationalData) (x : ℝ) : ℝ :=
  x * chiB0 r x *
    (2 * r.C2 / q r x + r.bu * F r x + r.bv * F r x ^ 2)

def a2 (r : RationalData) (x : ℝ) : ℝ :=
  (r.bA2 / 2 - chiGamma2 r x) / sigma2 r x

def E (r : RationalData) : ℝ :=
  r.K / r.mu * r.a0 + r.C2 / (2 * r.mu)

def G (r : RationalData) (x : ℝ) : ℝ :=
  r.K / q r x * a2 r x + r.C2 / (2 * q r x)

def H (r : RationalData) (x : ℝ) : ℝ :=
  r.C2 / p1 r x * (2 * r.a0 + a2 r x) +
    3 * r.C3 / (4 * p1 r x)

def qNumerator (r : RationalData) (x : ℝ) : ℝ :=
  r.buu * p1 r x ^ 2 + r.buv * r.K * p1 r x + r.bvv * r.K ^ 2

def Q (r : RationalData) (x : ℝ) : ℝ :=
  r.buu + r.buv * F r x + r.bvv * F r x ^ 2

def R (r : RationalData) (x : ℝ) : ℝ :=
  r.bu * r.a0 + r.bv * E r + Q r x / 2

def S (r : RationalData) (x : ℝ) : ℝ :=
  r.bu * a2 r x + r.bv * G r x + Q r x / 2

def cubicBracket (r : RationalData) (x : ℝ) : ℝ :=
  H r x + (r.bu + r.bv * F r x) * G r x +
    F r x * (R r x - S r x / 2)

def chiGamma3 (r : RationalData) (x : ℝ) : ℝ :=
  x * chiB0 r x * cubicBracket r x

def betaConstant (r : RationalData) : ℝ :=
  2 * r.bA2 * r.a0 + 3 * r.bA3 / 4

def coefficient (r : RationalData) (x : ℝ) : ℝ :=
  betaConstant r + r.bA2 * a2 r x - chiGamma3 r x

/-- Cleared numerator of the corrected second-harmonic graph coefficient. -/
def n3 (r : RationalData) (x : ℝ) : ℝ :=
  r.bA2 / 2 * r.K * p1 r x * q r x -
    s r x *
      (2 * r.C2 * p1 r x ^ 2 +
        (r.bu * r.K * p1 r x + r.bv * r.K ^ 2) * q r x)

/-- Cleared numerator of the quadratic second-harmonic signal correction. -/
def n2 (r : RationalData) (x : ℝ) : ℝ :=
  r.bA2 / 2 * r.K ^ 2 * p1 r x -
    r.K * s r x * (r.bu * r.K * p1 r x + r.bv * r.K ^ 2) -
    r.K * r.C2 * p1 r x * (4 * x + r.d) / 2

/-- Cleared numerator of the cubic critical projection. -/
def n4 (r : RationalData) (x : ℝ) : ℝ :=
  24 * r.K * r.C2 * r.a0 * p1 r x ^ 2 * delta r x +
    4 * r.C2 * p1 r x * n3 r x +
    9 * r.K * r.C3 * p1 r x ^ 2 * delta r x +
    4 * p1 r x * (r.bu * p1 r x + r.bv * r.K) * n2 r x +
    12 * r.K ^ 2 * (r.bu * r.a0 + r.bv * E r) *
      p1 r x ^ 2 * delta r x -
    2 * r.K * r.bu * p1 r x * n3 r x -
    2 * r.K * r.bv * p1 r x * n2 r x +
    3 * r.K ^ 2 * qNumerator r x * delta r x

/-- The constructed all-parameter numerator `P(x)`. -/
def numerator (r : RationalData) (x : ℝ) : ℝ :=
  -12 * r.K ^ 2 * betaConstant r * p1 r x ^ 2 * delta r x -
    4 * r.K * r.bA2 * p1 r x * n3 r x + s r x * n4 r x

/-- The positive-denominator form used by the manuscript. -/
def denominator (r : RationalData) (x : ℝ) : ℝ :=
  12 * r.K ^ 2 * p1 r x ^ 2 * (4 * x ^ 2 - r.d * r.mu)

theorem sigma2_eq (r : RationalData) {x : ℝ} (hq : q r x ≠ 0) :
    sigma2 r x = 3 * delta r x / q r x := by
  apply (eq_div_iff hq).2
  unfold sigma2 delta s p1
  field_simp [hq] <;> unfold q <;> ring

theorem a2_eq_n3 (r : RationalData) {x : ℝ}
    (hx : x ≠ 0) (hK : r.K ≠ 0) (hp : p1 r x ≠ 0)
    (hq : q r x ≠ 0) (hdelta : delta r x ≠ 0) :
    a2 r x = n3 r x / (3 * r.K * p1 r x * delta r x) := by
  rw [a2, sigma2_eq r hq]
  unfold chiGamma2 chiB0 F n3
  field_simp [hx, hK, hp, hq, hdelta] <;> ring

/-- The cancellation that removes the apparent second-harmonic denominator
from `G`. -/
theorem n2_clear_identity (r : RationalData) (x : ℝ) :
    q r x * n2 r x =
      r.K * n3 r x + 3 * r.K * r.C2 * p1 r x * delta r x / 2 := by
  unfold n2 n3 p1 q s delta
  ring

theorem G_eq_n2 (r : RationalData) {x : ℝ}
    (hx : x ≠ 0) (hK : r.K ≠ 0) (hp : p1 r x ≠ 0)
    (hq : q r x ≠ 0) (hdelta : delta r x ≠ 0) :
    G r x = n2 r x / (3 * r.K * p1 r x * delta r x) := by
  rw [G, a2_eq_n3 r hx hK hp hq hdelta]
  calc
    r.K / q r x *
          (n3 r x / (3 * r.K * p1 r x * delta r x)) +
        r.C2 / (2 * q r x) =
      (r.K * n3 r x +
          3 * r.K * r.C2 * p1 r x * delta r x / 2) /
        (3 * r.K * p1 r x * q r x * delta r x) := by
          field_simp [hK, hp, hq, hdelta] <;> ring
    _ = q r x * n2 r x /
        (3 * r.K * p1 r x * q r x * delta r x) := by
          rw [n2_clear_identity]
    _ = n2 r x / (3 * r.K * p1 r x * delta r x) := by
          field_simp [hK, hp, hq, hdelta] <;> ring

theorem Q_eq_qNumerator (r : RationalData) {x : ℝ}
    (hp : p1 r x ≠ 0) :
    Q r x = qNumerator r x / p1 r x ^ 2 := by
  unfold Q qNumerator F
  field_simp [hp] <;> ring

theorem cubicBracket_eq_n4 (r : RationalData) {x : ℝ}
    (hx : x ≠ 0) (hK : r.K ≠ 0) (hp : p1 r x ≠ 0)
    (hq : q r x ≠ 0) (hdelta : delta r x ≠ 0) :
    cubicBracket r x =
      n4 r x / (12 * r.K * p1 r x ^ 3 * delta r x) := by
  unfold cubicBracket H R S
  rw [a2_eq_n3 r hx hK hp hq hdelta,
    G_eq_n2 r hx hK hp hq hdelta, Q_eq_qNumerator r hp]
  unfold F n4
  field_simp [hK, hp, hdelta] <;> ring

theorem chiGamma3_eq_n4 (r : RationalData) {x : ℝ}
    (hx : x ≠ 0) (hK : r.K ≠ 0) (hp : p1 r x ≠ 0)
    (hq : q r x ≠ 0) (hdelta : delta r x ≠ 0) :
    chiGamma3 r x =
      s r x * n4 r x / (12 * r.K ^ 2 * p1 r x ^ 2 * delta r x) := by
  rw [chiGamma3, cubicBracket_eq_n4 r hx hK hp hq hdelta]
  unfold chiB0
  field_simp [hx, hK, hp, hdelta] <;> ring

theorem coefficient_eq_numerator_div_denominator (r : RationalData) {x : ℝ}
    (hx : x ≠ 0) (hK : r.K ≠ 0) (hp : p1 r x ≠ 0)
    (hq : q r x ≠ 0) (hdelta : delta r x ≠ 0) :
    coefficient r x = numerator r x / denominator r x := by
  rw [coefficient, a2_eq_n3 r hx hK hp hq hdelta,
    chiGamma3_eq_n4 r hx hK hp hq hdelta]
  unfold numerator denominator
  rw [show 4 * x ^ 2 - r.d * r.mu = -delta r x by
    unfold delta
    ring]
  field_simp [hK, hp, hdelta] <;> ring

theorem denominator_pos (r : RationalData) {x : ℝ}
    (hK : r.K ≠ 0) (hp : p1 r x ≠ 0)
    (hdmu : 0 ≤ r.d * r.mu)
    (hx : Real.sqrt (r.d * r.mu) / 2 < x) :
    0 < denominator r x := by
  have hsqrt : 0 ≤ Real.sqrt (r.d * r.mu) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (r.d * r.mu)) ^ 2 = r.d * r.mu :=
    Real.sq_sqrt hdmu
  have hgap : 0 < 4 * x ^ 2 - r.d * r.mu := by
    nlinarith
  unfold denominator
  positivity

end RationalData

/-- The physical non-minimal parameters specialized into the symbolic family. -/
noncomputable def physicalRationalData
    (p : PhysicalParams) (beta : ℝ) : RationalData :=
  let t := mobilityScaledTaylor p beta
  let t0 := mobilityScaledTaylor p 0
  { d := p.logisticSlope
    mu := p.mu
    K := t0.Cprime
    C2 := t0.Csecond
    C3 := t0.Cthird
    bA2 := t.bAsecond
    bA3 := t.bAthird
    bu := t.BuOverB0
    bv := t.BvOverB0
    buu := t.BuuOverB0
    buv := t.BuvOverB0
    bvv := t.BvvOverB0
    a0 := logisticA0 p }

/-- The symbolic threshold factor is the physical mobility-scaled threshold. -/
theorem physical_chiB0 (p : PhysicalParams) (x beta : ℝ) :
    (physicalRationalData p beta).chiB0 x = chiStarTimesB0 p x := by
  rfl

/-- The symbolic second-mode rate is the physical second-mode rate. -/
theorem physical_sigma2 (p : PhysicalParams) (x beta : ℝ) :
    (physicalRationalData p beta).sigma2 x =
      ChemotaxisBifurcation.sigma2 p x := by
  rfl

/-- The symbolic first signal mode is the physical first signal mode. -/
theorem physical_F (p : PhysicalParams) (x beta : ℝ) :
    (physicalRationalData p beta).F x = cubicF p x := by
  rfl

/-- The symbolic quadratic chemotactic product is the physical one. -/
theorem physical_chiGamma2 (p : PhysicalParams) (x beta : ℝ)
    (hq : p.mu + 4 * x ≠ 0) :
    (physicalRationalData p beta).chiGamma2 x =
      ChemotaxisBifurcation.chiGamma2 p x beta := by
  change
    x * chiStarTimesB0 p x *
        (2 * (mobilityScaledTaylor p 0).Csecond / (p.mu + 4 * x) +
          (mobilityScaledTaylor p beta).BuOverB0 * signalMode1 p x +
          (mobilityScaledTaylor p beta).BvOverB0 * signalMode1 p x ^ 2) =
      x * chiStarTimesB0 p x *
        (4 * signalMode2 p (4 * x) +
          (mobilityScaledTaylor p beta).BuOverB0 * signalMode1 p x +
          (mobilityScaledTaylor p beta).BvOverB0 * signalMode1 p x ^ 2)
  unfold signalMode2
  field_simp [hq] <;> ring

/-- The symbolic corrected second-harmonic jet is the physical jet. -/
theorem physical_a2 (p : PhysicalParams) (x beta : ℝ)
    (hq : p.mu + 4 * x ≠ 0) :
    (physicalRationalData p beta).a2 x = secondModeA2 p x beta := by
  calc
    (physicalRationalData p beta).a2 x =
        ((physicalRationalData p beta).bA2 / 2 -
          (physicalRationalData p beta).chiGamma2 x) /
          (physicalRationalData p beta).sigma2 x := rfl
    _ = ((mobilityScaledTaylor p beta).bAsecond / 2 -
          ChemotaxisBifurcation.chiGamma2 p x beta) /
          ChemotaxisBifurcation.sigma2 p x := by
            rw [physical_chiGamma2 p x beta hq, physical_sigma2]
            rfl
    _ = secondModeA2 p x beta := rfl

/-- The symbolic constant signal correction is the physical one. -/
theorem physical_E (p : PhysicalParams) (x beta : ℝ)
    (hmu : p.mu ≠ 0) :
    (physicalRationalData p beta).E =
      cubicE p (logisticQuadraticJet p x beta) := by
  change
    (mobilityScaledTaylor p 0).Cprime / p.mu * logisticA0 p +
        (mobilityScaledTaylor p 0).Csecond / (2 * p.mu) =
      signalMode1 p 0 * logisticA0 p + signalMode2 p 0
  unfold signalMode1 signalMode2
  field_simp [hmu] <;> ring

/-- The symbolic second-harmonic signal correction is the physical one. -/
theorem physical_G (p : PhysicalParams) (x beta : ℝ)
    (hq : p.mu + 4 * x ≠ 0) :
    (physicalRationalData p beta).G x =
      cubicG p x (logisticQuadraticJet p x beta) := by
  calc
    (physicalRationalData p beta).G x =
        (physicalRationalData p beta).K /
            (physicalRationalData p beta).q x *
            (physicalRationalData p beta).a2 x +
          (physicalRationalData p beta).C2 /
            (2 * (physicalRationalData p beta).q x) := rfl
    _ = signalMode1 p (4 * x) * secondModeA2 p x beta +
        signalMode2 p (4 * x) := by
          rw [physical_a2 p x beta hq]
          unfold physicalRationalData RationalData.q signalMode1 signalMode2
          field_simp [hq] <;> ring
    _ = cubicG p x (logisticQuadraticJet p x beta) := rfl

/-- The symbolic critical cubic signal correction is the physical one. -/
theorem physical_H (p : PhysicalParams) (x beta : ℝ)
    (hp : p.mu + x ≠ 0) (hq : p.mu + 4 * x ≠ 0) :
    (physicalRationalData p beta).H x =
      cubicH p x (logisticQuadraticJet p x beta) := by
  calc
    (physicalRationalData p beta).H x =
        (physicalRationalData p beta).C2 /
            (physicalRationalData p beta).p1 x *
            (2 * (physicalRationalData p beta).a0 +
              (physicalRationalData p beta).a2 x) +
          3 * (physicalRationalData p beta).C3 /
            (4 * (physicalRationalData p beta).p1 x) := rfl
    _ = 2 * signalMode2 p x *
          (2 * logisticA0 p + secondModeA2 p x beta) +
        3 * signalMode3 p x := by
          rw [physical_a2 p x beta hq]
          unfold physicalRationalData RationalData.p1 signalMode2 signalMode3
          field_simp [hp] <;> ring
    _ = cubicH p x (logisticQuadraticJet p x beta) := rfl

/-- The symbolic normalized mobility aggregate is the physical one. -/
theorem physical_Q (p : PhysicalParams) (x beta : ℝ) :
    (physicalRationalData p beta).Q x = cubicQOverB0 p x beta := by
  calc
    (physicalRationalData p beta).Q x =
        (physicalRationalData p beta).buu +
          (physicalRationalData p beta).buv *
            (physicalRationalData p beta).F x +
          (physicalRationalData p beta).bvv *
            (physicalRationalData p beta).F x ^ 2 := rfl
    _ = (mobilityScaledTaylor p beta).BuuOverB0 +
          (mobilityScaledTaylor p beta).BuvOverB0 * cubicF p x +
          (mobilityScaledTaylor p beta).BvvOverB0 * cubicF p x ^ 2 := by
            rw [physical_F p x beta]
            rfl
    _ = cubicQOverB0 p x beta := rfl

/-- The symbolic `R/B₀` aggregate is the physical one. -/
theorem physical_R (p : PhysicalParams) (x beta : ℝ)
    (hmu : p.mu ≠ 0) :
    (physicalRationalData p beta).R x =
      cubicROverB0 p x beta (logisticQuadraticJet p x beta) := by
  calc
    (physicalRationalData p beta).R x =
        (physicalRationalData p beta).bu *
            (physicalRationalData p beta).a0 +
          (physicalRationalData p beta).bv *
            (physicalRationalData p beta).E +
          (physicalRationalData p beta).Q x / 2 := rfl
    _ = (mobilityScaledTaylor p beta).BuOverB0 * logisticA0 p +
          (mobilityScaledTaylor p beta).BvOverB0 *
            cubicE p (logisticQuadraticJet p x beta) +
          cubicQOverB0 p x beta / 2 := by
            rw [physical_E p x beta hmu, physical_Q p x beta]
            rfl
    _ = cubicROverB0 p x beta (logisticQuadraticJet p x beta) := rfl

/-- The symbolic `S/B₀` aggregate is the physical one. -/
theorem physical_S (p : PhysicalParams) (x beta : ℝ)
    (hq : p.mu + 4 * x ≠ 0) :
    (physicalRationalData p beta).S x =
      cubicSOverB0 p x beta (logisticQuadraticJet p x beta) := by
  calc
    (physicalRationalData p beta).S x =
        (physicalRationalData p beta).bu *
            (physicalRationalData p beta).a2 x +
          (physicalRationalData p beta).bv *
            (physicalRationalData p beta).G x +
          (physicalRationalData p beta).Q x / 2 := rfl
    _ = (mobilityScaledTaylor p beta).BuOverB0 * secondModeA2 p x beta +
          (mobilityScaledTaylor p beta).BvOverB0 *
            cubicG p x (logisticQuadraticJet p x beta) +
          cubicQOverB0 p x beta / 2 := by
            rw [physical_a2 p x beta hq, physical_G p x beta hq,
              physical_Q p x beta]
            rfl
    _ = cubicSOverB0 p x beta (logisticQuadraticJet p x beta) := rfl

/-- The symbolic cubic chemotactic product is the physical one. -/
theorem physical_chiGamma3 (p : PhysicalParams) (x beta : ℝ)
    (hmu : p.mu ≠ 0) (hp : p.mu + x ≠ 0)
    (hq : p.mu + 4 * x ≠ 0) :
    (physicalRationalData p beta).chiGamma3 x =
      ChemotaxisBifurcation.chiGamma3 p x beta
        (logisticQuadraticJet p x beta) := by
  calc
    (physicalRationalData p beta).chiGamma3 x =
        x * (physicalRationalData p beta).chiB0 x *
          ((physicalRationalData p beta).H x +
            ((physicalRationalData p beta).bu +
              (physicalRationalData p beta).bv *
                (physicalRationalData p beta).F x) *
              (physicalRationalData p beta).G x +
            (physicalRationalData p beta).F x *
              ((physicalRationalData p beta).R x -
                (physicalRationalData p beta).S x / 2)) := rfl
    _ = x * chiStarTimesB0 p x *
          (cubicH p x (logisticQuadraticJet p x beta) +
            ((mobilityScaledTaylor p beta).BuOverB0 +
              (mobilityScaledTaylor p beta).BvOverB0 * cubicF p x) *
              cubicG p x (logisticQuadraticJet p x beta) +
            cubicF p x *
              (cubicROverB0 p x beta (logisticQuadraticJet p x beta) -
                cubicSOverB0 p x beta (logisticQuadraticJet p x beta) / 2)) := by
          rw [physical_chiB0, physical_H p x beta hp hq, physical_F,
            physical_G p x beta hq, physical_R p x beta hmu,
            physical_S p x beta hq]
          rfl
    _ = ChemotaxisBifurcation.chiGamma3 p x beta
        (logisticQuadraticJet p x beta) := rfl

/-- The symbolic family is the physical cubic chain after mobility scaling. -/
theorem logisticBetaCoefficient_eq_symbolic
    (p : PhysicalParams) (x beta : ℝ)
    (hmu : p.mu ≠ 0) (hp : p.mu + x ≠ 0)
    (hq : p.mu + 4 * x ≠ 0) :
    logisticBetaCoefficient p x beta =
      (physicalRationalData p beta).coefficient x := by
  unfold logisticBetaCoefficient betaCoefficient RationalData.coefficient
  rw [physical_a2 p x beta hq,
    physical_chiGamma3 p x beta hmu hp hq]
  change
    (mobilityScaledTaylor p beta).bAsecond / 2 *
          (4 * logisticA0 p + 2 * secondModeA2 p x beta) -
        ChemotaxisBifurcation.chiGamma3 p x beta
          (logisticQuadraticJet p x beta) +
        3 * (mobilityScaledTaylor p beta).bAthird / 4 =
      (2 * (mobilityScaledTaylor p beta).bAsecond * logisticA0 p +
          3 * (mobilityScaledTaylor p beta).bAthird / 4) +
        (mobilityScaledTaylor p beta).bAsecond * secondModeA2 p x beta -
        ChemotaxisBifurcation.chiGamma3 p x beta
          (logisticQuadraticJet p x beta)
  ring

/-- Equation 1.12 at the physical non-minimal interface.  The numerator is
constructed from the corrected quadratic and cubic coefficient chain. -/
theorem logisticBetaCoefficient_eq_numerator_div_denominator
    (p : PhysicalParams) (x beta : ℝ)
    (hx : x ≠ 0)
    (hK : (mobilityScaledTaylor p 0).Cprime ≠ 0)
    (hmu : p.mu ≠ 0)
    (hp : p.mu + x ≠ 0)
    (hq : p.mu + 4 * x ≠ 0)
    (hdelta : p.logisticSlope * p.mu - 4 * x ^ 2 ≠ 0) :
    logisticBetaCoefficient p x beta =
      (physicalRationalData p beta).numerator x /
        (physicalRationalData p beta).denominator x := by
  rw [logisticBetaCoefficient_eq_symbolic p x beta hmu hp hq]
  apply RationalData.coefficient_eq_numerator_div_denominator
  · exact hx
  · exact hK
  · simpa [physicalRationalData, RationalData.p1] using hp
  · simpa [physicalRationalData, RationalData.q] using hq
  · simpa [physicalRationalData, RationalData.delta] using hdelta

end

end ChemotaxisBifurcation.RationalCoefficient
