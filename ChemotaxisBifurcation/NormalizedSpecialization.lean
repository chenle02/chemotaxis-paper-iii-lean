module
public import ChemotaxisBifurcation.RationalCoefficient
public import ChemotaxisBifurcation.SpecializedPolynomial

@[expose] public section

/-!
# All-ones specialization of the constructed rational coefficient

This module connects the generic coefficient assembled from the finite Taylor
and projection chain to the normalized `P/Q` formulas displayed in the
all-ones example.  It is an algebraic specialization; it does not add an
analytic center-manifold or PDE existence claim.
-/

namespace ChemotaxisBifurcation.NormalizedSpecialization

open ChemotaxisBifurcation
open ChemotaxisBifurcation.RationalCoefficient
open ChemotaxisBifurcation.RationalCoefficient.RationalData
open ChemotaxisBifurcation.SpecializedPolynomial

noncomputable section

/-- Physical parameters of the manuscript's all-ones example. -/
def allOnesParams : PhysicalParams where
  a := 1
  b := 1
  alpha := 1
  m := 1
  gamma := 1
  nu := 1
  mu := 1
  uStar := 1
  vStar := 1

/-- The generic rational data after specializing all physical parameters to
one while retaining the sensitivity exponent `beta`. -/
def allOnesRationalData (beta : ℝ) : RationalData where
  d := 1
  mu := 1
  K := 1
  C2 := 0
  C3 := 0
  bA2 := 1
  bA3 := 0
  bu := 1
  bv := -beta / 2
  buu := 0
  buv := -beta / 2
  bvv := beta * (beta + 1) / 8
  a0 := -1 / 2

theorem physicalRationalData_allOnes (beta : ℝ) :
    physicalRationalData allOnesParams beta = allOnesRationalData beta := by
  norm_num [physicalRationalData, allOnesParams, allOnesRationalData,
    mobilityScaledTaylor, logisticA0, PhysicalParams.signalOffset,
    PhysicalParams.logisticSlope]

/-- The constructed generic numerator specializes to the displayed quartic,
up to the common positive factor `(1+x)/8`. -/
theorem numerator_allOnes (x beta : ℝ) :
    (allOnesRationalData beta).numerator x =
      (1 + x) * SpecializedPolynomial.numerator x beta / 8 := by
  norm_num [allOnesRationalData, RationalData.numerator, RationalData.n4,
    RationalData.n3, RationalData.n2, RationalData.qNumerator,
    RationalData.betaConstant, RationalData.E, RationalData.p1,
    RationalData.q, RationalData.s, RationalData.delta,
    SpecializedPolynomial.numerator]
  ring

/-- The constructed generic denominator has the same common factor. -/
theorem denominator_allOnes (x beta : ℝ) :
    (allOnesRationalData beta).denominator x =
      (1 + x) * SpecializedPolynomial.denominator x / 8 := by
  norm_num [allOnesRationalData, RationalData.denominator,
    RationalData.p1, SpecializedPolynomial.denominator]
  ring

/-- Consequently the constructed generic rational function is exactly the
normalized displayed coefficient away from the canceled factor `1+x`. -/
theorem ratio_allOnes {x beta : ℝ} (hx : 1 + x ≠ 0)
    (hden : SpecializedPolynomial.denominator x ≠ 0) :
    (allOnesRationalData beta).numerator x /
        (allOnesRationalData beta).denominator x =
      SpecializedPolynomial.coefficient x beta := by
  rw [numerator_allOnes, denominator_allOnes]
  unfold SpecializedPolynomial.coefficient
  field_simp [hx, hden]

/-- On the manuscript's admissible half-line, every denominator and canceled
factor needed by the specialization is nonzero. -/
theorem ratio_allOnes_of_half_lt {x beta : ℝ} (hx : 1 / 2 < x) :
    (allOnesRationalData beta).numerator x /
        (allOnesRationalData beta).denominator x =
      SpecializedPolynomial.coefficient x beta := by
  apply ratio_allOnes
  · linarith
  · exact ne_of_gt (SpecializedPolynomial.denominator_pos hx)

/-- The physical all-ones specialization reaches the normalized displayed
coefficient through the generic rational construction. -/
theorem physical_ratio_allOnes_of_half_lt {x beta : ℝ} (hx : 1 / 2 < x) :
    (physicalRationalData allOnesParams beta).numerator x /
        (physicalRationalData allOnesParams beta).denominator x =
      SpecializedPolynomial.coefficient x beta := by
  rw [physicalRationalData_allOnes]
  exact ratio_allOnes_of_half_lt hx

/-- The actual logistic cubic coefficient in the all-ones physical model is
the manuscript's normalized `P/Q` expression on the admissible half-line. -/
theorem logisticBetaCoefficient_allOnes {x beta : ℝ} (hx : 1 / 2 < x) :
    logisticBetaCoefficient allOnesParams x beta =
      SpecializedPolynomial.coefficient x beta := by
  rw [RationalCoefficient.logisticBetaCoefficient_eq_numerator_div_denominator
    allOnesParams x beta]
  · exact physical_ratio_allOnes_of_half_lt hx
  · linarith
  · norm_num [allOnesParams, mobilityScaledTaylor]
  · norm_num [allOnesParams]
  · norm_num [allOnesParams]
    linarith
  · norm_num [allOnesParams]
    linarith
  · norm_num [allOnesParams, PhysicalParams.logisticSlope]
    nlinarith

/-- Evaluation at `x=1` is exactly the displayed large-domain coefficient.
The numerator and denominator respectively reduce to
`576 - 369 beta - 25 beta^2` and `576`. -/
theorem coefficient_one_eq_betaInfinity (beta : ℝ) :
    SpecializedPolynomial.coefficient 1 beta =
      SpecializedPolynomial.betaInfinity beta := by
  norm_num [SpecializedPolynomial.coefficient,
    SpecializedPolynomial.numerator, SpecializedPolynomial.denominator,
    SpecializedPolynomial.betaInfinity]
  ring

/-- The actual all-ones logistic coefficient at `x=1` therefore equals the
manuscript's large-domain limiting coefficient. -/
theorem logisticBetaCoefficient_allOnes_one (beta : ℝ) :
    logisticBetaCoefficient allOnesParams 1 beta =
      SpecializedPolynomial.betaInfinity beta := by
  rw [logisticBetaCoefficient_allOnes (by norm_num : (1 / 2 : ℝ) < 1),
    coefficient_one_eq_betaInfinity]

end

end ChemotaxisBifurcation.NormalizedSpecialization
