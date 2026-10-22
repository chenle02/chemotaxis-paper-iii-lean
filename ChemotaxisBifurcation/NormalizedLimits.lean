module
public import ChemotaxisBifurcation.NormalizedSpecialization
public import ChemotaxisBifurcation.SmallDomainRate

@[expose] public section

/-!
# Exact all-ones critical constants and actual domain limits

The values 7/3 and -61/144 are specializations of the general formulas, rather
than independent definitions of the expected answers.
-/
namespace ChemotaxisBifurcation.NormalizedSpecialization

open Filter Asymptotics SmallDomain CoefficientLimits PhysicalModeGuards
open scoped Topology
noncomputable section

theorem allOnes_admissible : allOnesParams.LogisticAdmissible := by
  norm_num [PhysicalParams.LogisticAdmissible, PhysicalParams.EquilibriumRelations,
    PhysicalParams.LogisticEquilibrium, PhysicalParams.SignalEquilibrium, allOnesParams]

theorem cSD_allOnes (beta : ℝ) :
    cSD allOnesParams beta = (7 - 3 * beta) / 12 := by
  norm_num [cSD, scriptP, h, D, PhysicalParams.signalOffset, allOnesParams]
  ring

theorem betaSD_allOnes : betaSD allOnesParams = (7 / 3 : ℝ) := by
  norm_num [betaSD, scriptP, h, D, PhysicalParams.signalOffset, allOnesParams]

theorem dBeta_allOnes (beta : ℝ) :
    dBeta allOnesParams beta = -(4 + 7 * beta) / 48 := by
  norm_num [dBeta, scriptT0, h, tauBeta, D, PhysicalParams.logisticSlope,
    PhysicalParams.signalOffset, allOnesParams]
  ring

theorem dStar_allOnes : dStar allOnesParams = (-61 / 144 : ℝ) := by
  norm_num [dStar, scriptT, scriptM, h, D, PhysicalParams.logisticSlope, allOnesParams]

theorem balancingEigenvalue_allOnes : balancingEigenvalue allOnesParams = 1 := by
  norm_num [balancingEigenvalue, PhysicalParams.logisticSlope, allOnesParams]

/-- The finite critical value is the limit along actual admissible lengths. -/
theorem allOnes_critical_small_domain_limit {d : ℝ → ModeData}
    (hLength : ∀ᶠ L in 𝓝[>] (0 : ℝ), (d L).L = L)
    (hs : ∀ᶠ L in 𝓝[>] (0 : ℝ), StrictCriticalMode allOnesParams (d L) (7 / 3)) :
    Tendsto (fun L => logisticBetaCoefficient allOnesParams (d L).eigenvalue (7 / 3))
      (𝓝[>] 0) (𝓝 (-61 / 144 : ℝ)) := by
  have hs' : ∀ᶠ L in 𝓝[>] (0 : ℝ),
      StrictCriticalMode allOnesParams (d L) (betaSD allOnesParams) := by
    simpa only [betaSD_allOnes] using hs
  have hlim := physical_critical_coefficient_tendsto_small_domain_of_D_pos
    allOnesParams allOnes_admissible
    (by norm_num [D, allOnesParams])
    (by norm_num [scriptP, h, allOnesParams]) hLength hs'
  simpa only [betaSD_allOnes, dStar_allOnes] using hlim

/-- The critical -61/144 value has the manuscript's O(L²) error. -/
theorem allOnes_critical_small_domain_rate
    {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hL : Tendsto (fun i => (d i).L) l (𝓝[>] (0 : ℝ)))
    (hs : ∀ᶠ i in l, StrictCriticalMode allOnesParams (d i) (7 / 3)) :
    (fun i => logisticBetaCoefficient allOnesParams (d i).eigenvalue (7 / 3) + 61 / 144)
      =O[l] (fun i => (d i).L ^ 2) := by
  have hr := physical_small_domain_error_isBigO_length_sq
    allOnesParams (7 / 3) allOnes_admissible hL hs
  norm_num [cSD_allOnes, dBeta_allOnes] at hr
  exact hr

/-- The displayed large-domain quadratic is the actual limiting coefficient. -/
theorem allOnes_large_domain_limit (beta : ℝ)
    {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hL : Tendsto (fun i => (d i).L) l atTop)
    (hs : ∀ᶠ i in l, StrictCriticalMode allOnesParams (d i) beta) :
    Tendsto (fun i => logisticBetaCoefficient allOnesParams (d i).eigenvalue beta)
      l (𝓝 (SpecializedPolynomial.betaInfinity beta)) := by
  have hlim := physical_critical_coefficient_tendsto_large_domain
    allOnesParams beta allOnes_admissible hs hL
  simpa only [balancingEigenvalue_allOnes, logisticBetaCoefficient_allOnes_one] using hlim


/-- Exact rounding cell for the displayed large-domain threshold 1.423658. -/
theorem betaLargeDomain_rounding_cell :
    SpecializedPolynomial.betaLargeDomain ∈
      Set.Ioo (14236575 / 10000000 : ℝ) (14236585 / 10000000 : ℝ) := by
  have hs := SpecializedPolynomial.sqrt_21529_sq
  have hp := Real.sqrt_nonneg (21529 : ℝ)
  have hlo : (50 * (14236575 / 10000000 : ℝ) + 369) / 3 < Real.sqrt 21529 := by
    apply (sq_lt_sq₀ (by norm_num) hp).mp
    rw [hs]
    norm_num
  have hhi : Real.sqrt 21529 < (50 * (14236585 / 10000000 : ℝ) + 369) / 3 := by
    apply (sq_lt_sq₀ hp (by norm_num)).mp
    rw [hs]
    norm_num
  constructor <;> unfold SpecializedPolynomial.betaLargeDomain <;> linarith

end
end ChemotaxisBifurcation.NormalizedSpecialization
