module
public import ChemotaxisBifurcation.CubicAssembly
public import ChemotaxisBifurcation.SmallDomain

@[expose] public section

/-!
# Two counterexamples to Remark 1.2(2) (arXiv v1, p. 9)

Remark 1.2(2) of arXiv:2610.20976v1 makes two claims about the domain-length dependence of the
cubic coefficient `β_{n₀}` of Theorem 1.2(2) that are false as written. Theorem 1.2(2) itself is
not affected. This module gives exact counterexamples built from the same algebraic coefficient
interface (`CubicAssembly`) that the rest of the companion uses.

* **No switching for large `k` needs `β_∞ ≠ 0`** (v1 TeX line 828). The remark says that, for large
  `k`, the bifurcation type does not switch as `L` moves through `(L_{k-1}, L_k)`. Example 3.1
  (`a = b = μ = ν = m = α = γ = 1`, so `√(aαμ) = 1`) at `β = β_ld = (3√21529 - 369)/50` is a
  counterexample: the coefficient equals `P̃(λ, β)/(96(1+λ)(4λ²-1))` (`logistic_example`), `P̃(·, β_ld)`
  has a simple zero at `λ = 1` (`Ptilde_one_betaLd`, `Ptilde_factor`), and the coefficient is
  positive just below `λ = 1` and negative just above it (`sign_change_at_one`). Since `λ_k = 1` at
  `L = kπ` and `L_{k-1} < kπ < L_k` for every `k ≥ 2` (Eq. 1.11), the type switches inside every
  admissible interval. Here `β_∞ = 0`; Theorem 1.2(2)(ii) assumes `β_∞ ≠ 0` and is correct.
  The interval inclusion `L_{k-1} < kπ < L_k` is the paper's Eq. 1.11 and is not restated here.

* **(1.16)-(1.17) hold only in the non-minimal model** (v1 TeX lines 835-854). The formula
  `c = (𝖯 - 6βγDv*/(1+v*))/(24(u*)²)` (`SmallDomain.cSD`) is the small-domain coefficient of the
  logistic model only. For the fixed-mass minimal model with `u* = v* = m = γ = μ = ν = 1` and
  `β = 3`, the actual coefficient is `(x³/12 + 7x²/16 - x/32 - 1/96)/(x+1)²` for every value of the
  unused parameter `α` (`fixedMass_beta3`), so `β₁/λ → 1/12` (`fixedMass_beta3_div_tendsto`), while
  (1.16) gives `-(3α+1)/24 < 0` (`cSD_pMin`): the opposite small-domain bifurcation type
  (`small_domain_formula_fails_minimal`).

Both findings were found by an AI reading of the paper and are recorded as `manuscript_findings`
of the Theorem 1.2(2) ledger row; the revision of 2026-10-17 restricts both statements.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.RemarkFindings

open ChemotaxisBifurcation Filter Topology

/-! ## The small-domain formula (1.16) in the minimal model -/

/-- Minimal-model parameters `a = b = 0`, `m = γ = ν = μ = u* = v* = 1`, with the logistic exponent
`α` left free: it does not enter the minimal model but does enter (1.16). -/
def pMin (al : ℝ) : PhysicalParams :=
  { a := 0, b := 0, alpha := al, m := 1, gamma := 1, nu := 1, mu := 1, uStar := 1, vStar := 1 }

theorem pMin_admissible (al : ℝ) : (pMin al).FixedMassAdmissible := by
  refine ⟨rfl, rfl, by norm_num [pMin], by norm_num [pMin], by norm_num [pMin], by norm_num [pMin],
    by norm_num [pMin], by norm_num [pMin], ?_⟩
  simp [PhysicalParams.SignalEquilibrium, pMin]

/-- The minimal-model cubic coefficient at `β = 3`, exactly, for every `α`. -/
theorem fixedMass_beta3 (al x : ℝ) (hx : 0 < x) :
    fixedMassBetaCoefficient (pMin al) x 3 =
      (x ^ 3 / 12 + 7 / 16 * x ^ 2 - x / 32 - 1 / 96) / (x + 1) ^ 2 := by
  have h1 : x + 1 ≠ 0 := by positivity
  have h2 : 1 + 4 * x ≠ 0 := by positivity
  have h3 : x ≠ 0 := hx.ne'
  simp only [fixedMassBetaCoefficient, betaCoefficient, chiGamma3, fixedMassQuadraticJet,
    quadraticJetData, fixedMassA0, secondModeA2, chiGamma2, sigma2, signalMode1, signalMode2,
    signalMode3, cubicE, cubicF, cubicG, cubicH, cubicROverB0, cubicSOverB0, cubicQOverB0,
    chiStarTimesB0, mobilityScaledTaylor, PhysicalParams.signalOffset,
    PhysicalParams.logisticSlope, pMin]
  simp only [add_zero, sub_zero, zero_mul, mul_zero, zero_add, zero_div]
  have hs : -4 * x + 4 * x * (1 + x) / (1 + 4 * x) = -12 * x ^ 2 / (1 + 4 * x) := by
    field_simp; ring
  rw [hs]
  have h5 : (12 : ℝ) * x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The actual minimal small-domain coefficient is `1/12`: `β₁(λ)/λ → 1/12` as `λ → ∞`. -/
theorem fixedMass_beta3_div_tendsto (al : ℝ) :
    Tendsto (fun x : ℝ => fixedMassBetaCoefficient (pMin al) x 3 / x) atTop (𝓝 (1 / 12)) := by
  have hev : (fun x : ℝ => fixedMassBetaCoefficient (pMin al) x 3 / x) =ᶠ[atTop]
      (fun x : ℝ => (1 / 12 + 7 / 16 * x⁻¹ - 1 / 32 * x⁻¹ ^ 2 - 1 / 96 * x⁻¹ ^ 3) /
        (1 + x⁻¹) ^ 2) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [fixedMass_beta3 al x hx]
    have : x ≠ 0 := hx.ne'
    have : x + 1 ≠ 0 := by positivity
    field_simp
  rw [tendsto_congr' hev]
  have h0 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have := ((((tendsto_const_nhds (x := (1 / 12 : ℝ))).add (h0.const_mul (7 / 16))).sub
    ((h0.pow 2).const_mul (1 / 32))).sub ((h0.pow 3).const_mul (1 / 96))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add h0 |>.pow 2) (by norm_num)
  convert this using 1
  norm_num

/-- Formula (1.16) evaluated at the minimal parameters gives `-(3α+1)/24`. -/
theorem cSD_pMin (al : ℝ) : SmallDomain.cSD (pMin al) 3 = -(3 * al + 1) / 24 := by
  simp only [SmallDomain.cSD, SmallDomain.scriptP, SmallDomain.h, SmallDomain.D,
    PhysicalParams.signalOffset, pMin]
  ring

/-- (1.16) fails in the minimal model: for every `α > 0` it predicts a negative small-domain
coefficient, while the actual minimal coefficient is `1/12 > 0`. -/
theorem small_domain_formula_fails_minimal (al : ℝ) (hal : 0 < al) :
    SmallDomain.cSD (pMin al) 3 < 0 ∧
      Tendsto (fun x : ℝ => fixedMassBetaCoefficient (pMin al) x 3 / x) atTop (𝓝 (1 / 12)) := by
  refine ⟨?_, fixedMass_beta3_div_tendsto al⟩
  rw [cSD_pMin]
  linarith

/-! ## Switching in every admissible interval when `β_∞ = 0` (Example 3.1) -/

/-- The numerator `P̃(λ, β)` displayed in Example 3.1. -/
def Ptilde (l b : ℝ) : ℝ :=
  (224 - 96 * b) * l ^ 4 + (192 - 152 * b) * l ^ 3 + (8 - 104 * b - 16 * b ^ 2) * l ^ 2
    + (96 - 28 * b - 8 * b ^ 2) * l + 56 + 11 * b - b ^ 2

/-- Example 3.1 parameters `a = b = μ = ν = m = α = γ = 1`, `u* = v* = 1`. -/
def pEx : PhysicalParams :=
  { a := 1, b := 1, alpha := 1, m := 1, gamma := 1, nu := 1, mu := 1, uStar := 1, vStar := 1 }

/-- The non-minimal coefficient of Example 3.1 is `P̃(λ, β)/(96(1+λ)(4λ²-1))` for `λ > 1/2`. -/
theorem logistic_example (x b : ℝ) (hx : 1 / 2 < x) :
    logisticBetaCoefficient pEx x b = Ptilde x b / (96 * (1 + x) * (4 * x ^ 2 - 1)) := by
  have h1 : (0 : ℝ) < x := by linarith
  have h2 : 4 * x ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : (1 : ℝ) + x ≠ 0 := by linarith
  have h4 : (1 : ℝ) + 4 * x ≠ 0 := by linarith
  have h5 : x ≠ 0 := h1.ne'
  have h6 : (1 : ℝ) - 4 * x ^ 2 ≠ 0 := by nlinarith
  simp only [logisticBetaCoefficient, betaCoefficient, chiGamma3, logisticQuadraticJet,
    quadraticJetData, logisticA0, secondModeA2, chiGamma2, sigma2, signalMode1, signalMode2,
    signalMode3, cubicE, cubicF, cubicG, cubicH, cubicROverB0, cubicSOverB0, cubicQOverB0,
    chiStarTimesB0, mobilityScaledTaylor, PhysicalParams.signalOffset,
    PhysicalParams.logisticSlope, pEx, Ptilde]
  have hs : -4 * x - 1 * 1 + 4 * (x + 1 * 1) * (1 + x) / (1 + 4 * x) =
      (1 - 4 * x ^ 2) * 3 / (1 + 4 * x) := by field_simp; ring
  rw [hs]
  field_simp
  ring

/-- `β_ld = (3√21529 - 369)/50`, the large-domain threshold of Example 3.1. -/
noncomputable def betaLd : ℝ := (3 * Real.sqrt 21529 - 369) / 50

/-- At `β = β_ld` the numerator vanishes at `λ = 1 = √(aαμ)`, so `β_∞ = 0`. -/
theorem Ptilde_one_betaLd : Ptilde 1 betaLd = 0 := by
  have hs : Real.sqrt 21529 ^ 2 = 21529 := Real.sq_sqrt (by norm_num)
  simp only [Ptilde, betaLd]
  nlinarith [hs]

theorem betaLd_bounds : 1.42 < betaLd ∧ betaLd < 1.43 := by
  have hs : Real.sqrt 21529 ^ 2 = 21529 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 21529 := Real.sqrt_nonneg _
  constructor <;> simp only [betaLd] <;> nlinarith

/-- `P̃(·, β_ld) = (λ - 1) g(λ)`. -/
theorem Ptilde_factor (l : ℝ) : Ptilde l betaLd = (l - 1) *
    ((224 - 96 * betaLd) * (l ^ 3 + l ^ 2 + l + 1) + (192 - 152 * betaLd) * (l ^ 2 + l + 1)
      + (8 - 104 * betaLd - 16 * betaLd ^ 2) * (l + 1) + (96 - 28 * betaLd - 8 * betaLd ^ 2)) := by
  have h := Ptilde_one_betaLd
  simp only [Ptilde] at h ⊢
  linear_combination h

/-- At `β = β_ld` the coefficient of Example 3.1 is positive just below `λ = 1` and negative just
above it: the bifurcation type switches at `λ_k = 1`, i.e. at `L = kπ`, inside every admissible
interval `(L_{k-1}, L_k)`, `k ≥ 2`. -/
theorem sign_change_at_one :
    ∃ δ > 0, ∀ x, 1 - δ < x → x < 1 + δ →
      (x < 1 → 0 < logisticBetaCoefficient pEx x betaLd) ∧
      (1 < x → logisticBetaCoefficient pEx x betaLd < 0) := by
  obtain ⟨hb1, hb2⟩ := betaLd_bounds
  refine ⟨1 / 100, by norm_num, fun x hx1 hx2 => ?_⟩
  have hx : (1 : ℝ) / 2 < x := by linarith
  have hg : (224 - 96 * betaLd) * (x ^ 3 + x ^ 2 + x + 1) + (192 - 152 * betaLd) * (x ^ 2 + x + 1)
      + (8 - 104 * betaLd - 16 * betaLd ^ 2) * (x + 1)
      + (96 - 28 * betaLd - 8 * betaLd ^ 2) < 0 := by
    have a1 : (0 : ℝ) < x - 0.99 := by linarith
    have a2 : (0 : ℝ) < 1.01 - x := by linarith
    have b1 : (0 : ℝ) < betaLd - 1.42 := by linarith
    have b2 : (0 : ℝ) < 1.43 - betaLd := by linarith
    have x0 : (0 : ℝ) < x := by linarith
    nlinarith [mul_pos a1 b1, mul_pos a1 b2, mul_pos a2 b1, mul_pos a2 b2, mul_pos b1 b2,
      mul_pos a1 a2, mul_pos (mul_pos a1 a1) b1, mul_pos (mul_pos a2 a2) b2,
      mul_pos (mul_pos x0 x0) b1, mul_pos (mul_pos x0 x0) b2, mul_pos (mul_pos x0 x0) x0,
      mul_pos (mul_pos (mul_pos x0 x0) x0) b1, mul_pos (mul_pos (mul_pos x0 x0) x0) b2,
      mul_pos (mul_pos x0 b1) b1, mul_pos (mul_pos x0 b2) b2, mul_pos (mul_pos x0 b1) b2]
  have hden : 0 < 96 * (1 + x) * (4 * x ^ 2 - 1) := by
    have : 0 < 4 * x ^ 2 - 1 := by nlinarith
    positivity
  rw [logistic_example x betaLd hx, Ptilde_factor]
  constructor
  · intro h; apply div_pos _ hden; nlinarith
  · intro h; apply div_neg_of_neg_of_pos _ hden; nlinarith

end ChemotaxisBifurcation.RemarkFindings
