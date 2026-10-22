module
public import ChemotaxisBifurcation.ModeIntervals
public import ChemotaxisBifurcation.SmallDomain
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Domain-length limits

This module separates the elementary limit argument from the minimizer theorem.
The corridor assumptions are explicit inputs.  A later mode-classification
module supplies them for the paper's critical mode.
-/

namespace ChemotaxisBifurcation.DomainLimits

open Filter Topology
open ChemotaxisBifurcation
open ChemotaxisBifurcation.SmallDomain

noncomputable section

/-- The exact Neumann eigenvalue at a real domain length. -/
def modeEigenvalue (L : ℝ) (n : ℕ) : ℝ :=
  (((n : ℝ) * Real.pi) / L) ^ 2

/-- A positive modal lower bound forces the mode index to grow at least
linearly with the domain length. -/
theorem modeIndex_lower_bound
    {r L lambda : ℝ} {n : ℕ}
    (hr : 0 < r) (hL : 0 < L)
    (hlambda : lambda = modeEigenvalue L n)
    (hlower : r / 2 ≤ lambda) :
    Real.sqrt (r / 2) / Real.pi * L ≤ (n : ℝ) := by
  have hrhalf : 0 ≤ r / 2 := by positivity
  have hsqrt : 0 ≤ Real.sqrt (r / 2) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (r / 2)) ^ 2 = r / 2 :=
    Real.sq_sqrt hrhalf
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  have hscaled : r / 2 * L ^ 2 ≤ ((n : ℝ) * Real.pi) ^ 2 := by
    rw [hlambda, modeEigenvalue, div_pow] at hlower
    exact (le_div_iff₀ hLsq).mp (by simpa [mul_comm] using hlower)
  have hsqrt_le : Real.sqrt (r / 2) * L ≤ (n : ℝ) * Real.pi := by
    apply (sq_le_sq₀ (mul_nonneg hsqrt hL.le) (mul_nonneg hn hpi.le)).mp
    rw [mul_pow, hsqrt_sq]
    exact hscaled
  rw [show Real.sqrt (r / 2) / Real.pi * L =
    (Real.sqrt (r / 2) * L) / Real.pi by ring]
  exact (div_le_iff₀ hpi).2 hsqrt_le

/-- From the exact eigenvalue formula and a fixed positive lower bound, a
domain length tending to infinity forces the critical mode to infinity. -/
theorem modeIndex_tendsto_atTop
    {ι : Type*} {l : Filter ι}
    {L lambda : ι → ℝ} {n : ι → ℕ} {r : ℝ}
    (hr : 0 < r)
    (hL : Tendsto L l atTop)
    (hformula : ∀ᶠ k in l, lambda k = modeEigenvalue (L k) (n k))
    (hlower : ∀ᶠ k in l, r / 2 ≤ lambda k) :
    Tendsto (fun k => (n k : ℝ)) l atTop := by
  have hc : 0 < Real.sqrt (r / 2) / Real.pi := by positivity
  have hcL : Tendsto (fun k => Real.sqrt (r / 2) / Real.pi * L k)
      l atTop := hL.const_mul_atTop hc
  apply tendsto_atTop_mono' l ?_ hcL
  filter_upwards [hformula, hlower, hL.eventually_gt_atTop 0] with k hformulaK hlowerK hLpos
  exact modeIndex_lower_bound hr hLpos hformulaK hlowerK

/-- The lower mode corridor tends to the balancing eigenvalue. -/
theorem lowerCorridor_tendsto
    {ι : Type*} {l : Filter ι} {N : ι → ℝ} {r : ℝ} (hr : 0 < r)
    (hN : Tendsto N l atTop) :
    Tendsto (fun k => r * N k / (N k + 1)) l (𝓝 r) := by
  have hNp : Tendsto (fun k => N k + 1) l atTop :=
    tendsto_atTop_add_const_right l 1 hN
  have hinv : Tendsto (fun k => (N k + 1)⁻¹) l (𝓝 0) :=
    hNp.inv_tendsto_atTop
  have hmodel : Tendsto (fun k => r * (1 - (N k + 1)⁻¹)) l (𝓝 r) := by
    have hrconst : Tendsto (fun _ : ι => r) l (𝓝 r) := tendsto_const_nhds
    have hone : Tendsto (fun _ : ι => (1 : ℝ)) l (𝓝 1) := tendsto_const_nhds
    simpa using hrconst.mul (hone.sub hinv)
  apply hmodel.congr'
  filter_upwards [hNp.eventually_gt_atTop 0] with k hk
  field_simp [ne_of_gt hk]
  ring

/-- The upper mode corridor tends to the balancing eigenvalue. -/
theorem upperCorridor_tendsto
    {ι : Type*} {l : Filter ι} {N : ι → ℝ} {r : ℝ} (hr : 0 < r)
    (hN : Tendsto N l atTop) :
    Tendsto (fun k => r * N k / (N k - 1)) l (𝓝 r) := by
  have hNm : Tendsto (fun k => N k - 1) l atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right l (-1 : ℝ) hN
  have hinv : Tendsto (fun k => (N k - 1)⁻¹) l (𝓝 0) :=
    hNm.inv_tendsto_atTop
  have hmodel : Tendsto (fun k => r * (1 + (N k - 1)⁻¹)) l (𝓝 r) := by
    have hrconst : Tendsto (fun _ : ι => r) l (𝓝 r) := tendsto_const_nhds
    have hone : Tendsto (fun _ : ι => (1 : ℝ)) l (𝓝 1) := tendsto_const_nhds
    simpa using hrconst.mul (hone.add hinv)
  apply hmodel.congr'
  filter_upwards [hNm.eventually_gt_atTop 0] with k hk
  field_simp [ne_of_gt hk]
  ring

/-- A function trapped between the two adjacent-mode corridors converges to
the balancing eigenvalue once the mode index tends to infinity. -/
theorem eigenvalue_tendsto_of_corridor
    {ι : Type*} {l : Filter ι} {lambda N : ι → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hN : Tendsto N l atTop)
    (hlower : ∀ᶠ k in l, r * N k / (N k + 1) ≤ lambda k)
    (hupper : ∀ᶠ k in l, lambda k ≤ r * N k / (N k - 1)) :
    Tendsto lambda l (𝓝 r) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (lowerCorridor_tendsto hr hN) (upperCorridor_tendsto hr hN)
    hlower hupper

/-- Large-domain convergence from the exact modal formula and explicit
corridor assumptions. -/
theorem eigenvalue_tendsto_of_domain_corridor
    {ι : Type*} {l : Filter ι}
    {L lambda : ι → ℝ} {n : ι → ℕ} {r : ℝ}
    (hr : 0 < r)
    (hL : Tendsto L l atTop)
    (hformula : ∀ᶠ k in l, lambda k = modeEigenvalue (L k) (n k))
    (hfixedLower : ∀ᶠ k in l, r / 2 ≤ lambda k)
    (hlower : ∀ᶠ k in l,
      r * (n k : ℝ) / ((n k : ℝ) + 1) ≤ lambda k)
    (hupper : ∀ᶠ k in l,
      lambda k ≤ r * (n k : ℝ) / ((n k : ℝ) - 1)) :
    Tendsto lambda l (𝓝 r) := by
  have hn := modeIndex_tendsto_atTop hr hL hformula hfixedLower
  exact eigenvalue_tendsto_of_corridor hr hn hlower hupper

/-- The critical eigenvalue converges to the balancing value along any
large-domain path of strict minimizing modes.  The corridor assumptions are
discharged by `ModeIntervals`. -/
theorem physical_critical_eigenvalue_tendsto_balancing
    (p : PhysicalParams) (beta r : ℝ)
    {ι : Type*} {l : Filter ι} {d : ι → ModeData}
    (hp : PhysicalModeGuards.PositiveModeParameters p)
    (hstrict : ∀ᶠ i in l,
      PhysicalModeGuards.StrictCriticalMode p (d i) beta)
    (hL : Tendsto (fun i => (d i).L) l atTop)
    (hr : 0 < r) (hrsq : r ^ 2 = p.logisticSlope * p.mu) :
    Tendsto (fun i => (d i).eigenvalue) l (𝓝 r) := by
  have hformula : ∀ᶠ i in l,
      (d i).eigenvalue = modeEigenvalue (d i).L (d i).n0 :=
    Eventually.of_forall fun _ => rfl
  have hfixed : ∀ᶠ i in l, r / 2 ≤ (d i).eigenvalue :=
    hstrict.mono fun i hi =>
      (ModeIntervals.physical_critical_fixed_lower p (d i) beta r
        hp hi hr hrsq).le
  have hlower : ∀ᶠ i in l,
      r * ((d i).n0 : ℝ) / (((d i).n0 : ℝ) + 1) ≤ (d i).eigenvalue :=
    hstrict.mono fun i hi =>
      (ModeIntervals.physical_critical_lower_corridor p (d i) beta r
        hp hi hr hrsq).le
  have hn := modeIndex_tendsto_atTop hr hL hformula hfixed
  have hnTwo : ∀ᶠ i in l, 1 < (d i).n0 := by
    filter_upwards [hn.eventually_gt_atTop 1] with i hi
    exact_mod_cast hi
  have hupper : ∀ᶠ i in l,
      (d i).eigenvalue ≤
        r * ((d i).n0 : ℝ) / (((d i).n0 : ℝ) - 1) := by
    filter_upwards [hstrict, hnTwo] with i hi hn2
    exact (ModeIntervals.physical_critical_upper_corridor p (d i) beta r
      hp hi hn2 hr hrsq).le
  exact eigenvalue_tendsto_of_domain_corridor hr hL hformula hfixed hlower hupper

/-- The first-mode lower comparison diverges as the domain shrinks to zero. -/
theorem firstMode_tendsto_atTop_small_domain :
    Tendsto (fun L : ℝ => (Real.pi / L) ^ 2) (𝓝[>] 0) atTop := by
  have hinv : Tendsto (fun L : ℝ => L⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero
  have hpi : Tendsto (fun L : ℝ => Real.pi * L⁻¹) (𝓝[>] 0) atTop :=
    hinv.const_mul_atTop Real.pi_pos
  change Tendsto (fun L : ℝ => (Real.pi * L⁻¹) ^ 2) (𝓝[>] 0) atTop
  exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hpi

/-- Any nonconstant Neumann mode diverges at least as fast as the first mode
when the domain shrinks to zero. -/
theorem modeEigenvalue_tendsto_atTop_small_domain
    {n : ℝ → ℕ} (hn : ∀ᶠ L in 𝓝[>] (0 : ℝ), 1 ≤ n L) :
    Tendsto (fun L => modeEigenvalue L (n L)) (𝓝[>] 0) atTop := by
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) ?_ firstMode_tendsto_atTop_small_domain
  filter_upwards [hn, self_mem_nhdsWithin] with L hnL hL
  have hLpos : 0 < L := hL
  have hnreal : (1 : ℝ) ≤ (n L : ℝ) := by exact_mod_cast hnL
  unfold modeEigenvalue
  have hbase : 0 ≤ Real.pi / L := by positivity
  have hmode : Real.pi / L ≤ (n L : ℝ) * Real.pi / L := by
    exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hLpos.le
  nlinarith [sq_nonneg ((n L : ℝ) * Real.pi / L - Real.pi / L)]

/-- Along a positive domain-length path of strict critical modes, the actual
critical eigenvalue diverges as the length shrinks to zero. -/
theorem physical_critical_eigenvalue_tendsto_atTop_small_domain
    (p : PhysicalParams) (beta : ℝ) {d : ℝ → ModeData}
    (hLength : ∀ᶠ L in 𝓝[>] (0 : ℝ), (d L).L = L)
    (hstrict : ∀ᶠ L in 𝓝[>] (0 : ℝ),
      PhysicalModeGuards.StrictCriticalMode p (d L) beta) :
    Tendsto (fun L => (d L).eigenvalue) (𝓝[>] 0) atTop := by
  have hn : ∀ᶠ L in 𝓝[>] (0 : ℝ), 1 ≤ (d L).n0 :=
    hstrict.mono fun _ hs => hs.2.1
  have hmode := modeEigenvalue_tendsto_atTop_small_domain hn
  apply hmode.congr'
  filter_upwards [hLength] with L hL
  calc
    modeEigenvalue L (d L).n0 = modeEigenvalue (d L).L (d L).n0 :=
      congrArg (fun z => modeEigenvalue z (d L).n0) hL.symm
    _ = (d L).eigenvalue := rfl

/-- Composition of the checked physical coefficient limit with any eigenvalue
path tending to infinity. -/
theorem logisticCoefficient_sub_linear_tendsto_dBeta_of_eigenvalue
    (p : PhysicalParams) (beta : ℝ)
    {ι : Type*} {l : Filter ι} {lambda : ι → ℝ}
    (hu : p.uStar ≠ 0) (hw : p.signalOffset ≠ 0)
    (hmu : p.mu ≠ 0) (hd : p.logisticSlope ≠ 0)
    (hK : (RationalCoefficient.physicalRationalData p beta).K ≠ 0)
    (hlambda : Tendsto lambda l atTop) :
    Tendsto
      (fun k => logisticBetaCoefficient p (lambda k) beta -
        cSD p beta * lambda k)
      l (𝓝 (dBeta p beta)) :=
  (logisticBetaCoefficient_sub_linear_tendsto_dBeta
    p beta hu hw hmu hd hK).comp hlambda

end

end ChemotaxisBifurcation.DomainLimits
