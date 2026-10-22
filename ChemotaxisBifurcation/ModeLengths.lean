module
public import ChemotaxisBifurcation.ModeIntervals

@[expose] public section

/-!
# Literal domain-length intervals and beta-independent mode selection

The boundary length is pi*sqrt(k*(k+1))/sqrt(r), where r=sqrt(a*alpha*mu).
Its fourth-root form is identified explicitly. Strict intervals exclude ties.
-/

namespace ChemotaxisBifurcation.ModeIntervals

open PhysicalModeGuards Thresholds Filter
open scoped Topology

noncomputable section

def criticalLength (r : ℝ) (k : ℕ) : ℝ :=
  Real.pi * Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) / Real.sqrt r

theorem criticalLength_zero (r : ℝ) : criticalLength r 0 = 0 := by
  simp [criticalLength]

theorem criticalLength_nonneg (r : ℝ) (k : ℕ) : 0 ≤ criticalLength r k := by
  unfold criticalLength
  positivity

theorem criticalLength_pos (r : ℝ) (k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    0 < criticalLength r k := by
  unfold criticalLength
  positivity

theorem criticalLength_sq (r : ℝ) (k : ℕ) (hr : 0 < r) :
    criticalLength r k ^ 2 = Real.pi ^ 2 * (k : ℝ) * ((k : ℝ) + 1) / r := by
  unfold criticalLength
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hr.le]
  ring

theorem criticalLength_pred_sq (r : ℝ) (n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    criticalLength r (n - 1) ^ 2 = Real.pi ^ 2 * (n : ℝ) * ((n : ℝ) - 1) / r := by
  rw [criticalLength_sq r (n - 1) hr, Nat.cast_sub hn, Nat.cast_one]
  ring

theorem criticalLength_fourth_root (z : ℝ) (k : ℕ) (hz : 0 ≤ z) :
    criticalLength (Real.sqrt z) k =
      Real.pi * Real.sqrt ((k : ℝ) * ((k : ℝ) + 1)) / z ^ (1 / 4 : ℝ) := by
  have hroot : Real.sqrt (Real.sqrt z) = z ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hz]
    norm_num
  unfold criticalLength
  rw [hroot]

theorem modeCell_iff_length_interval (r L : ℝ) (n : ℕ)
    (hr : 0 < r) (hL : 0 < L) (hn : 0 < n) :
    modeCell ((Real.pi / L) ^ 2) r n ↔
      criticalLength r (n - 1) < L ∧ L < criticalLength r n := by
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  have hlower :
      (Real.pi / L) ^ 2 * (n : ℝ) * ((n : ℝ) - 1) < r ↔
        criticalLength r (n - 1) ^ 2 < L ^ 2 := by
    rw [criticalLength_pred_sq r n hr hn]
    rw [show (Real.pi / L) ^ 2 * (n : ℝ) * ((n : ℝ) - 1) =
        (Real.pi ^ 2 * (n : ℝ) * ((n : ℝ) - 1)) / L ^ 2 by ring]
    rw [div_lt_iff₀ hLsq, div_lt_iff₀ hr]
    constructor <;> intro h <;> nlinarith
  have hupper :
      r < (Real.pi / L) ^ 2 * (n : ℝ) * ((n : ℝ) + 1) ↔
        L ^ 2 < criticalLength r n ^ 2 := by
    rw [criticalLength_sq r n hr]
    rw [show (Real.pi / L) ^ 2 * (n : ℝ) * ((n : ℝ) + 1) =
        (Real.pi ^ 2 * (n : ℝ) * ((n : ℝ) + 1)) / L ^ 2 by ring]
    rw [lt_div_iff₀ hLsq, lt_div_iff₀ hr]
    constructor <;> intro h <;> nlinarith
  unfold modeCell
  rw [hlower, hupper]
  exact and_congr
    (sq_lt_sq₀ (criticalLength_nonneg r (n - 1)) hL.le)
    (sq_lt_sq₀ hL.le (criticalLength_nonneg r n))

theorem physical_strictMode_iff (p : PhysicalParams) (d : ModeData) (beta : ℝ)
    (hp : PositiveModeParameters p) (hL : 0 < d.L) :
    StrictCriticalMode p d beta ↔
      StrictMode p.logisticSlope p.mu ((Real.pi / d.L) ^ 2) d.n0 := by
  constructor
  · exact physical_strictMode p d beta hp
  · intro hs
    refine ⟨hL, hs.1, ?_⟩
    intro m hm hmn
    apply (chiStar_lt_iff_modeFactor_lt p d.eigenvalue
      (Semidiscrete.continuumLam d.L m) beta hp).mpr
    rw [data_eigenvalue_eq_modeAt d, continuumLam_eq_modeAt d.L m]
    exact hs.2 m hm hmn

theorem physical_critical_length_iff (p : PhysicalParams) (d : ModeData) (beta r : ℝ)
    (hp : PositiveModeParameters p) (hL : 0 < d.L) (hn : 0 < d.n0)
    (hr : 0 < r) (hrsq : r ^ 2 = p.logisticSlope * p.mu) :
    StrictCriticalMode p d beta ↔
      criticalLength r (d.n0 - 1) < d.L ∧ d.L < criticalLength r d.n0 := by
  have hc : 0 < (Real.pi / d.L) ^ 2 := by positivity
  rw [physical_strictMode_iff p d beta hp hL,
    strictMode_iff_cell p.logisticSlope p.mu _ r d.n0 hc hr hrsq hn,
    modeCell_iff_length_interval r d.L d.n0 hr hL hn]

/-- The full strict critical-mode predicate is independent of beta. -/
theorem strictCriticalMode_beta_iff (p : PhysicalParams) (d : ModeData) (beta1 beta2 : ℝ)
    (hp : PositiveModeParameters p) :
    StrictCriticalMode p d beta1 ↔ StrictCriticalMode p d beta2 := by
  constructor
  · intro h
    exact (physical_strictMode_iff p d beta2 hp h.1).mpr
      (physical_strictMode p d beta1 hp h)
  · intro h
    exact (physical_strictMode_iff p d beta1 hp h.1).mpr
      (physical_strictMode p d beta2 hp h)

/-- In the minimal model, the first positive mode is the only strict minimum. -/
theorem strictMode_minimal_iff (mu c : ℝ) (n : ℕ) (hc : 0 < c) (hn : 0 < n) :
    StrictMode 0 mu c n ↔ n = 1 := by
  constructor
  · intro hs
    by_contra hne
    have hn1 : 1 < n := by omega
    have h := hs.2 1 (by omega) (Ne.symm hne)
    rw [modeFactor_zero_eq mu _ (modeAt_pos hc hn).ne',
      modeFactor_zero_eq mu _ (modeAt_pos hc Nat.one_pos).ne'] at h
    have hlt := modeAt_strictMono hc hn1
    linarith
  · intro hn1
    subst n
    refine ⟨Nat.one_pos, ?_⟩
    intro m hm hne
    have h1m : 1 < m := by omega
    rw [modeFactor_zero_eq mu _ (modeAt_pos hc Nat.one_pos).ne',
      modeFactor_zero_eq mu _ (modeAt_pos hc hm).ne']
    have hlt := modeAt_strictMono hc h1m
    linarith

theorem fixedMass_strictCriticalMode_iff (p : PhysicalParams) (d : ModeData) (beta : ℝ)
    (hp : p.FixedMassAdmissible) (hL : 0 < d.L) (hn : 0 < d.n0) :
    StrictCriticalMode p d beta ↔ d.n0 = 1 := by
  have hq : p.logisticSlope = 0 := by simp [PhysicalParams.logisticSlope, hp.1]
  have hc : 0 < (Real.pi / d.L) ^ 2 := by positivity
  rw [physical_strictMode_iff p d beta (fixedMass_positive_parameters p hp) hL,
    hq, strictMode_minimal_iff p.mu _ d.n0 hc hn]

/-- Below the first boundary length the actual strict critical mode is one. -/
theorem first_mode_of_below_first_length (p : PhysicalParams) (d : ModeData) (beta r : ℝ)
    (hp : PositiveModeParameters p) (hs : StrictCriticalMode p d beta)
    (hr : 0 < r) (hrsq : r ^ 2 = p.logisticSlope * p.mu)
    (hbelow : d.L < criticalLength r 1) : d.n0 = 1 := by
  let first : ModeData := ⟨d.L, 1⟩
  have hf : StrictCriticalMode p first beta := by
    apply (physical_critical_length_iff p first beta r hp hs.1 Nat.one_pos hr hrsq).mpr
    constructor
    · simpa [first, criticalLength_zero] using hs.1
    · exact hbelow
  by_contra hne
  have h1 := hs.2.2 1 Nat.one_pos (Ne.symm hne)
  have h2 := hf.2.2 d.n0 hs.2.1 hne
  change p.chiStar d.eigenvalue beta < p.chiStar first.eigenvalue beta at h1
  change p.chiStar first.eigenvalue beta < p.chiStar d.eigenvalue beta at h2
  linarith

/-- The first-mode conclusion is eventual along every small-domain path. -/
theorem eventually_first_critical_mode {ι : Type*} {l : Filter ι}
    (p : PhysicalParams) (d : ι → ModeData) (beta r : ℝ)
    (hp : PositiveModeParameters p) (hr : 0 < r)
    (hrsq : r ^ 2 = p.logisticSlope * p.mu)
    (hL : Tendsto (fun i => (d i).L) l (𝓝[>] (0 : ℝ)))
    (hs : ∀ᶠ i in l, StrictCriticalMode p (d i) beta) :
    ∀ᶠ i in l, (d i).n0 = 1 := by
  have hL' : Tendsto (fun i => (d i).L) l (𝓝 (0 : ℝ)) :=
    hL.mono_right nhdsWithin_le_nhds
  have hbelow : ∀ᶠ i in l, (d i).L < criticalLength r 1 :=
    hL'.eventually (gt_mem_nhds (criticalLength_pos r 1 hr Nat.one_pos))
  filter_upwards [hs, hbelow] with i hi hb
  exact first_mode_of_below_first_length p (d i) beta r hp hi hr hrsq hb

end

end ChemotaxisBifurcation.ModeIntervals
