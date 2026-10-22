module
public import ChemotaxisBifurcation.PhysicalModeGuards

@[expose] public section

/-!
# Exact strict-minimizer cells and critical-eigenvalue corridors

For c=(pi/L)^2 and r^2=q*mu, mode n is the strict minimum precisely when
c*n*(n-1) < r < c*n*(n+1). Endpoints are ties and are not classified here.
The corridor statements are the inputs consumed by DomainLimits.
-/

namespace ChemotaxisBifurcation.ModeIntervals

open Thresholds PhysicalModeGuards

noncomputable section

def modeAt (c : ℝ) (n : ℕ) : ℝ := c * (n : ℝ) ^ 2

def StrictMode (q mu c : ℝ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m ≠ n →
    modeFactor q mu (modeAt c n) < modeFactor q mu (modeAt c m)

def modeCell (c r : ℝ) (n : ℕ) : Prop :=
  c * (n : ℝ) * ((n : ℝ) - 1) < r ∧
    r < c * (n : ℝ) * ((n : ℝ) + 1)

/-- Reused exact difference identity from the legacy modal-ordering module. -/
theorem modeFactor_sub (q mu x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    modeFactor q mu y - modeFactor q mu x =
      (y - x) * (x * y - q * mu) / (x * y) := by
  unfold modeFactor
  field_simp [hx, hy] <;> ring

theorem modeFactor_lt_iff_product (q mu x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    modeFactor q mu x < modeFactor q mu y ↔ q * mu < x * y := by
  have hy := hx.trans hxy
  have hd := mul_pos hx hy
  have hg := sub_pos.mpr hxy
  constructor
  · intro h
    have hh := sub_pos.mpr h
    rw [modeFactor_sub q mu x y hx.ne' hy.ne'] at hh
    have hn : 0 < (y - x) * (x * y - q * mu) := by
      simpa using (lt_div_iff₀ hd).mp hh
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hg).mp hn)
  · intro h
    apply sub_pos.mp
    rw [modeFactor_sub q mu x y hx.ne' hy.ne']
    exact div_pos (mul_pos hg (sub_pos.mpr h)) hd

theorem modeFactor_reverse_lt_iff_product (q mu x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    modeFactor q mu y < modeFactor q mu x ↔ x * y < q * mu := by
  have hy := hx.trans hxy
  have hd := mul_pos hx hy
  have hg := sub_pos.mpr hxy
  constructor
  · intro h
    have hh := sub_neg.mpr h
    rw [modeFactor_sub q mu x y hx.ne' hy.ne'] at hh
    have hn : (y - x) * (x * y - q * mu) < 0 := by
      simpa using (div_lt_iff₀ hd).mp hh
    have hf : x * y - q * mu < 0 := by
      by_contra hnot
      have hp := mul_nonneg hg.le (le_of_not_gt hnot)
      linarith
    exact sub_neg.mp hf
  · intro h
    apply sub_neg.mp
    rw [modeFactor_sub q mu x y hx.ne' hy.ne']
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hg (sub_neg.mpr h)) hd

theorem modeAt_pos {c : ℝ} {n : ℕ} (hc : 0 < c) (hn : 0 < n) : 0 < modeAt c n := by
  unfold modeAt
  positivity

theorem modeAt_strictMono {c : ℝ} (hc : 0 < c) : StrictMono (modeAt c) := by
  intro m n hmn
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  exact mul_lt_mul_of_pos_left ((sq_lt_sq₀ hm0 hn0).mpr hmnR) hc

theorem mode_product (c : ℝ) (m n : ℕ) :
    modeAt c m * modeAt c n = (c * (m : ℝ) * (n : ℝ)) ^ 2 := by
  unfold modeAt
  ring

theorem strictMode_iff_cell (q mu c r : ℝ) (n : ℕ)
    (hc : 0 < c) (hr : 0 < r) (hrsq : r ^ 2 = q * mu) (hn : 0 < n) :
    StrictMode q mu c n ↔ modeCell c r n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro hs
    constructor
    · by_cases hn1 : n = 1
      · simpa [hn1] using hr
      · have hn2 : 1 < n := by omega
        have hpred : 0 < n - 1 := by omega
        have hcomp := hs.2 (n - 1) hpred (by omega)
        have hp := (modeFactor_reverse_lt_iff_product q mu
          (modeAt c (n - 1)) (modeAt c n) (modeAt_pos hc hpred)
          (modeAt_strictMono hc (by omega))).mp hcomp
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub hn, Nat.cast_one]
        rw [mode_product, hcast, ← hrsq] at hp
        have hn2R : (1 : ℝ) < n := by exact_mod_cast hn2
        have he := (sq_lt_sq₀ (by positivity : 0 ≤ c * ((n : ℝ) - 1) * (n : ℝ)) hr.le).mp hp
        simpa [mul_comm, mul_left_comm, mul_assoc] using he
    · have hcomp := hs.2 (n + 1) (by omega) (by omega)
      have hp := (modeFactor_lt_iff_product q mu (modeAt c n) (modeAt c (n + 1))
        (modeAt_pos hc hn) (modeAt_strictMono hc (by omega))).mp hcomp
      rw [mode_product, Nat.cast_add, Nat.cast_one, ← hrsq] at hp
      exact (sq_lt_sq₀ hr.le (by positivity)).mp hp
  · intro hcell
    refine ⟨hn, ?_⟩
    intro m hm hmn
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have hm1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hlt
      have hmr : (m : ℝ) ≤ (n : ℝ) - 1 := by linarith
      have hbound : c * (m : ℝ) * (n : ℝ) < r := by
        calc
          c * (m : ℝ) * (n : ℝ) = (c * (n : ℝ)) * (m : ℝ) := by ring
          _ ≤ (c * (n : ℝ)) * ((n : ℝ) - 1) :=
            mul_le_mul_of_nonneg_left hmr (mul_pos hc hnR).le
          _ < r := hcell.1
      apply (modeFactor_reverse_lt_iff_product q mu (modeAt c m) (modeAt c n)
        (modeAt_pos hc hm) (modeAt_strictMono hc hlt)).mpr
      rw [mode_product, ← hrsq]
      exact (sq_lt_sq₀ (by positivity) hr.le).mpr hbound
    · have hn1 : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hgt
      have hbound : r < c * (n : ℝ) * (m : ℝ) := by
        exact hcell.2.trans_le (mul_le_mul_of_nonneg_left hn1 (mul_pos hc hnR).le)
      apply (modeFactor_lt_iff_product q mu (modeAt c n) (modeAt c m)
        (modeAt_pos hc hn) (modeAt_strictMono hc hgt)).mpr
      rw [mode_product, ← hrsq]
      exact (sq_lt_sq₀ hr.le (by positivity)).mpr hbound

theorem cell_lower_corridor (c r : ℝ) (n : ℕ) (hn : 0 < n) (hcell : modeCell c r n) :
    r * (n : ℝ) / ((n : ℝ) + 1) < modeAt c n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  calc
    r * (n : ℝ) < (c * (n : ℝ) * ((n : ℝ) + 1)) * (n : ℝ) :=
      mul_lt_mul_of_pos_right hcell.2 hnR
    _ = modeAt c n * ((n : ℝ) + 1) := by unfold modeAt; ring

theorem cell_upper_corridor (c r : ℝ) (n : ℕ) (hn : 1 < n) (hcell : modeCell c r n) :
    modeAt c n < r * (n : ℝ) / ((n : ℝ) - 1) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  apply (lt_div_iff₀ (sub_pos.mpr hnR)).mpr
  calc
    modeAt c n * ((n : ℝ) - 1) = (c * (n : ℝ) * ((n : ℝ) - 1)) * (n : ℝ) := by
      unfold modeAt; ring
    _ < r * (n : ℝ) := mul_lt_mul_of_pos_right hcell.1 (by linarith)

theorem cell_fixed_lower (c r : ℝ) (n : ℕ) (hr : 0 < r) (hn : 0 < n)
    (hcell : modeCell c r n) : r / 2 < modeAt c n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : r / 2 ≤ r * (n : ℝ) / ((n : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hnR)]
  exact hl.trans_lt (cell_lower_corridor c r n hn hcell)

theorem continuumLam_eq_modeAt (L : ℝ) (n : ℕ) :
    Semidiscrete.continuumLam L n = modeAt ((Real.pi / L) ^ 2) n := by
  unfold Semidiscrete.continuumLam modeAt
  ring

theorem data_eigenvalue_eq_modeAt (d : ModeData) :
    d.eigenvalue = modeAt ((Real.pi / d.L) ^ 2) d.n0 :=
  continuumLam_eq_modeAt d.L d.n0

theorem chiStar_lt_iff_modeFactor_lt (p : PhysicalParams) (x y beta : ℝ)
    (hp : PositiveModeParameters p) :
    p.chiStar x beta < p.chiStar y beta ↔
      modeFactor p.logisticSlope p.mu x < modeFactor p.logisticSlope p.mu y := by
  rw [Semidiscrete.chiStar_eq_physical_modeThreshold p x beta hp.nu_pos hp.gamma_pos hp.u_pos hp.v_pos,
    Semidiscrete.chiStar_eq_physical_modeThreshold p y beta hp.nu_pos hp.gamma_pos hp.u_pos hp.v_pos]
  change Semidiscrete.physicalPrefactor p beta * modeFactor p.logisticSlope p.mu x <
      Semidiscrete.physicalPrefactor p beta * modeFactor p.logisticSlope p.mu y ↔ _
  exact mul_lt_mul_iff_right₀ (Semidiscrete.physicalPrefactor_pos p beta
    hp.nu_pos hp.gamma_pos hp.u_pos hp.v_pos)

theorem physical_strictMode (p : PhysicalParams) (d : ModeData) (beta : ℝ)
    (hp : PositiveModeParameters p) (hs : StrictCriticalMode p d beta) :
    StrictMode p.logisticSlope p.mu ((Real.pi / d.L) ^ 2) d.n0 := by
  refine ⟨hs.2.1, ?_⟩
  intro m hm hmn
  have h := (chiStar_lt_iff_modeFactor_lt p d.eigenvalue
    (Semidiscrete.continuumLam d.L m) beta hp).mp (hs.2.2 m hm hmn)
  rw [data_eigenvalue_eq_modeAt d, continuumLam_eq_modeAt d.L m] at h
  exact h

theorem physical_critical_mode_cell (p : PhysicalParams) (d : ModeData) (beta r : ℝ)
    (hp : PositiveModeParameters p) (hs : StrictCriticalMode p d beta)
    (hr : 0 < r) (hrsq : r ^ 2 = p.logisticSlope * p.mu) :
    modeCell ((Real.pi / d.L) ^ 2) r d.n0 := by
  have hc : 0 < (Real.pi / d.L) ^ 2 := by have hL := hs.1; positivity
  exact (strictMode_iff_cell p.logisticSlope p.mu _ r d.n0 hc hr hrsq hs.2.1).mp
    (physical_strictMode p d beta hp hs)

theorem physical_critical_lower_corridor (p : PhysicalParams) (d : ModeData) (beta r : ℝ)
    (hp : PositiveModeParameters p) (hs : StrictCriticalMode p d beta)
    (hr : 0 < r) (hrsq : r ^ 2 = p.logisticSlope * p.mu) :
    r * (d.n0 : ℝ) / ((d.n0 : ℝ) + 1) < d.eigenvalue := by
  rw [data_eigenvalue_eq_modeAt]
  exact cell_lower_corridor _ r d.n0 hs.2.1 (physical_critical_mode_cell p d beta r hp hs hr hrsq)

theorem physical_critical_upper_corridor (p : PhysicalParams) (d : ModeData) (beta r : ℝ)
    (hp : PositiveModeParameters p) (hs : StrictCriticalMode p d beta) (hn : 1 < d.n0)
    (hr : 0 < r) (hrsq : r ^ 2 = p.logisticSlope * p.mu) :
    d.eigenvalue < r * (d.n0 : ℝ) / ((d.n0 : ℝ) - 1) := by
  rw [data_eigenvalue_eq_modeAt]
  exact cell_upper_corridor _ r d.n0 hn (physical_critical_mode_cell p d beta r hp hs hr hrsq)

theorem physical_critical_fixed_lower (p : PhysicalParams) (d : ModeData) (beta r : ℝ)
    (hp : PositiveModeParameters p) (hs : StrictCriticalMode p d beta)
    (hr : 0 < r) (hrsq : r ^ 2 = p.logisticSlope * p.mu) : r / 2 < d.eigenvalue := by
  rw [data_eigenvalue_eq_modeAt]
  exact cell_fixed_lower _ r d.n0 hr hs.2.1 (physical_critical_mode_cell p d beta r hp hs hr hrsq)

end

end ChemotaxisBifurcation.ModeIntervals
