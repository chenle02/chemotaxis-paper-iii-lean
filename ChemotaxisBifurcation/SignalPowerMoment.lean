module
public import ChemotaxisBifurcation.SignalCompactness

/-!
# Arbitrary-r actual signal bounds and C1 extraction

The compactness step in Lemma 5.1 uses any finite r>max(1,gamma). A normalized
power-moment scale lets the earlier actual signal W2q proof apply verbatim,
without a logistic reaction-law hypothesis. This module then derives an
actual C1 subsequence for that complete exponent range.
-/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
namespace ChemotaxisBifurcation.SignalPowerMoment
noncomputable section

/-- Normalize an arbitrary uniform population power moment on [0,L]. This is
only a convenient scalar, not an assumed equilibrium or logistic parameter. -/
def momentScale (L R r : ℝ) : ℝ := (R / L) ^ (1 / r)

/-- The actual signal W2q bound for every finite population exponent
r>max(1,gamma), q=r/gamma. No logistic reaction law is needed. The existing
actual-norm proof depends only on its normalized moment input, so alpha=r-1
is used as a bound-exponent parameter, not the population reaction exponent. -/
theorem W2q_bound_of_power_moment (L mu nu gamma r R : ℝ) (u v dv ddv : ℝ → ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma)
    (hr : 1 < r) (hgamma_r : gamma < r) (hR : 0 ≤ R)
    (hu : ContinuousOn u (Icc 0 L)) (hu0 : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hv : ContinuousOn v (Icc 0 L)) (hvpos : ∀ x ∈ Icc 0 L, 0 < v x)
    (hdv : ContinuousOn dv (Icc 0 L)) (hddv : ContinuousOn ddv (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x)
    (hderiv2 : ∀ x ∈ Ioo 0 L, HasDerivAt dv (ddv x) x)
    (heq : ∀ x ∈ Ioo 0 L, ddv x - mu * v x + nu * u x ^ gamma = 0)
    (hbc0 : dv 0 = 0) (hbcL : dv L = 0)
    (hmoment : ∫ x in (0 : ℝ)..L, u x ^ r ≤ R) :
    (∫ x in (0 : ℝ)..L, |v x| ^ (r / gamma)) ^ (1 / (r / gamma)) +
      (∫ x in (0 : ℝ)..L, |dv x| ^ (r / gamma)) ^ (1 / (r / gamma)) +
      (∫ x in (0 : ℝ)..L, |ddv x| ^ (r / gamma)) ^ (1 / (r / gamma)) ≤
      L ^ (1 / (r / gamma)) * momentScale L R r ^ gamma *
        (nu / mu + 2 * nu + 2 * nu * L) := by
  have hr0 : 0 < r := by linarith
  have hscale0 : 0 ≤ momentScale L R r := Real.rpow_nonneg (div_nonneg hR hL.le) _
  have hscale : momentScale L R r ^ r = R / L := by
    dsimp [momentScale]
    rw [one_div, Real.rpow_inv_rpow (div_nonneg hR hL.le) hr0.ne']
  have hq : 1 < r / gamma := (lt_div_iff₀ hgamma).mpr (by simpa using hgamma_r)
  have hexp : gamma * (r / gamma) = 1 + (r - 1) := by field_simp; ring
  have hm : ∫ x in (0 : ℝ)..L, u x ^ (1 + (r - 1)) ≤
      L * momentScale L R r ^ (1 + (r - 1)) := by
    rw [show 1 + (r - 1) = r by ring, hscale]
    have hLR : L * (R / L) = R := by field_simp
    rwa [hLR]
  exact SpikeEstimates.logistic_W2q_actual L mu nu gamma (r - 1) (momentScale L R r)
    (r / gamma) u v dv ddv hL hmu hnu (by linarith) hgamma hscale0 hq hexp
    hu hu0 hv hvpos hdv hddv hderiv hderiv2 heq hbc0 hbcL hm

/-- Full arbitrary-r classical signal C1 subsequence extraction from actual
stationary signal equations and a uniform population Lr moment bound. -/
theorem exists_C1_subsequence_of_power_moment (L mu nu gamma r R : ℝ)
    (u v dv ddv : ℕ → ℝ → ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma)
    (hr : 1 < r) (hgamma_r : gamma < r) (hR : 0 ≤ R)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hu0 : ∀ n x, x ∈ Icc 0 L → 0 ≤ u n x)
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hvpos : ∀ n x, x ∈ Icc 0 L → 0 < v n x)
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hddv : ∀ n, ContinuousOn (ddv n) (Icc 0 L))
    (hderiv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x)
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (heq : ∀ n x, x ∈ Ioo 0 L → ddv n x - mu * v n x + nu * u n x ^ gamma = 0)
    (hbc0 : ∀ n, dv n 0 = 0) (hbcL : ∀ n, dv n L = 0)
    (hmoment : ∀ n, ∫ x in (0 : ℝ)..L, u n x ^ r ≤ R) :
    ∃ V DV : ℝ → ℝ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ContinuousOn V (Icc 0 L) ∧ ContinuousOn DV (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => v (phi n)) V atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => dv (phi n)) DV atTop (Icc 0 L) ∧
      DV 0 = 0 ∧ DV L = 0 ∧ (∀ x ∈ Icc 0 L, 0 ≤ V x) ∧
      ∀ x ∈ Ioo 0 L, HasDerivAt V (DV x) x := by
  let B := L ^ (1 / (r / gamma)) * momentScale L R r ^ gamma *
    (nu / mu + 2 * nu + 2 * nu * L)
  have hB : 0 ≤ B := by
    dsimp [B, momentScale]
    positivity
  have hq : 1 < r / gamma := (lt_div_iff₀ hgamma).mpr (by simpa using hgamma_r)
  have hb : ∀ n,
      (∫ x in (0 : ℝ)..L, |v n x| ^ (r / gamma)) ^ (1 / (r / gamma)) +
      (∫ x in (0 : ℝ)..L, |dv n x| ^ (r / gamma)) ^ (1 / (r / gamma)) +
      (∫ x in (0 : ℝ)..L, |ddv n x| ^ (r / gamma)) ^ (1 / (r / gamma)) ≤ B := by
    intro n
    exact W2q_bound_of_power_moment L mu nu gamma r R (u n) (v n) (dv n) (ddv n)
      hL hmu hnu hgamma hr hgamma_r hR (hu n) (hu0 n) (hv n) (hvpos n) (hdv n)
      (hddv n) (hderiv n) (hderiv2 n) (heq n) (hbc0 n) (hbcL n) (hmoment n)
  obtain ⟨V, DV, phi, hphi, hV, hDV, hvlim, hdvlim, hderivlim⟩ :=
    SignalCompactness.exists_C1_subsequence_of_W2q_bound L (r / gamma) B v dv ddv
      hL hq hB hv hdv hddv hderiv hderiv2 hb
  refine ⟨V, DV, phi, hphi, hV, hDV, hvlim, hdvlim, ?_, ?_, ?_, hderivlim⟩
  · have h := hdvlim.tendsto_at ⟨le_rfl, hL.le⟩
    simp only [hbc0] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · have h := hdvlim.tendsto_at ⟨hL.le, le_rfl⟩
    simp only [hbcL] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · intro x hx
    exact ge_of_tendsto (hvlim.tendsto_at hx) (Eventually.of_forall fun n => (hvpos (phi n) x hx).le)
end
end ChemotaxisBifurcation.SignalPowerMoment
