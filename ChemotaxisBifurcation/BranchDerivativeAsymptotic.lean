module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/
public import ChemotaxisBifurcation.BranchCurves

@[expose] public section

set_option autoImplicit false
namespace ChemotaxisBifurcation.BranchDerivativeAsymptotic
open Real Filter Topology Asymptotics
open ChemotaxisBifurcation.MixedRemainder ChemotaxisBifurcation.BranchCurves

/-- The equilibrium equation cancels the leading derivative error. -/
theorem equilibrium_derivative_error (alpha beta eta s R Rs ds C : ℝ)
    (hs : s ≠ 0)
    (hroot : alpha * eta * s - beta * s ^ 3 + R = 0)
    (hderiv : ds = alpha * eta - 3 * beta * s ^ 2 + Rs)
    (hR : |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4))
    (hRs : |Rs| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3)) :
    |ds + 2 * alpha * eta| ≤ 4 * C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := by
  have hdivroot : alpha * eta - beta * s ^ 2 + R / s = 0 := by
    calc _ = (alpha * eta * s - beta * s ^ 3 + R) / s := by field_simp [hs]
      _ = 0 := by rw [hroot]; simp
  have hdivR : |R / s| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := by
    rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hs)).mpr
    calc |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4) := hR
      _ = C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) * |s| := by
        rw [← (by decide : Even 4).pow_abs s, ← sq_abs s]; ring
  have hid : ds + 2 * alpha * eta = Rs - 3 * (R / s) := by linarith
  rw [hid]
  calc |Rs - 3 * (R / s)| ≤ |Rs| + |3 * (R / s)| := by
        simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le Rs (-(3 * (R / s))))
    _ = |Rs| + 3 * |R / s| := by rw [abs_mul]; norm_num
    _ ≤ 4 * C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3) := by linarith

/-- A square-amplitude bound turns the mixed error into an explicit little-o majorant. -/
theorem equilibrium_derivative_error_window (alpha beta eta s R Rs ds C D : ℝ)
    (hs : s ≠ 0) (hC : 0 ≤ C)
    (hroot : alpha * eta * s - beta * s ^ 3 + R = 0)
    (hderiv : ds = alpha * eta - 3 * beta * s ^ 2 + Rs)
    (hR : |R| ≤ C * (|s| * eta ^ 2 + |s| ^ 3 * |eta| + s ^ 4))
    (hRs : |Rs| ≤ C * (eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3))
    (hwindow : s ^ 2 ≤ D * |eta|) :
    |ds + 2 * alpha * eta| ≤ 4 * C * ((1 + D) * |eta| + D * |s|) * |eta| := by
  have h1 := mul_le_mul_of_nonneg_right hwindow (abs_nonneg eta)
  have h2 := mul_le_mul_of_nonneg_right hwindow (abs_nonneg s)
  have he : eta ^ 2 + s ^ 2 * |eta| + |s| ^ 3 ≤
      ((1 + D) * |eta| + D * |s|) * |eta| := by
    rw [← sq_abs s] at h2
    nlinarith [sq_abs eta]
  exact (equilibrium_derivative_error alpha beta eta s R Rs ds C hs hroot hderiv hR hRs).trans
    (by nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4 * C)])

noncomputable def errorFactor (alpha beta C eta : ℝ) : ℝ :=
  4 * C * ((1 + 2 * alpha / |beta|) * |eta| +
    (2 * alpha / |beta|) * (9 / 8 * Real.sqrt (alpha * eta / beta)))

theorem errorFactor_tendsto_zero (alpha beta C : ℝ) :
    Tendsto (errorFactor alpha beta C) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (errorFactor alpha beta C) := by unfold errorFactor; fun_prop
  have hz : errorFactor alpha beta C 0 = 0 := by simp [errorFactor]
  simpa [hz] using hc.continuousAt.tendsto (x := (0 : ℝ))

section Branch
variable (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))

include halpha hbeta hC hr hr1 hRval hRder hRs

/-- Actual BranchCurves branches have derivative -2αη with a vanishing relative error. -/
theorem branch_derivative_error_bound (eta : ℝ)
    (hsmall : CurveSmall alpha beta C r eta) (hside : 0 < eta * beta)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    |deriv (reducedField alpha beta R eta)
        (branch alpha beta (branchRadius alpha beta C r) R sgn eta) + 2 * alpha * eta| ≤
      errorFactor alpha beta C eta * |eta| := by
  let s := branch alpha beta (branchRadius alpha beta C r) R sgn eta
  obtain ⟨⟨hpos, hsrho, hroot⟩, -, -⟩ := branch_spec alpha beta C r eta R Rs
    halpha hbeta hC hr hr1 hRval hRder hRs hsmall hside sgn hsgn
  have hs : s ≠ 0 := by intro hz; change 0 < sgn * s at hpos; rw [hz, mul_zero] at hpos; linarith
  have hsr : |s| ≤ r := hsrho.trans (branchRadius_le alpha beta C r)
  have he : |eta| ≤ r := hsmall.1.le
  have hamp : |s| ≤ 9 / 8 * Real.sqrt (alpha * eta / beta) :=
    branch_abs_le alpha beta C r eta R Rs halpha hbeta hC hr hr1 hRval hRder hRs hsmall sgn hsgn
  have ht : 0 ≤ alpha * eta / beta := (amp_sq_eq_abs alpha beta eta hside) ▸ (by positivity)
  have hsq := Real.sq_sqrt ht
  have hw : s ^ 2 ≤ (2 * alpha / |beta|) * |eta| := by
    have hq : |s| ^ 2 ≤ (9 / 8 * Real.sqrt (alpha * eta / beta)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg s) hamp 2
    rw [sq_abs] at hq
    rw [mul_pow, hsq] at hq
    rw [amp_sq_eq_abs alpha beta eta hside] at hq
    have hp : 0 ≤ alpha * |eta| / |beta| := by positivity
    calc s ^ 2 ≤ (9 / 8) ^ 2 * (alpha * |eta| / |beta|) := hq
      _ ≤ 2 * (alpha * |eta| / |beta|) := by nlinarith
      _ = (2 * alpha / |beta|) * |eta| := by ring
  have hd := (reducedField_hasDerivAt alpha beta R Rs eta s (hRder eta s he hsr)).deriv
  have hbound := equilibrium_derivative_error_window alpha beta eta s (R eta s) (Rs eta s)
    (deriv (reducedField alpha beta R eta) s) C (2 * alpha / |beta|) hs hC
    (by simpa [reducedField] using hroot) hd (hRval eta s he hsr) (hRs eta s he hsr) hw
  have hh := mul_le_mul_of_nonneg_left hamp (by positivity : 0 ≤ 2 * alpha / |beta|)
  change |deriv (reducedField alpha beta R eta) s + 2 * alpha * eta| ≤ _
  refine hbound.trans ?_
  unfold errorFactor
  gcongr

/-- Step 5's actual derivative little-o, restricted to the side containing nonzero branches. -/
theorem branch_derivative_isLittleO (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    (fun eta => deriv (reducedField alpha beta R eta)
        (branch alpha beta (branchRadius alpha beta C r) R sgn eta) + 2 * alpha * eta)
      =o[𝓝[{eta : ℝ | 0 < eta * beta}] 0] (fun eta => |eta|) := by
  apply Asymptotics.IsLittleO.of_bound
  intro eps heps
  have hfactor : ∀ᶠ eta in 𝓝 (0 : ℝ), errorFactor alpha beta C eta < eps :=
    (errorFactor_tendsto_zero alpha beta C).eventually (gt_mem_nhds heps)
  have hsmall : ∀ᶠ eta in 𝓝 (0 : ℝ), CurveSmall alpha beta C r eta :=
    curveSmall_mem_nhds alpha beta C r halpha hbeta hC hr
  filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
    hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with eta hf he hs
  simp only [Real.norm_eq_abs, abs_abs]
  exact (branch_derivative_error_bound alpha beta C r R Rs halpha hbeta hC hr hr1
    hRval hRder hRs eta he hs sgn hsgn).trans
      (mul_le_mul_of_nonneg_right hf.le (abs_nonneg eta))
end Branch
end ChemotaxisBifurcation.BranchDerivativeAsymptotic
