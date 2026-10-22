module
public import ChemotaxisBifurcation.RemainderAmplitude

@[expose] public section

/-!
# Absorbing the paper's remainder bounds

These inequalities start with the manuscript's divided remainder estimate
`|e| ≤ C (|eta| + |s|) s²`. They derive parameter/amplitude comparison and an
explicit error proportional to |eta| for an existing nonzero equilibrium.
No branch existence or PDE theorem is asserted.
-/

namespace ChemotaxisBifurcation.NormalForm

theorem parameter_amplitude_bounds (alpha beta eta s e : ℝ)
    (halpha : 0 < alpha)
    (hroot : alpha * eta - beta * s ^ 2 + e = 0)
    (hsmall : |e| ≤ |beta| / 2 * s ^ 2) :
    |beta| / 2 * s ^ 2 ≤ alpha * |eta| ∧
      alpha * |eta| ≤ 3 * |beta| / 2 * s ^ 2 := by
  have hid1 : beta * s ^ 2 = alpha * eta + e := by linarith
  have h1 := abs_add_le (alpha * eta) e
  rw [← hid1] at h1
  simp only [abs_mul, abs_of_pos halpha, abs_of_nonneg (sq_nonneg s)] at h1
  have hid2 : alpha * eta = beta * s ^ 2 + -e := by linarith
  have h2 := abs_add_le (beta * s ^ 2) (-e)
  rw [← hid2] at h2
  simp only [abs_mul, abs_neg, abs_of_pos halpha, abs_of_nonneg (sq_nonneg s)] at h2
  constructor <;> nlinarith

theorem divided_remainder_cubic_bound (C D eta s e : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hs : |s| ≤ 1)
    (heta : |eta| ≤ D * s ^ 2)
    (herr : |e| ≤ C * (|eta| + |s|) * s ^ 2) :
    |e| ≤ (C * (D + 1)) * |s| ^ 3 := by
  have hs2 : s ^ 2 ≤ |s| := by nlinarith [sq_abs s, abs_nonneg s]
  have he1 : |eta| ≤ D * |s| :=
    heta.trans (mul_le_mul_of_nonneg_left hs2 hD)
  have hsum : |eta| + |s| ≤ (D + 1) * |s| := by nlinarith
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum hC) (sq_nonneg s)
  calc
    |e| ≤ C * (|eta| + |s|) * s ^ 2 := herr
    _ ≤ C * ((D + 1) * |s|) * s ^ 2 := hm
    _ = (C * (D + 1)) * |s| ^ 3 := by rw [← sq_abs s]; ring

/-- The paper's mixed remainder bound yields an explicit O(|eta|) error in the
square-root magnitude, after absorption on a small rectangle. -/
theorem magnitude_error_from_paper_bound (alpha beta eta s e C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : s ≠ 0)
    (hC : 0 ≤ C) (hs1 : |s| ≤ 1)
    (hroot : alpha * eta - beta * s ^ 2 + e = 0)
    (herr : |e| ≤ C * (|eta| + |s|) * s ^ 2)
    (hrectangle : C * (|eta| + |s|) ≤ |beta| / 2) :
    abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
      (2 * alpha * C * (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| := by
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have hs2 : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  have hsmall : |e| ≤ |beta| / 2 * s ^ 2 :=
    herr.trans (mul_le_mul_of_nonneg_right hrectangle hs2.le)
  have hstrict : |e| < |beta| * s ^ 2 := by nlinarith [mul_pos hb hs2]
  have hside := remainder_equilibrium_side alpha beta eta s e halpha hbeta hroot hstrict
  have ht := amplitude_sq_pos alpha beta eta halpha hside
  obtain ⟨hlow, hupp⟩ := parameter_amplitude_bounds alpha beta eta s e halpha hroot hsmall
  let D : ℝ := 3 * |beta| / (2 * alpha)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have heta : |eta| ≤ D * s ^ 2 := by
    have hdiv : |eta| ≤ (3 * |beta| / 2 * s ^ 2) / alpha :=
      (le_div_iff₀ halpha).mpr (by nlinarith)
    calc
      |eta| ≤ (3 * |beta| / 2 * s ^ 2) / alpha := hdiv
      _ = D * s ^ 2 := by dsimp [D]; ring
  have hsq : s ^ 2 ≤ (2 * alpha / |beta|) * |eta| := by
    have hdiv : s ^ 2 ≤ (2 * alpha * |eta|) / |beta| :=
      (le_div_iff₀ hb).mpr (by nlinarith)
    calc
      s ^ 2 ≤ (2 * alpha * |eta|) / |beta| := hdiv
      _ = (2 * alpha / |beta|) * |eta| := by ring
  have hec := divided_remainder_cubic_bound C D eta s e hC hD hs1 heta herr
  have hamp := remainder_magnitude_error alpha beta eta s e (C * (D + 1))
    hbeta hs hroot ht.le hec
  have hcoef : 0 ≤ C * (D + 1) / |beta| := by positivity
  calc
    abs (|s| - Real.sqrt (alpha * eta / beta)) ≤ C * (D + 1) * s ^ 2 / |beta| := hamp
    _ = (C * (D + 1) / |beta|) * s ^ 2 := by ring
    _ ≤ (C * (D + 1) / |beta|) * ((2 * alpha / |beta|) * |eta|) :=
      mul_le_mul_of_nonneg_left hsq hcoef
    _ = (2 * alpha * C * (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| := by
      dsimp [D]
      ring

/-- Finite endgame from the literal reduced equation and the two independent
paper remainder estimates. Existence of such an equilibrium is an input. -/
theorem paper_equilibrium_core (alpha beta eta s R Rs ds C : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hs : s ≠ 0)
    (hC : 0 ≤ C) (hs1 : |s| ≤ 1)
    (hroot : alpha * eta * s - beta * s ^ 3 + R = 0)
    (hderiv : ds = alpha * eta - 3 * beta * s ^ 2 + Rs)
    (hR : |R| ≤ C * (|eta| * |s| ^ 3 + |s| ^ 4))
    (hRs : |Rs| ≤ C * (|eta| * s ^ 2 + |s| ^ 3))
    (hrectangle : C * (|eta| + |s|) ≤ |beta| / 2) :
    0 < eta * beta ∧ ds * beta < 0 ∧
      abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
        (2 * alpha * C * (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| := by
  have hdivroot : alpha * eta - beta * s ^ 2 + R / s = 0 := by
    calc
      alpha * eta - beta * s ^ 2 + R / s =
          (alpha * eta * s - beta * s ^ 3 + R) / s := by
        field_simp [hs] <;> ring
      _ = 0 := by rw [hroot]; simp
  have hdivR : |R / s| ≤ C * (|eta| + |s|) * s ^ 2 := by
    rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hs)).mpr
    calc
      |R| ≤ C * (|eta| * |s| ^ 3 + |s| ^ 4) := hR
      _ = C * (|eta| + |s|) * s ^ 2 * |s| := by rw [← sq_abs s]; ring
  have hRs' : |Rs| ≤ C * (|eta| + |s|) * s ^ 2 := by
    calc
      |Rs| ≤ C * (|eta| * s ^ 2 + |s| ^ 3) := hRs
      _ = C * (|eta| + |s|) * s ^ 2 := by rw [← sq_abs s]; ring
  have hs2 : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have hrect := mul_le_mul_of_nonneg_right hrectangle hs2.le
  have hsmallR : |R / s| < |beta| * s ^ 2 := by
    nlinarith [mul_pos hb hs2]
  have hsmallBoth : |R / s| + |Rs| < 2 * |beta| * s ^ 2 := by
    nlinarith [mul_pos hb hs2]
  exact ⟨remainder_equilibrium_side alpha beta eta s (R / s)
      halpha hbeta hdivroot hsmallR,
    remainder_equilibrium_derivative_sign alpha beta eta s (R / s) Rs ds
      hbeta hdivroot hderiv hsmallBoth,
    magnitude_error_from_paper_bound alpha beta eta s (R / s) C
      halpha hbeta hs hC hs1 hdivroot hdivR hrectangle⟩

end ChemotaxisBifurcation.NormalForm
