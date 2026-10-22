module
public import ChemotaxisBifurcation.SignalTaylorRemainder
public import ChemotaxisBifurcation.MobilityDerivatives

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation
open Set

/-- Actual positive-base real powers have a derived quadratic Taylor error. -/
theorem rpow_quadratic_remainder (u q : ℝ) (hu : 0 < u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ u / 2 →
      |(u+s)^q - u^q - q*u^(q-1)*s - q*(q-1)*u^(q-2)/2*s^2|
        ≤ C * |s|^3 := by
  let p : PhysicalParams := ⟨0, 0, 0, 0, q, 1, 0, u, 0⟩
  obtain ⟨C, hC, hrem⟩ := signalSource_quartic_remainder p hu
  let D : ℝ := q*(q-1)*(q-2)*u^(q-3)/6
  refine ⟨C * (u/2) + |D|, by positivity, ?_⟩
  intro s hs
  have hh := hrem s hs
  simp only [p, rawTaylorData, one_mul] at hh
  change |(u+s)^q - u^q - q*u^(q-1)*s - q*(q-1)*u^(q-2)/2*s^2 - D*s^3|
    ≤ C * |s|^4 at hh
  let R := (u+s)^q - u^q - q*u^(q-1)*s - q*(q-1)*u^(q-2)/2*s^2
  change |R| ≤ _
  calc
    |R| = |(R-D*s^3)+D*s^3| := by congr 1; ring
    _ ≤ |R-D*s^3| + |D*s^3| := abs_add_le _ _
    _ ≤ C*|s|^4 + |D| *|s|^3 := by rw [abs_mul, abs_pow]; gcongr
    _ ≤ (C*(u/2)+|D|)*|s|^3 := by
      nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hC (pow_nonneg (abs_nonneg s) 3))]

private theorem quadratic_product_error
    (a b a0 a1 a2 b0 b1 b2 u v N A B D : ℝ)
    (hN : 0 ≤ N) (hN1 : N ≤ 1) (hu : |u| ≤ N) (hv : |v| ≤ N)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (_hD : 0 ≤ D) (hb : |b| ≤ D)
    (haerr : |a - (a0+a1*u+a2*u^2)| ≤ A*N^3)
    (hberr : |b - (b0+b1*v+b2*v^2)| ≤ B*N^3) :
    |a*b - (a0*b0+a1*b0*u+a0*b1*v+a2*b0*u^2+a1*b1*u*v+a0*b2*v^2)| ≤
      (A*D + (|a0|+|a1|+|a2|)*B + |a1*b2| + |a2*b1| + |a2*b2|)*N^3 := by
  let P := a0+a1*u+a2*u^2
  have hu1 : |u| ≤ 1 := hu.trans hN1
  have hP : |P| ≤ |a0|+|a1|+|a2| := by
    calc
      |P| ≤ |a0|+|a1*u|+|a2*u^2| := (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ |a0|+|a1|+|a2| := by
        rw [abs_mul, abs_mul, abs_pow]
        gcongr
        · exact mul_le_of_le_one_right (abs_nonneg _) hu1
        · exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg u) hu1)
  have hN4 : N^4 ≤ N^3 := by nlinarith [mul_nonneg (pow_nonneg hN 3) (sub_nonneg.mpr hN1)]
  have h1 : |(a-P)*b| ≤ (A*D)*N^3 := by
    rw [abs_mul]
    calc
      |a-P| *|b| ≤ (A*N^3)*D := mul_le_mul haerr hb (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h2 : |P*(b-(b0+b1*v+b2*v^2))| ≤ ((|a0|+|a1|+|a2|)*B)*N^3 := by
    rw [abs_mul]
    calc
      |P| *|b-(b0+b1*v+b2*v^2)| ≤ (|a0|+|a1|+|a2|)*(B*N^3) :=
        mul_le_mul hP hberr (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h3 : |a1*b2*u*v^2| ≤ |a1*b2| *N^3 := by
    rw [abs_mul, abs_mul, abs_pow]
    calc
      |a1*b2| *|u| *|v|^2 ≤ |a1*b2| *N*N^2 := by gcongr
      _ = _ := by ring
  have h4 : |a2*b1*u^2*v| ≤ |a2*b1| *N^3 := by
    rw [abs_mul, abs_mul, abs_pow]
    calc
      |a2*b1| *|u|^2*|v| ≤ |a2*b1| *N^2*N := by gcongr
      _ = _ := by ring
  have h5 : |a2*b2*u^2*v^2| ≤ |a2*b2| *N^3 := by
    rw [abs_mul, abs_mul, abs_pow, abs_pow]
    calc
      |a2*b2| *|u|^2*|v|^2 ≤ |a2*b2| *N^2*N^2 := by gcongr
      _ = |a2*b2| *N^4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hN4 (abs_nonneg _)
  have hid : a*b - (a0*b0+a1*b0*u+a0*b1*v+a2*b0*u^2+a1*b1*u*v+a0*b2*v^2) =
      (a-P)*b+P*(b-(b0+b1*v+b2*v^2))+a1*b2*u*v^2+a2*b1*u^2*v+a2*b2*u^2*v^2 := by
    dsimp [P]; ring
  rw [hid]
  calc
    _ ≤ |(a-P)*b| + |P*(b-(b0+b1*v+b2*v^2))| + |a1*b2*u*v^2| +
      |a2*b1*u^2*v| + |a2*b2*u^2*v^2| := by
        exact (abs_add_le _ _).trans (by gcongr; exact (abs_add_le _ _).trans (by gcongr; exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)))
    _ ≤ _ := by linarith

private theorem rpow_bounded_on_half (w q : ℝ) (hw : 0 < w) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ v : ℝ, |v| ≤ w/2 → |(w+v)^q| ≤ D := by
  have hc : ContinuousOn (fun y : ℝ => y^q) (Icc (w/2) (3*w/2)) := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    exact (Real.contDiffAt_rpow_const_of_ne (n := 1) (ne_of_gt hy0)).continuousAt.continuousWithinAt
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro v hv
  apply (hD (w+v) ?_).trans (le_max_left _ _)
  obtain ⟨hl, hr⟩ := abs_le.mp hv
  constructor <;> linarith

/-- The actual mobility has a quadratic Taylor remainder, with every
coefficient equal to the paper's raw Taylor dictionary. -/
theorem mobility_quadratic_remainder (p : PhysicalParams) (beta : ℝ)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v N : ℝ,
      0 ≤ N → N ≤ 1 → N ≤ p.uStar/2 → N ≤ p.signalOffset/2 →
      |u| ≤ N → |v| ≤ N →
      |(p.uStar+u)^p.m / (p.signalOffset+v)^beta -
        ((rawTaylorData p beta).B0 + (rawTaylorData p beta).Bu*u +
          (rawTaylorData p beta).Bv*v + (rawTaylorData p beta).Buu*u^2 +
          (rawTaylorData p beta).Buv*u*v + (rawTaylorData p beta).Bvv*v^2)| ≤ C*N^3 := by
  obtain ⟨A, hA, hAre⟩ := rpow_quadratic_remainder p.uStar p.m hu
  obtain ⟨B, hB, hBre⟩ := rpow_quadratic_remainder p.signalOffset (-beta) hw
  obtain ⟨D, hD, hDb⟩ := rpow_bounded_on_half p.signalOffset (-beta) hw
  let a0 := p.uStar^p.m
  let a1 := p.m*p.uStar^(p.m-1)
  let a2 := p.m*(p.m-1)*p.uStar^(p.m-2)/2
  let b0 := p.signalOffset^(-beta)
  let b1 := (-beta)*p.signalOffset^(-beta-1)
  let b2 := (-beta)*(-beta-1)*p.signalOffset^(-beta-2)/2
  refine ⟨A*D+(|a0|+|a1|+|a2|)*B+|a1*b2|+|a2*b1|+|a2*b2|, by positivity, ?_⟩
  intro u v N hN hN1 hNu hNv huN hvN
  have haerr : |(p.uStar+u)^p.m-(a0+a1*u+a2*u^2)| ≤ A*N^3 := by
    have h := hAre u (huN.trans hNu)
    have h' : |(p.uStar+u)^p.m-(a0+a1*u+a2*u^2)| ≤ A*|u|^3 := by
      convert h using 1
      congr 1
      dsimp [a0,a1,a2]
      ring
    exact h'.trans (by gcongr)
  have hberr : |(p.signalOffset+v)^(-beta)-(b0+b1*v+b2*v^2)| ≤ B*N^3 := by
    have h := hBre v (hvN.trans hNv)
    have h' : |(p.signalOffset+v)^(-beta)-(b0+b1*v+b2*v^2)| ≤ B*|v|^3 := by
      convert h using 1
      congr 1
      dsimp [b0,b1,b2]
      ring
    exact h'.trans (by gcongr)
  have h := quadratic_product_error ((p.uStar+u)^p.m) ((p.signalOffset+v)^(-beta))
    a0 a1 a2 b0 b1 b2 u v N A B D hN hN1 huN hvN hA hB hD
    (hDb v (hvN.trans hNv)) haerr hberr
  have hex1 : -beta-1 = -(beta+1) := by ring
  have hex2 : -beta-2 = -(beta+2) := by ring
  have hp : (rawTaylorData p beta).B0 + (rawTaylorData p beta).Bu*u +
      (rawTaylorData p beta).Bv*v + (rawTaylorData p beta).Buu*u^2 +
      (rawTaylorData p beta).Buv*u*v + (rawTaylorData p beta).Bvv*v^2 =
      a0*b0+a1*b0*u+a0*b1*v+a2*b0*u^2+a1*b1*u*v+a0*b2*v^2 := by
    simp only [a0,a1,a2,b0,b1,b2,hex1,hex2,Real.rpow_neg hw.le,
      rawTaylorData,div_eq_mul_inv]
    ring
  have hpos : 0 < p.signalOffset+v := by
    have hvlo := (abs_le.mp (hvN.trans hNv)).1
    linarith
  rw [hp,div_eq_mul_inv,← Real.rpow_neg hpos.le beta]
  exact h

/-- The actual mobility Taylor residual times the signal derivative is quartic
under the ordinary small C1 bounds; no flux-remainder hypothesis is supplied. -/
theorem mobility_flux_field_quartic_bound (p : PhysicalParams) (beta : ℝ)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L N : ℝ) (U V : ℝ → ℝ),
      0 ≤ N → N ≤ 1 → N ≤ p.uStar/2 → N ≤ p.signalOffset/2 →
      (∀ x ∈ Icc 0 L, |U x| ≤ N) →
      (∀ x ∈ Icc 0 L, |V x| ≤ N) →
      (∀ x ∈ Icc 0 L, |deriv V x| ≤ N) → ∀ x ∈ Icc 0 L,
      |((p.uStar+U x)^p.m / (p.signalOffset+V x)^beta -
        ((rawTaylorData p beta).B0 + (rawTaylorData p beta).Bu*U x +
          (rawTaylorData p beta).Bv*V x + (rawTaylorData p beta).Buu*(U x)^2 +
          (rawTaylorData p beta).Buv*U x*V x + (rawTaylorData p beta).Bvv*(V x)^2)) *
          deriv V x| ≤ C*N^4 := by
  obtain ⟨C, hC, hrem⟩ := mobility_quadratic_remainder p beta hu hw
  refine ⟨C, hC, ?_⟩
  intro L N U V hN hN1 hNu hNv hU hV hDV x hx
  rw [abs_mul]
  calc
    _ ≤ (C*N^3)*N := mul_le_mul
      (hrem (U x) (V x) N hN hN1 hNu hNv (hU x hx) (hV x hx))
      (hDV x hx) (abs_nonneg _) (by positivity)
    _ = C*N^4 := by ring

end ChemotaxisBifurcation
