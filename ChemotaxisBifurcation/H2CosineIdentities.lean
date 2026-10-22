module
public import ChemotaxisBifurcation.WeakDerivative1D

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.H2CosineIdentities
open Real Set MeasureTheory Filter Topology WeakDerivative1D CosineCoefficients
noncomputable section

/-- The actual weak H2 and Neumann data produce the classical representative,
with unchanged manuscript-normalized coefficients, absolute summability and
pointwise reconstruction. No external Sobolev/trace identification is assumed. -/
theorem representative_with_actual_coefficients {L : ℝ} (hL : 0 < L) {u du ddu : ℝ → ℝ}
    (hu : H2 L u du ddu) (hN : NeumannTrace L du) :
    ∃ U DU : ℝ → ℝ, NeumannW21 L U DU ∧
      (∀ᵐ x, x ∈ Ioo 0 L → u x = U x) ∧
      (∀ᵐ x, x ∈ Ioo 0 L → du x = DU x) ∧
      (∀ k, cosineCoeff L u k = cosineCoeff L U k) ∧
      Summable (fun k => ‖cosineCoeff L u k‖) ∧
      ∀ x ∈ Icc 0 L, HasSum (fun k => cosineCoeff L u k*cos ((k : ℝ)*Real.pi*x/L)) (U x) := by
  obtain ⟨U,DU,hU,hae,hdae⟩ := hu.exists_neumannW21 hL hN
  refine ⟨U,DU,hU,hae,hdae,cosineCoeff_congr_ae hL hae,hu.summable_norm_cosineCoeff hL hN,?_⟩
  intro x hx
  simpa only [cosineCoeff_congr_ae hL hae] using CosineCoefficients.hasSum_cosineCoeff L hL hU hx

/-- When the original representative is continuous, reconstruction holds for
that actual function at every endpoint and interior point, not merely a.e. -/
theorem hasSum_of_H2_continuous {L : ℝ} (hL : 0 < L) {u du ddu : ℝ → ℝ}
    (hu : H2 L u du ddu) (hN : NeumannTrace L du)
    (hc : ContinuousOn u (Icc 0 L)) :
    ∀ x ∈ Icc 0 L, HasSum (fun k => cosineCoeff L u k*cos ((k : ℝ)*Real.pi*x/L)) (u x) := by
  obtain ⟨U,hae,hUc,hsum⟩ := hu.hasSum_cosineCoeff hL hN
  have heq := eqOn_of_ae_eq_continuousOn hL hc hUc hae
  intro x hx
  rw [heq hx]
  exact hsum x hx

/-- Actual weak-H2-to-function identity; all coefficients are those of the original representatives. -/
theorem cosine_sine_sine_of_H2 (L : ℝ) (hL : 0 < L) {u u1 u2 : ℝ → ℝ}
    (hu : H2 L u u1 u2) (hNu : NeumannTrace L u1)
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        u x * Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (cosineCoeff L u (Int.natAbs ((n : ℤ) - k)) - cosineCoeff L u (n + k) +
        (if n = k then cosineCoeff L u 0 else 0)) := by
  obtain ⟨U,DU,hU,haeu,_⟩ := hu.exists_neumannW21 hL hNu
  simp_rw [cosineCoeff_congr_ae hL haeu]
  have hi : ∫ x in (0 : ℝ)..L,
        u x * Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) = ∫ x in (0 : ℝ)..L,
        U x * Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) := by
    apply integral_congr_ae_Ioo hL.le
    filter_upwards [haeu] with x hu hx
    simp only [hu hx]
  rw [hi]
  exact CosineCoefficients.cosine_sine_sine_of_neumann L hL hU n k hn hk

/-- Actual weak-H2-to-function identity; all coefficients are those of the original representatives. -/
theorem two_cosines_two_sines_of_H2 (L : ℝ) (hL : 0 < L) {u u1 u2 v v1 v2 : ℝ → ℝ}
    (hu : H2 L u u1 u2) (hNu : NeumannTrace L u1)
    (hv : H2 L v v1 v2) (hNv : NeumannTrace L v1)
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        u x * v x * Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) - k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) - k)},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) - k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = -((n : ℤ) - k)},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) + k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) + k)},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) + k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2)) := by
  obtain ⟨U,DU,hU,haeu,_⟩ := hu.exists_neumannW21 hL hNu
  obtain ⟨V,DV,hV,haev,_⟩ := hv.exists_neumannW21 hL hNv
  simp_rw [cosineCoeff_congr_ae hL haeu]
  simp_rw [cosineCoeff_congr_ae hL haev]
  have hi : ∫ x in (0 : ℝ)..L,
        u x * v x * Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) = ∫ x in (0 : ℝ)..L,
        U x * V x * Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) := by
    apply integral_congr_ae_Ioo hL.le
    filter_upwards [haeu,haev] with x hu hv hx
    simp only [hu hx,hv hx]
  rw [hi]
  exact CosineCoefficients.two_cosines_two_sines_of_neumann L hL hU hV n k hn hk

/-- Actual weak-H2-to-function identity; all coefficients are those of the original representatives. -/
theorem cos_cos_cos_of_H2 (L : ℝ) (hL : 0 < L) {u u1 u2 v v1 v2 : ℝ → ℝ}
    (hu : H2 L u u1 u2) (hNu : NeumannTrace L u1)
    (hv : H2 L v v1 v2) (hNv : NeumannTrace L v1)
    (k : ℕ) :
    ∫ x in (0 : ℝ)..L, u x * v x * Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -(k : ℤ)},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = k},
            cosineCoeff L u p.1.1 * cosineCoeff L v p.1.2)) +
        L / 4 * (if k = 0 then cosineCoeff L u 0 * cosineCoeff L v 0 else 0) := by
  obtain ⟨U,DU,hU,haeu,_⟩ := hu.exists_neumannW21 hL hNu
  obtain ⟨V,DV,hV,haev,_⟩ := hv.exists_neumannW21 hL hNv
  simp_rw [cosineCoeff_congr_ae hL haeu]
  simp_rw [cosineCoeff_congr_ae hL haev]
  have hi : ∫ x in (0 : ℝ)..L, u x * v x * Real.cos ((k : ℝ) * Real.pi * x / L) = ∫ x in (0 : ℝ)..L, U x * V x * Real.cos ((k : ℝ) * Real.pi * x / L) := by
    apply integral_congr_ae_Ioo hL.le
    filter_upwards [haeu,haev] with x hu hv hx
    simp only [hu hx,hv hx]
  rw [hi]
  exact CosineCoefficients.cos_cos_cos_of_neumann L hL hU hV k

/-- Actual weak-H2-to-function identity; all coefficients are those of the original representatives. -/
theorem cos_cos_cos_cos_of_H2 (L : ℝ) (hL : 0 < L) {u u1 u2 v v1 v2 w w1 w2 : ℝ → ℝ}
    (hu : H2 L u u1 u2) (hNu : NeumannTrace L u1)
    (hv : H2 L v v1 v2) (hNv : NeumannTrace L v1)
    (hw : H2 L w w1 w2) (hNw : NeumannTrace L w1)
    (k : ℕ) :
    ∫ x in (0 : ℝ)..L, u x * v x * w x * Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 + t.2.2 = k},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = k},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = -(k : ℤ)},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = k},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = -(k : ℤ)},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = k},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = -(k : ℤ)},
            cosineCoeff L u t.1.1 * cosineCoeff L v t.1.2.1 * cosineCoeff L w t.1.2.2)) +
        L / 8 * (if k = 0 then
          cosineCoeff L u 0 * cosineCoeff L v 0 * cosineCoeff L w 0 else 0) := by
  obtain ⟨U,DU,hU,haeu,_⟩ := hu.exists_neumannW21 hL hNu
  obtain ⟨V,DV,hV,haev,_⟩ := hv.exists_neumannW21 hL hNv
  obtain ⟨W,DW,hW,haew,_⟩ := hw.exists_neumannW21 hL hNw
  simp_rw [cosineCoeff_congr_ae hL haeu]
  simp_rw [cosineCoeff_congr_ae hL haev]
  simp_rw [cosineCoeff_congr_ae hL haew]
  have hi : ∫ x in (0 : ℝ)..L, u x * v x * w x * Real.cos ((k : ℝ) * Real.pi * x / L) = ∫ x in (0 : ℝ)..L, U x * V x * W x * Real.cos ((k : ℝ) * Real.pi * x / L) := by
    apply integral_congr_ae_Ioo hL.le
    filter_upwards [haeu,haev,haew] with x hu hv hw hx
    simp only [hu hx,hv hx,hw hx]
  rw [hi]
  exact CosineCoefficients.cos_cos_cos_cos_of_neumann L hL hU hV hW k

end
end ChemotaxisBifurcation.H2CosineIdentities
