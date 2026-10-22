module
/-
Copyright (c) 2026 Le Chen. Released under Apache 2.0 license as described in the file LICENSE.
-/

public import ChemotaxisBifurcation.FourierKernels
public import ChemotaxisBifurcation.FourierSeriesProducts

@[expose] public section

/-!
# Paper III, Lemma 2.1 (`L:trig-integrals`)

The four identities `E:cosine-sine-sine`, `E:two-cosines-two-sines`,
`E:cos-cos-cos` and `E:cos-cos-cos-cos`, stated unconditionally for
absolutely summable (`ℓ¹(ℕ₀)`) coefficient sequences on the interval
`[0, L]`, `L > 0`, with the unnormalized modes `cos (i π x / L)` and
`sin (n π x / L)`.

Each identity instantiates the kernel hypothesis of the corresponding
`FourierSeriesProducts.*_of_kernel` theorem with the signed kernel integral
of `FourierKernels`.  The constrained sums `∑_{i-j=r} u_i v_j` are tsums over
the subtype of index tuples satisfying the constraint, with all differences
taken in `ℤ`.  The `lp` versions take the coefficients in
`lp (fun _ : ℕ => ℝ) 1`, i.e. `ℓ¹(ℕ₀)` as in the lemma's hypothesis.

The bridge from the actual center-manifold phase space
(`H²` with Neumann conditions) to `ℓ¹` cosine coefficients is not proved here.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.TrigIntegrals

open ChemotaxisBifurcation.InfiniteCosineProjection
open ChemotaxisBifurcation.FourierKernels
open ChemotaxisBifurcation.FourierSeriesProducts

noncomputable section

private theorem ind_eq_ite {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) : ind P = if Q then 1 else 0 := by
  unfold ind
  by_cases hQ : Q
  · simp [hQ, h.mpr hQ]
  · simp [hQ, mt h.mp hQ]

/-! ### Kernel hypotheses in the raw indicator form -/

theorem kernel_cos_sin_sin (L : ℝ) (hL : 0 < L) (n k i : ℕ) :
    ∫ x in (0 : ℝ)..L,
        Real.cos ((i : ℝ) * Real.pi * x / L) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((if (i : ℤ) = (n : ℤ) - k then 1 else 0) +
        (if (i : ℤ) = -((n : ℤ) - k) then 1 else 0) -
        (if (i : ℤ) = (n : ℤ) + k then 1 else 0) -
        (if (i : ℤ) = -((n : ℤ) + k) then 1 else 0)) := by
  have h := integral_cos_sin_sin_signed L hL i n k
  simp only [cosinePhase, sinePhase] at h
  rw [h,
    ind_eq_ite (show (i : ℤ) + n - k = 0 ↔ (i : ℤ) = -((n : ℤ) - k) by omega),
    ind_eq_ite (show (i : ℤ) - n + k = 0 ↔ (i : ℤ) = (n : ℤ) - k by omega),
    ind_eq_ite (show (i : ℤ) + n + k = 0 ↔ (i : ℤ) = -((n : ℤ) + k) by omega),
    ind_eq_ite (show (i : ℤ) - n - k = 0 ↔ (i : ℤ) = (n : ℤ) + k by omega)]
  ring

theorem kernel_cos_cos_sin_sin (L : ℝ) (hL : 0 < L) (n k i j : ℕ) :
    ∫ x in (0 : ℝ)..L,
        Real.cos ((i : ℝ) * Real.pi * x / L) *
          Real.cos ((j : ℝ) * Real.pi * x / L) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 8 * ((if (i : ℤ) - j = (n : ℤ) - k then 1 else 0) +
        (if (i : ℤ) - j = -((n : ℤ) - k) then 1 else 0) +
        (if (i : ℤ) + j = (n : ℤ) - k then 1 else 0) +
        (if (i : ℤ) + j = -((n : ℤ) - k) then 1 else 0) -
        (if (i : ℤ) - j = (n : ℤ) + k then 1 else 0) -
        (if (i : ℤ) - j = -((n : ℤ) + k) then 1 else 0) -
        (if (i : ℤ) + j = (n : ℤ) + k then 1 else 0) -
        (if (i : ℤ) + j = -((n : ℤ) + k) then 1 else 0)) := by
  have h := integral_cos_cos_sin_sin_signed L hL i j n k
  simp only [cosinePhase, sinePhase] at h
  rw [h,
    ind_eq_ite (show (i : ℤ) + j + n - k = 0 ↔ (i : ℤ) + j = -((n : ℤ) - k) by
      omega),
    ind_eq_ite (show (i : ℤ) + j - n + k = 0 ↔ (i : ℤ) + j = (n : ℤ) - k by
      omega),
    ind_eq_ite (show (i : ℤ) - j + n - k = 0 ↔ (i : ℤ) - j = -((n : ℤ) - k) by
      omega),
    ind_eq_ite (show (i : ℤ) - j - n + k = 0 ↔ (i : ℤ) - j = (n : ℤ) - k by
      omega),
    ind_eq_ite (show (i : ℤ) + j + n + k = 0 ↔ (i : ℤ) + j = -((n : ℤ) + k) by
      omega),
    ind_eq_ite (show (i : ℤ) + j - n - k = 0 ↔ (i : ℤ) + j = (n : ℤ) + k by
      omega),
    ind_eq_ite (show (i : ℤ) - j + n + k = 0 ↔ (i : ℤ) - j = -((n : ℤ) + k) by
      omega),
    ind_eq_ite (show (i : ℤ) - j - n - k = 0 ↔ (i : ℤ) - j = (n : ℤ) + k by
      omega)]
  ring

theorem kernel_cos_cos_cos (L : ℝ) (hL : 0 < L) (k i j : ℕ) :
    ∫ x in (0 : ℝ)..L,
        Real.cos ((i : ℝ) * Real.pi * x / L) *
          Real.cos ((j : ℝ) * Real.pi * x / L) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((if (i : ℤ) + j = k then 1 else 0) +
        (if (i : ℤ) + j = -(k : ℤ) then 1 else 0) +
        (if (i : ℤ) - j = k then 1 else 0) +
        (if (i : ℤ) - j = -(k : ℤ) then 1 else 0)) := by
  have h := integral_cos_cos_cos_signed L hL i j k
  simp only [cosinePhase] at h
  rw [h,
    ind_eq_ite (show (i : ℤ) + j + k = 0 ↔ (i : ℤ) + j = -(k : ℤ) by omega),
    ind_eq_ite (show (i : ℤ) + j - k = 0 ↔ (i : ℤ) + j = k by omega),
    ind_eq_ite (show (i : ℤ) - j + k = 0 ↔ (i : ℤ) - j = -(k : ℤ) by omega),
    ind_eq_ite (show (i : ℤ) - j - k = 0 ↔ (i : ℤ) - j = k by omega)]
  ring

theorem kernel_cos_cos_cos_cos (L : ℝ) (hL : 0 < L) (k i j l : ℕ) :
    ∫ x in (0 : ℝ)..L,
        Real.cos ((i : ℝ) * Real.pi * x / L) *
          Real.cos ((j : ℝ) * Real.pi * x / L) *
          Real.cos ((l : ℝ) * Real.pi * x / L) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 * ((if (i : ℤ) + j + l = k then 1 else 0) +
        (if (i : ℤ) + j + l = -(k : ℤ) then 1 else 0) +
        (if (i : ℤ) + j - l = k then 1 else 0) +
        (if (i : ℤ) + j - l = -(k : ℤ) then 1 else 0) +
        (if (i : ℤ) - j + l = k then 1 else 0) +
        (if (i : ℤ) - j + l = -(k : ℤ) then 1 else 0) +
        (if (i : ℤ) - j - l = k then 1 else 0) +
        (if (i : ℤ) - j - l = -(k : ℤ) then 1 else 0)) := by
  have h := integral_cos_cos_cos_cos_signed L hL i j l k
  simp only [cosinePhase] at h
  rw [h,
    ind_eq_ite (show (i : ℤ) + j + l + k = 0 ↔ (i : ℤ) + j + l = -(k : ℤ) by
      omega),
    ind_eq_ite (show (i : ℤ) + j + l - k = 0 ↔ (i : ℤ) + j + l = k by omega),
    ind_eq_ite (show (i : ℤ) + j - l + k = 0 ↔ (i : ℤ) + j - l = -(k : ℤ) by
      omega),
    ind_eq_ite (show (i : ℤ) + j - l - k = 0 ↔ (i : ℤ) + j - l = k by omega),
    ind_eq_ite (show (i : ℤ) - j + l + k = 0 ↔ (i : ℤ) - j + l = -(k : ℤ) by
      omega),
    ind_eq_ite (show (i : ℤ) - j + l - k = 0 ↔ (i : ℤ) - j + l = k by omega),
    ind_eq_ite (show (i : ℤ) - j - l + k = 0 ↔ (i : ℤ) - j - l = -(k : ℤ) by
      omega),
    ind_eq_ite (show (i : ℤ) - j - l - k = 0 ↔ (i : ℤ) - j - l = k by omega)]
  ring

/-! ### Lemma 2.1 for absolutely summable coefficient sequences -/

/-- Lemma 2.1, display `E:cosine-sine-sine`. -/
theorem cosine_sine_sine (L : ℝ) (hL : 0 < L) (u : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (u (Int.natAbs ((n : ℤ) - k)) - u (n + k) +
        (if n = k then u 0 else 0)) :=
  cosine_sine_sine_of_kernel L u hu n k hn hk (kernel_cos_sin_sin L hL n k)

/-- Lemma 2.1, display `E:two-cosines-two-sines`. -/
theorem two_cosines_two_sines (L : ℝ) (hL : 0 < L) (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) + k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2)) :=
  two_cosines_two_sines_of_kernel L u v hu hv n k hn hk
    (kernel_cos_cos_sin_sin L hL n k)

/-- Lemma 2.1, display `E:cos-cos-cos` (`k ≥ 0`). -/
theorem cos_cos_cos (L : ℝ) (hL : 0 < L) (u v : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k}, u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -(k : ℤ)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = k}, u p.1.1 * v p.1.2)) +
        L / 4 * (if k = 0 then u 0 * v 0 else 0) :=
  cos_cos_cos_of_kernel L u v hu hv k (kernel_cos_cos_cos L hL k)

/-- Lemma 2.1, display `E:cos-cos-cos-cos` (`k ≥ 0`). -/
theorem cos_cos_cos_cos (L : ℝ) (hL : 0 < L) (u v w : ℕ → ℝ)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖)
    (hw : Summable fun l => ‖w l‖) (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          (∑' l : ℕ, w l * Real.cos ((l : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2)) +
        L / 8 * (if k = 0 then u 0 * v 0 * w 0 else 0) :=
  cos_cos_cos_cos_of_kernel L u v w hu hv hw k (kernel_cos_cos_cos_cos L hL k)

/-! ### `ℓ¹(ℕ₀)` versions (coefficients in `lp (fun _ : ℕ => ℝ) 1`) -/

/-- Lemma 2.1, display `E:cosine-sine-sine`, for `u ∈ ℓ¹(ℕ₀)`. -/
theorem cosine_sine_sine_lp (L : ℝ) (hL : 0 < L)
    (u : lp (fun _ : ℕ => ℝ) 1) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 4 * (u (Int.natAbs ((n : ℤ) - k)) - u (n + k) +
        (if n = k then u 0 else 0)) :=
  cosine_sine_sine L hL u (summable_norm_of_lp_one u) n k hn hk

/-- Lemma 2.1, display `E:two-cosines-two-sines`, for `u, v ∈ ℓ¹(ℕ₀)`. -/
theorem two_cosines_two_sines_lp (L : ℝ) (hL : 0 < L)
    (u v : lp (fun _ : ℕ => ℝ) 1) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.sin ((n : ℝ) * Real.pi * x / L) *
          Real.sin ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) - k},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = -((n : ℤ) - k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -((n : ℤ) + k)},
            u p.1.1 * v p.1.2) -
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = (n : ℤ) + k},
            u p.1.1 * v p.1.2)) :=
  two_cosines_two_sines L hL u v (summable_norm_of_lp_one u)
    (summable_norm_of_lp_one v) n k hn hk

/-- Lemma 2.1, display `E:cos-cos-cos`, for `u, v ∈ ℓ¹(ℕ₀)`. -/
theorem cos_cos_cos_lp (L : ℝ) (hL : 0 < L) (u v : lp (fun _ : ℕ => ℝ) 1)
    (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 4 * ((∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k}, u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -(k : ℤ)},
            u p.1.1 * v p.1.2) +
          (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) + p.2 = k}, u p.1.1 * v p.1.2)) +
        L / 4 * (if k = 0 then u 0 * v 0 else 0) :=
  cos_cos_cos L hL u v (summable_norm_of_lp_one u) (summable_norm_of_lp_one v) k

/-- Lemma 2.1, display `E:cos-cos-cos-cos`, for `u, v, w ∈ ℓ¹(ℕ₀)`. -/
theorem cos_cos_cos_cos_lp (L : ℝ) (hL : 0 < L)
    (u v w : lp (fun _ : ℕ => ℝ) 1) (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          (∑' l : ℕ, w l * Real.cos ((l : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2)) +
        L / 8 * (if k = 0 then u 0 * v 0 * w 0 else 0) :=
  cos_cos_cos_cos L hL u v w (summable_norm_of_lp_one u)
    (summable_norm_of_lp_one v) (summable_norm_of_lp_one w) k

end

end ChemotaxisBifurcation.TrigIntegrals
