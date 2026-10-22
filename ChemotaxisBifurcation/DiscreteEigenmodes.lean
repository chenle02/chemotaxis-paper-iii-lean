module
public import ChemotaxisBifurcation.Semidiscrete
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Cosine spectrum of the reflected Neumann stencil

This module starts the finite scheme-to-spectrum bridge for Theorem 1.4.  The
operator is the literal three-point negative Laplacian with reflected ghost
points and endpoint factor two.
-/

namespace ChemotaxisBifurcation.DiscreteEigenmodes

open ChemotaxisBifurcation.Semidiscrete

noncomputable section

abbrev Grid (N : ℕ) := Fin (N + 1)
abbrev GridFunction (N : ℕ) := Grid N → ℝ

def reflectedPrev (N : ℕ) (hN : 0 < N) (i : Grid N) : Grid N :=
  if hi : i.val = 0 then
    ⟨1, by omega⟩
  else
    ⟨i.val - 1, by omega⟩

def reflectedNext (N : ℕ) (hN : 0 < N) (i : Grid N) : Grid N :=
  if hi : i.val = N then
    ⟨N - 1, by omega⟩
  else
    ⟨i.val + 1, by omega⟩

def meshWidth (L : ℝ) (N : ℕ) : ℝ := L / (N : ℝ)

def reflectedNegLaplacianApply
    (L : ℝ) (N : ℕ) (hN : 0 < N) (u : GridFunction N) (i : Grid N) : ℝ :=
  (2 * u i - u (reflectedPrev N hN i) - u (reflectedNext N hN i)) /
    meshWidth L N ^ 2

def reflectedNegLaplacian
    (L : ℝ) (N : ℕ) (hN : 0 < N) : GridFunction N →ₗ[ℝ] GridFunction N where
  toFun u := reflectedNegLaplacianApply L N hN u
  map_add' u v := by
    funext i
    unfold reflectedNegLaplacianApply
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    funext i
    unfold reflectedNegLaplacianApply
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

def discreteCosineMode (N n : ℕ) : GridFunction N :=
  fun i => Real.cos ((n : ℝ) * Real.pi * (i : ℝ) / (N : ℝ))

theorem cos_step_identity (x theta : ℝ) :
    2 * Real.cos x - Real.cos (x - theta) - Real.cos (x + theta) =
      4 * Real.sin (theta / 2) ^ 2 * Real.cos x := by
  have hsc := Real.sin_sq_add_cos_sq (theta / 2)
  have hcos : Real.cos theta = 1 - 2 * Real.sin (theta / 2) ^ 2 := by
    rw [show theta = 2 * (theta / 2) by ring, Real.cos_two_mul]
    ring_nf at hsc ⊢
    nlinarith
  rw [Real.cos_sub, Real.cos_add, hcos]
  ring

theorem cos_reflected_right_identity (n : ℕ) (theta : ℝ) :
    2 * Real.cos ((n : ℝ) * Real.pi) -
        2 * Real.cos ((n : ℝ) * Real.pi - theta) =
      4 * Real.sin (theta / 2) ^ 2 * Real.cos ((n : ℝ) * Real.pi) := by
  have hsc := Real.sin_sq_add_cos_sq (theta / 2)
  have hcos : Real.cos theta = 1 - 2 * Real.sin (theta / 2) ^ 2 := by
    rw [show theta = 2 * (theta / 2) by ring, Real.cos_two_mul]
    ring_nf at hsc ⊢
    nlinarith
  have hsin : Real.sin ((n : ℝ) * Real.pi) = 0 := by
    simpa [mul_comm] using Real.sin_nat_mul_pi n
  rw [Real.cos_sub, hsin, hcos]
  ring_nf

/-- Pointwise cosine eigenpair for the literal reflected stencil. -/
theorem reflectedNegLaplacian_cosine_eigenpair
    (L : ℝ) (N n : ℕ) (hL : L ≠ 0) (hN : 0 < N) (hnN : n ≤ N) :
    reflectedNegLaplacian L N hN (discreteCosineMode N n) =
      discLam L n N • discreteCosineMode N n := by
  funext i
  let theta : ℝ := (n : ℝ) * Real.pi / (N : ℝ)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  by_cases hi0 : i.val = 0
  · have hiN : i.val ≠ N := by omega
    have hcur : discreteCosineMode N n i = 1 := by
      unfold discreteCosineMode
      rw [show (i : ℝ) = 0 by exact_mod_cast hi0]
      simp
    have hprev : discreteCosineMode N n (reflectedPrev N hN i) = Real.cos theta := by
      unfold discreteCosineMode
      rw [show (reflectedPrev N hN i).val = 1 by simp [reflectedPrev, hi0]]
      unfold theta
      norm_num
    have hnext : discreteCosineMode N n (reflectedNext N hN i) = Real.cos theta := by
      unfold discreteCosineMode
      rw [show (reflectedNext N hN i).val = 1 by
        unfold reflectedNext
        rw [dif_neg hiN]
        dsimp
        omega]
      unfold theta
      norm_num
    simp only [reflectedNegLaplacian, LinearMap.coe_mk, AddHom.coe_mk,
      reflectedNegLaplacianApply, Pi.smul_apply, smul_eq_mul]
    rw [hcur, hprev, hnext]
    rw [show 2 * 1 - Real.cos theta - Real.cos theta =
      2 - 2 * Real.cos theta by ring]
    have hstep := cos_step_identity 0 theta
    simp only [Real.cos_zero, zero_sub, Real.cos_neg, zero_add] at hstep
    have hstep' : 2 - 2 * Real.cos theta =
        4 * Real.sin (theta / 2) ^ 2 := by
      linarith [hstep]
    rw [hstep']
    unfold discLam discArg meshWidth theta
    field_simp [hL, hNR]
    <;> ring
  · by_cases hiN : i.val = N
    · have hcur : discreteCosineMode N n i = Real.cos ((n : ℝ) * Real.pi) := by
        unfold discreteCosineMode
        rw [show (i : ℝ) = (N : ℝ) by exact_mod_cast hiN]
        field_simp [hNR]
      have hprevMode :
          discreteCosineMode N n (reflectedPrev N hN i) =
            Real.cos ((n : ℝ) * Real.pi - theta) := by
        unfold discreteCosineMode
        rw [show (reflectedPrev N hN i).val = N - 1 by
          unfold reflectedPrev
          rw [dif_neg hi0]
          dsimp
          rw [hiN]]
        rw [Nat.cast_sub hN, Nat.cast_one]
        unfold theta
        field_simp [hNR]
      have hnextMode :
          discreteCosineMode N n (reflectedNext N hN i) =
            Real.cos ((n : ℝ) * Real.pi - theta) := by
        unfold discreteCosineMode
        rw [show (reflectedNext N hN i).val = N - 1 by
          simp [reflectedNext, hiN]]
        rw [Nat.cast_sub hN, Nat.cast_one]
        unfold theta
        field_simp [hNR]
      simp only [reflectedNegLaplacian, LinearMap.coe_mk, AddHom.coe_mk,
        reflectedNegLaplacianApply, Pi.smul_apply, smul_eq_mul]
      rw [hcur, hprevMode, hnextMode]
      rw [show 2 * Real.cos ((n : ℝ) * Real.pi) -
          Real.cos ((n : ℝ) * Real.pi - theta) -
          Real.cos ((n : ℝ) * Real.pi - theta) =
        2 * Real.cos ((n : ℝ) * Real.pi) -
          2 * Real.cos ((n : ℝ) * Real.pi - theta) by ring]
      have hstep := cos_reflected_right_identity n theta
      rw [hstep]
      unfold discLam discArg meshWidth theta
      field_simp [hL, hNR]
    · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi0
      have hiLt : i.val < N := by omega
      have hcurMode :
          discreteCosineMode N n i = Real.cos (theta * (i : ℝ)) := by
        unfold discreteCosineMode theta
        ring_nf
      have hprevMode :
          discreteCosineMode N n (reflectedPrev N hN i) =
            Real.cos (theta * (i : ℝ) - theta) := by
        unfold discreteCosineMode
        rw [show (reflectedPrev N hN i).val = i.val - 1 by
          simp [reflectedPrev, hi0]]
        rw [Nat.cast_sub hiPos, Nat.cast_one]
        unfold theta
        ring_nf
      have hnextMode :
          discreteCosineMode N n (reflectedNext N hN i) =
            Real.cos (theta * (i : ℝ) + theta) := by
        unfold discreteCosineMode
        rw [show (reflectedNext N hN i).val = i.val + 1 by
          simp [reflectedNext, hiN]]
        rw [Nat.cast_add, Nat.cast_one]
        unfold theta
        ring_nf
      simp only [reflectedNegLaplacian, LinearMap.coe_mk, AddHom.coe_mk,
        reflectedNegLaplacianApply, Pi.smul_apply, smul_eq_mul]
      rw [hcurMode, hprevMode, hnextMode]
      rw [cos_step_identity]
      unfold discLam discArg meshWidth theta
      field_simp [hL, hNR]

theorem discreteCosineMode_ne_zero (N n : ℕ) :
    discreteCosineMode N n ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Grid N)
  simp [discreteCosineMode] at h0


/-- The represented discrete eigenvalues are strictly increasing with the mode index. -/
theorem discLam_strictMono_on_represented
    (L : ℝ) (N n k : ℕ) (hL : L ≠ 0) (hN : 0 < N)
    (hnk : n < k) (hkN : k ≤ N) :
    discLam L n N < discLam L k N := by
  have hnN : n ≤ N := (Nat.le_of_lt hnk).trans hkN
  have han := discArg_mem_Icc n N hN hnN
  have hak := discArg_mem_Icc k N hN hkN
  have harg : discArg n N < discArg k N := by
    unfold discArg
    have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
    have hnkr : (n : ℝ) < (k : ℝ) := by exact_mod_cast hnk
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hnkr Real.pi_pos) (by positivity)
  have hslt : Real.sin (discArg n N) < Real.sin (discArg k N) :=
    Real.strictMonoOn_sin
      ⟨(le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) han.1), han.2⟩
      ⟨(le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hak.1), hak.2⟩ harg
  have hsn : 0 ≤ Real.sin (discArg n N) :=
    Real.sin_nonneg_of_nonneg_of_le_pi han.1
      (han.2.trans (by linarith [Real.pi_pos]))
  have hsk : 0 ≤ Real.sin (discArg k N) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hak.1
      (hak.2.trans (by linarith [Real.pi_pos]))
  have hsquare : Real.sin (discArg n N) ^ 2 < Real.sin (discArg k N) ^ 2 := by
    nlinarith
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmesh : L / (N : ℝ) ≠ 0 := div_ne_zero hL hNR
  unfold discLam
  exact mul_lt_mul_of_pos_left hsquare (by positivity)

/-- Distinct represented indices have distinct reflected-stencil eigenvalues. -/
theorem discLam_injective_on_grid (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N) :
    Function.Injective (fun n : Grid N => discLam L n.val N) := by
  intro i j hij
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact (ne_of_lt (discLam_strictMono_on_represented L N i.val j.val hL hN hlt
      (Nat.le_of_lt_succ j.isLt))) hij
  · exact (ne_of_gt (discLam_strictMono_on_represented L N j.val i.val hL hN hgt
      (Nat.le_of_lt_succ i.isLt))) hij

/-- Every represented cosine is a nonzero eigenvector of the reflected stencil. -/
theorem discreteCosineMode_hasEigenvector
    (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N) (n : Grid N) :
    Module.End.HasEigenvector (reflectedNegLaplacian L N hN)
      (discLam L n.val N) (discreteCosineMode N n.val) := by
  constructor
  · exact Module.End.mem_eigenspace_iff.mpr
      (reflectedNegLaplacian_cosine_eigenpair L N n.val hL hN
        (Nat.le_of_lt_succ n.isLt))
  · exact discreteCosineMode_ne_zero N n.val

/-- The `N+1` represented cosine eigenvectors are linearly independent. -/
theorem discreteCosineModes_linearIndependent
    (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N) :
    LinearIndependent ℝ (fun n : Grid N => discreteCosineMode N n.val) := by
  exact Module.End.eigenvectors_linearIndependent' (reflectedNegLaplacian L N hN)
    (fun n : Grid N => discLam L n.val N)
    (discLam_injective_on_grid L N hL hN)
    (fun n : Grid N => discreteCosineMode N n.val)
    (discreteCosineMode_hasEigenvector L N hL hN)

/-- The represented cosine eigenvectors form a basis of all grid functions. -/
noncomputable def discreteCosineBasis
    (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N) :
    Module.Basis (Grid N) ℝ (GridFunction N) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent
    (discreteCosineModes_linearIndependent L N hL hN)

/-- Every grid function has a finite expansion in the represented cosine modes. -/
theorem discreteCosineMode_exhaustion
    (L : ℝ) (N : ℕ) (hL : L ≠ 0) (hN : 0 < N) (u : GridFunction N) :
    ∃ c : Grid N → ℝ,
      ∑ n : Grid N, c n • discreteCosineMode N n.val = u := by
  classical
  let b := discreteCosineBasis L N hL hN
  refine ⟨fun n => b.repr u n, ?_⟩
  simpa [b, discreteCosineBasis,
    coe_basisOfPiSpaceOfLinearIndependent] using b.sum_repr u

end

end ChemotaxisBifurcation.DiscreteEigenmodes
