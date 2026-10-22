module
public import ChemotaxisBifurcation.FourierAmplitude

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.WeakH2CosineMode
open Set WeakH2PhaseSpace WeakH2AmbientClosure
noncomputable section

theorem mode_H2 {L : ℝ} (hL : 0 < L) (n : ℕ) :
    WeakDerivative1D.H2 L (neumannMode L n)
      (fun x => -waveNumber L n * Real.sin (waveNumber L n * x))
      (fun x => -(waveNumber L n)^2 * Real.cos (waveNumber L n * x)) := by
  apply ClassicalSobolevDictionary.classical_H2 hL
  · unfold neumannMode
    fun_prop
  · fun_prop
  · fun_prop
  · intro x _
    unfold neumannMode
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul (waveNumber L n)).cos
  · intro x _
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id x).const_mul (waveNumber L n)).sin).const_mul (-waveNumber L n)

theorem mode_neumann {L : ℝ} (hL : 0 < L) (n : ℕ) :
    WeakDerivative1D.NeumannTrace L
      (fun x => -waveNumber L n * Real.sin (waveNumber L n * x)) := by
  apply ClassicalSobolevDictionary.classical_neumann_trace
  · fun_prop
  · simp
  · have he : waveNumber L n * L = (n : ℝ) * Real.pi := by
      unfold waveNumber
      field_simp [ne_of_gt hL]
    rw [he,Real.sin_nat_mul_pi]
    simp

/-- The actual unnormalized cosine jet in the genuine weak-H2 Neumann phase.
Its derivatives and endpoint traces are proved through the classical dictionary. -/
def mode {L : ℝ} (hL : 0 < L) (n : ℕ) : Space L hL :=
  of_H2 hL (mode_H2 hL n) (mode_neumann hL n)

/-- The continuous population representative is exactly the manuscript cosine. -/
theorem profile_mode {L : ℝ} (hL : 0 < L) (n : ℕ) (x : Icc (0 : ℝ) L) :
    profileCLM hL (mode hL n) x = neumannMode L n x := by
  apply profile_of_H2 hL (mode_H2 hL n) (mode_neumann hL n)
  unfold neumannMode
  fun_prop

/-- Every positive cosine jet has zero actual population mass. -/
theorem mass_mode {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n) :
    populationMass hL (mode hL n) = 0 := by
  rw [populationMass_eq_of_rep hL (mode hL n) (neumannMode L n)
    (fun x => (profile_mode hL n x).symm)]
  exact integral_neumannMode_positive_zero L n hL hn

/-- The positive cosine jet belongs to the minimal mean-zero perturbation space. -/
theorem mode_mem_fixedMeanSet {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n) :
    mode hL n ∈ fixedMeanSet hL 0 := by
  change populationMass hL (mode hL n) = L * 0
  rw [mass_mode hL n hn,mul_zero]

/-- Literal positive-mode Fourier coordinates of cosine jets are Kronecker deltas. -/
theorem coefficient_mode_kronecker {L : ℝ} (hL : 0 < L) (k n : ℕ)
    (hk : 0 < k) (hn : 0 < n) :
    FourierAmplitude.coefficient hL k (mode hL n) = if k = n then 1 else 0 := by
  rw [FourierAmplitude.coefficient_eq_projection hL k (mode hL n) (neumannMode L n)
    (fun x => (profile_mode hL n x).symm)]
  unfold actualCriticalProjection
  rw [integral_neumannMode_mul L hL n k]
  by_cases h : k = n
  · subst k
    simp [hn.ne',ne_of_gt hL]
  · simp [h,Ne.symm h]

/-- Normalization is derived from the actual cosine integral, not assumed. -/
theorem coefficient_mode {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n) :
    FourierAmplitude.coefficient hL n (mode hL n) = 1 := by
  simpa using coefficient_mode_kronecker hL n n hn hn

end
end ChemotaxisBifurcation.WeakH2CosineMode
