module
public import ChemotaxisBifurcation.WeakH2CosineMode
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Projection

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.FourierComplement
open Set Topology MeasureTheory WeakH2PhaseSpace WeakH2AmbientClosure FourierAmplitude WeakH2CosineMode
noncomputable section

/-- The literal physical Fourier-orthogonality subspace of genuine Neumann H2. -/
def complement {L : ℝ} (hL : 0 < L) (n : ℕ) : Submodule ℝ (Space L hL) :=
  (coefficientCLM hL n).ker

theorem mem_complement_iff {L : ℝ} (hL : 0 < L) (n : ℕ) (J : Space L hL) :
    J ∈ complement hL n ↔
      (∫ x : Icc (0 : ℝ) L, profileCLM hL J x * neumannMode L n x
        ∂SignalWeakSource.intervalVolume L) = 0 :=
  coefficient_eq_zero_iff hL n J

/-- A closed complement in the actual weak-H2 norm. -/
theorem isClosed_complement {L : ℝ} (hL : 0 < L) (n : ℕ) :
    IsClosed (complement hL n : Set (Space L hL)) :=
  (coefficientCLM hL n).isClosed_ker

/-- Continuous inclusion of the actual cosine line, with physical amplitude. -/
def modeLine {L : ℝ} (hL : 0 < L) (n : ℕ) : ℝ →L[ℝ] Space L hL :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (mode hL n)

theorem coefficient_modeLine {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n) :
    Function.RightInverse (modeLine hL n) (coefficientCLM hL n) := by
  intro a
  change coefficient hL n (a • mode hL n) = a
  rw [coefficient_smul,coefficient_mode hL n hn,mul_one]

/-- Every genuine phase point splits continuously into its physical Fourier
amplitude and its literal orthogonal remainder. This constructs neither a
center manifold nor a PDE local branch. -/
def splitting {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n) :
    Space L hL ≃L[ℝ] ℝ × complement hL n :=
  ContinuousLinearEquiv.equivOfRightInverse (coefficientCLM hL n) (modeLine hL n)
    (coefficient_modeLine hL n hn)

/-- The first coordinate is the actual population Fourier amplitude. -/
theorem splitting_amplitude {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (J : Space L hL) : (splitting hL n hn J).1 = coefficient hL n J := rfl

/-- The remainder is obtained by subtracting the actual normalized cosine mode. -/
theorem splitting_remainder {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (J : Space L hL) :
    ((splitting hL n hn J).2 : Space L hL) = J - coefficient hL n J • mode hL n := rfl

/-- Physical reconstruction, in the genuine phase rather than only pointwise. -/
theorem splitting_reconstruct {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (a : ℝ) (K : complement hL n) :
    (splitting hL n hn).symm (a,K) = a • mode hL n + K := rfl

/-- Uniqueness of the physical cosine coefficient and orthogonal remainder. -/
theorem decomposition_unique {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (J K : Space L hL) (a : ℝ) (hK : K ∈ complement hL n)
    (he : J = a • mode hL n + K) :
    a = coefficient hL n J ∧ K = J - coefficient hL n J • mode hL n := by
  have hz : coefficient hL n K = 0 := hK
  have ha : coefficient hL n J = a := by
    rw [he,coefficient_add,coefficient_smul,coefficient_mode hL n hn,hz,mul_one,add_zero]
  constructor
  · exact ha.symm
  · rw [ha,he]
    abel

/-- The normalized cosine span and the literal orthogonal kernel form a direct sum. -/
theorem isCompl_span_complement {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n) :
    IsCompl (Submodule.span ℝ {mode hL n}) (complement hL n) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro J hJ hK
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hJ
    have ha : a = 0 := by
      have hz : coefficient hL n (a • mode hL n) = 0 := hK
      rw [coefficient_smul,coefficient_mode hL n hn,mul_one] at hz
      exact hz
    simp [ha]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro J _
    rw [Submodule.mem_sup]
    refine ⟨coefficient hL n J • mode hL n,
      Submodule.mem_span_singleton.mpr ⟨_,rfl⟩,
      J - coefficient hL n J • mode hL n,?_,by abel⟩
    exact (splitting hL n hn J).2.property

/-- Removing a positive cosine mode preserves the actual mass, hence also
all fixed-mean affine slices used by the minimal model. -/
theorem remainder_mass {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (J : Space L hL) :
    populationMass hL (J - coefficient hL n J • mode hL n) = populationMass hL J := by
  rw [populationMass_sub,populationMass_smul,mass_mode hL n hn,mul_zero,sub_zero]

/-- The minimal fixed-mass model inherits the actual same splitting, with
a remainder of the prescribed mean and a mean-zero positive mode. -/
theorem remainder_mem_fixedMean_iff {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (J : Space L hL) (U : ℝ) :
    J - coefficient hL n J • mode hL n ∈ fixedMeanSet hL U ↔ J ∈ fixedMeanSet hL U := by
  change populationMass hL (J - coefficient hL n J • mode hL n) = L*U ↔ _
  rw [remainder_mass hL n hn]
  rfl

/-- The affine fixed-mean decomposition around the actual homogeneous
population has zero-mean, Fourier-orthogonal remainder, uniquely. -/
theorem existsUnique_fixedMean_decomposition {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (U : ℝ) (J : Space L hL) (hJ : J ∈ fixedMeanSet hL U) :
    ∃! z : ℝ × Space L hL,
      z.2 ∈ fixedMeanSet hL 0 ∧ z.2 ∈ complement hL n ∧
      J = const hL U + z.1 • mode hL n + z.2 := by
  let P := J - const hL U
  let a := coefficient hL n P
  let K := P - a • mode hL n
  have hP : P ∈ fixedMeanSet hL 0 := (mem_fixedMean_iff_sub_const hL U J).mp hJ
  have hKM : K ∈ fixedMeanSet hL 0 := (remainder_mem_fixedMean_iff hL n hn P 0).mpr hP
  have hKC : K ∈ complement hL n := (splitting hL n hn P).2.property
  refine ⟨(a,K),⟨hKM,hKC,by dsimp [K,P]; abel⟩,?_⟩
  rintro ⟨b,Q⟩ ⟨hQM,hQC,he⟩
  have heP : P = b • mode hL n + Q := by dsimp [P]; rw [he]; abel
  obtain ⟨hb,hQ⟩ := decomposition_unique hL n hn P Q b hQC heP
  exact Prod.ext hb hQ

/-- The canonical orthogonal correction around any homogeneous population.
No correction-existence or orthogonality hypothesis is required. -/
def canonicalRemainder {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (U : ℝ) (J : Space L hL) : complement hL n :=
  (splitting hL n hn (J - const hL U)).2

theorem continuous_canonicalRemainder {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (U : ℝ) : Continuous (canonicalRemainder hL n hn U) :=
  continuous_snd.comp ((splitting hL n hn).continuous.comp (continuous_id.sub continuous_const))

/-- The physical population profile has its canonical Fourier expansion at
all phase points, with amplitude computed from the actual population. -/
theorem canonical_profile_expansion {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (U : ℝ) (J : Space L hL) (x : Icc (0 : ℝ) L) :
    profileCLM hL J x = U + coefficient hL n J * neumannMode L n x +
      profileCLM hL (canonicalRemainder hL n hn U J) x := by
  have he : (canonicalRemainder hL n hn U J : Space L hL) =
      J - const hL U - coefficient hL n J • mode hL n := by
    rw [canonicalRemainder,splitting_remainder,coefficient_sub_const hL n hn]
  rw [he]
  simp only [map_sub,map_smul,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
    smul_eq_mul,profile_mode,profileCLM_const,ContinuousMap.const_apply]
  ring

/-- Canonical curve corrections need no separate orthogonality assumption.
The actual amplitude parameterization is still an explicit local-branch input. -/
theorem curve_canonical_expansion {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (U : ℝ) (c : ℝ → Space L hL) {D : Set ℝ}
    (ha : ∀ t ∈ D, coefficient hL n (c t) = t) :
    ∀ t ∈ D, ∀ x : Icc (0 : ℝ) L,
      profileCLM hL (c t) x = U + t * neumannMode L n x +
        profileCLM hL (canonicalRemainder hL n hn U (c t)) x := by
  intro t ht x
  simpa only [ha t ht] using canonical_profile_expansion hL n hn U (c t) x

end
end ChemotaxisBifurcation.FourierComplement
