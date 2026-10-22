module
public import ChemotaxisBifurcation.WeakH2AmbientClosure
public import ChemotaxisBifurcation.CubicJetExtraction
public import ChemotaxisBifurcation.QuadraticModeSupport
public import ChemotaxisBifurcation.ParametrizedSolutionComponents

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.FourierAmplitude
open Set Topology MeasureTheory WeakH2PhaseSpace WeakH2AmbientClosure GlobalBranch
noncomputable section

/-- The physical population Fourier coordinate, normalized for positive modes.
At mode zero this definition is twice the mean; positive-mode theorems retain n>0. -/
def coefficient {L : ℝ} (hL : 0 < L) (n : ℕ) (J : Space L hL) : ℝ :=
  2/L * ∫ x : Icc (0 : ℝ) L,
    profileCLM hL J x * neumannMode L n x ∂SignalWeakSource.intervalVolume L

/-- Continuity in the genuine weak-H2 norm follows from its proved profile map. -/
theorem continuous_coefficient {L : ℝ} (hL : 0 < L) (n : ℕ) :
    Continuous (coefficient hL n) := by
  let w : C(Icc (0 : ℝ) L,ℝ) := ⟨fun x => neumannMode L n x,by
    unfold neumannMode waveNumber
    fun_prop⟩
  let mu := SignalWeakSource.intervalVolume L
  let T := ContinuousMap.toLp (1 : ENNReal) mu ℝ (E := ℝ)
  have hF : Continuous (fun J : Space L hL => profileCLM hL J * w) :=
    (profileCLM hL).continuous.mul continuous_const
  have h := (MeasureTheory.continuous_integral (μ := mu)).comp (T.continuous.comp hF)
  have he : (fun J : Space L hL => ∫ x, T (profileCLM hL J * w) x ∂mu) =
      fun J => ∫ x, profileCLM hL J x * neumannMode L n x ∂mu := by
    funext J
    exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (1 : ENNReal)) mu (profileCLM hL J * w))
  change Continuous (fun J : Space L hL => ∫ x, T (profileCLM hL J * w) x ∂mu) at h
  rw [he] at h
  exact continuous_const.mul h

/-- Additivity of the actual coordinate, with integrability derived on the compact interval. -/
theorem coefficient_add {L : ℝ} (hL : 0 < L) (n : ℕ) (J K : Space L hL) :
    coefficient hL n (J+K) = coefficient hL n J + coefficient hL n K := by
  have hw : Continuous (fun x : Icc (0 : ℝ) L => neumannMode L n x) := by
    unfold neumannMode waveNumber
    fun_prop
  have hi (J : Space L hL) : Integrable (fun x : Icc (0 : ℝ) L =>
      profileCLM hL J x * neumannMode L n x) (SignalWeakSource.intervalVolume L) :=
    ((profileCLM hL J).continuous.mul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [coefficient,map_add,ContinuousMap.add_apply,add_mul]
  rw [integral_add (hi J) (hi K)]
  ring

theorem coefficient_smul {L : ℝ} (hL : 0 < L) (n : ℕ) (a : ℝ) (J : Space L hL) :
    coefficient hL n (a • J) = a * coefficient hL n J := by
  simp only [coefficient,map_smul,ContinuousMap.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]
  ring

/-- The physical coordinate as a continuous linear functional, not a continuity premise. -/
def coefficientCLM {L : ℝ} (hL : 0 < L) (n : ℕ) : Space L hL →L[ℝ] ℝ where
  toFun := coefficient hL n
  map_add' := coefficient_add hL n
  map_smul' := coefficient_smul hL n
  cont := continuous_coefficient hL n

/-- Agreement with the literal normalized interval projection of any representative. -/
theorem coefficient_eq_projection {L : ℝ} (hL : 0 < L) (n : ℕ) (J : Space L hL)
    (u : ℝ → ℝ) (hRep : ∀ x : Icc (0 : ℝ) L, u x = profileCLM hL J x) :
    coefficient hL n J = actualCriticalProjection L n u := by
  unfold coefficient actualCriticalProjection
  congr 1
  calc (∫ x : Icc (0 : ℝ) L, profileCLM hL J x * neumannMode L n x ∂SignalWeakSource.intervalVolume L) =
      ∫ x : Icc (0 : ℝ) L, u x * neumannMode L n x ∂SignalWeakSource.intervalVolume L := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by dsimp; rw [hRep x])
    _ = _ := SignalWeakSource.integral_intervalVolume hL.le (fun x => u x * neumannMode L n x)

/-- Positive cosine coordinates vanish at every constant equilibrium. -/
theorem coefficient_const {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n) (U : ℝ) :
    coefficient hL n (WeakH2PhaseSpace.const hL U) = 0 := by
  rw [coefficient_eq_projection hL n _ (fun _ => U) (fun x => by rw [profileCLM_const]; rfl)]
  simp only [actualCriticalProjection,intervalIntegral.integral_const_mul,
    integral_neumannMode_positive_zero L n hL hn,mul_zero]

/-- The manuscript's orthogonal complement is genuinely closed in the full phase. -/
theorem isClosed_zero_coordinate {L : ℝ} (hL : 0 < L) (n : ℕ) :
    IsClosed {J : Space L hL | coefficient hL n J = 0} :=
  isClosed_eq (continuous_coefficient hL n) continuous_const

/-- Agreement with the existing positive-mode cosine-series convention. -/
theorem coefficient_eq_cosineCoeff {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (J : Space L hL) (u : ℝ → ℝ)
    (hRep : ∀ x : Icc (0 : ℝ) L, u x = profileCLM hL J x) :
    coefficient hL n J = CosineCoefficients.cosineCoeff L u n := by
  rw [coefficient_eq_projection hL n J u hRep]
  simp only [CosineCoefficients.cosineCoeff,ite_eq_right hn.ne',actualCriticalProjection]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  have ha : waveNumber L n * x = (n : ℝ) * Real.pi * x / L := by
    unfold waveNumber
    ring
  simp only [neumannMode,ha]

/-- Constant translation does not change any positive-mode coordinate. -/
theorem coefficient_sub_const {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (J : Space L hL) (U : ℝ) :
    coefficient hL n (J - WeakH2PhaseSpace.const hL U) = coefficient hL n J := by
  change coefficientCLM hL n (J - WeakH2PhaseSpace.const hL U) = _
  rw [map_sub]
  change coefficient hL n J - coefficient hL n (WeakH2PhaseSpace.const hL U) = _
  rw [coefficient_const hL n hn U,sub_zero]

/-- Exact equivalence with the manuscript's unnormalized orthogonality test. -/
theorem coefficient_eq_zero_iff {L : ℝ} (hL : 0 < L) (n : ℕ) (J : Space L hL) :
    coefficient hL n J = 0 ↔
      (∫ x : Icc (0 : ℝ) L, profileCLM hL J x * neumannMode L n x ∂SignalWeakSource.intervalVolume L) = 0 := by
  simp [coefficient,mul_eq_zero,ne_of_gt hL]

/-- The literal Fourier-orthogonality space is closed in the genuine phase. -/
theorem isClosed_orthogonal {L : ℝ} (hL : 0 < L) (n : ℕ) :
    IsClosed {J : Space L hL | (∫ x : Icc (0 : ℝ) L,
      profileCLM hL J x * neumannMode L n x ∂SignalWeakSource.intervalVolume L) = 0} := by
  convert isClosed_zero_coordinate hL n using 1
  ext J
  exact (coefficient_eq_zero_iff hL n J).symm

/-- The same complement condition remains closed on the minimal model's
actual mean-zero perturbation space. -/
theorem isClosed_minimal_orthogonal {L : ℝ} (hL : 0 < L) (n : ℕ) :
    IsClosed (fixedMeanSet hL 0 ∩ {J : Space L hL | (∫ x : Icc (0 : ℝ) L,
      profileCLM hL J x * neumannMode L n x ∂SignalWeakSource.intervalVolume L) = 0}) :=
  (isClosed_fixedMeanSet hL 0).inter (isClosed_orthogonal hL n)

/-- Orthogonal-remainder parametrization gives the exact physical amplitude.
The expansion and orthogonality are supplied; their normalized coordinate is derived. -/
theorem coefficient_of_decomposition {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (J K : Space L hL) (U a : ℝ)
    (hRep : ∀ x : Icc (0 : ℝ) L, profileCLM hL J x =
      U + a * neumannMode L n x + profileCLM hL K x)
    (hK : coefficient hL n K = 0) : coefficient hL n J = a := by
  let mu := SignalWeakSource.intervalVolume L
  have hw : Continuous (fun x : Icc (0 : ℝ) L => neumannMode L n x) := by
    unfold neumannMode waveNumber
    fun_prop
  have hi0 : Integrable (fun x : Icc (0 : ℝ) L => U * neumannMode L n x) mu :=
    (continuous_const.mul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun x : Icc (0 : ℝ) L => a * (neumannMode L n x * neumannMode L n x)) mu :=
    (continuous_const.mul (hw.mul hw)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x : Icc (0 : ℝ) L => profileCLM hL K x * neumannMode L n x) mu :=
    ((profileCLM hL K).continuous.mul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : (∫ x : Icc (0 : ℝ) L, neumannMode L n x ∂mu) = 0 := by
    rw [SignalWeakSource.integral_intervalVolume hL.le (neumannMode L n)]
    exact integral_neumannMode_positive_zero L n hL hn
  have hs : (∫ x : Icc (0 : ℝ) L, neumannMode L n x * neumannMode L n x ∂mu) = L/2 := by
    rw [SignalWeakSource.integral_intervalVolume hL.le (fun x => neumannMode L n x * neumannMode L n x)]
    simp only [integral_neumannMode_mul L hL,ite_true,ite_eq_right hn.ne']
  have he : (fun x : Icc (0 : ℝ) L => profileCLM hL J x * neumannMode L n x) =
      fun x : Icc (0 : ℝ) L => (U * neumannMode L n x + a * (neumannMode L n x * neumannMode L n x)) +
        profileCLM hL K x * neumannMode L n x := by
    funext x
    rw [hRep x]
    ring
  change 2/L * (∫ x : Icc (0 : ℝ) L, profileCLM hL J x * neumannMode L n x ∂mu) = a
  rw [he]
  rw [integral_add
    (f := fun x : Icc (0 : ℝ) L => U * neumannMode L n x + a * (neumannMode L n x * neumannMode L n x))
    (g := fun x : Icc (0 : ℝ) L => profileCLM hL K x * neumannMode L n x) (hi0.add hi1) hi2]
  rw [integral_add hi0 hi1,integral_const_mul,integral_const_mul,hz,hs,mul_zero,zero_add]
  change 2/L * (a * (L/2) + _) = a
  calc _ = a + coefficient hL n K := by
         unfold coefficient
         dsimp [mu]
         field_simp [ne_of_gt hL]
       _ = a := by rw [hK,add_zero]

/-- Actual amplitude on parameter/population pairs, evaluated on the population component. -/
def amplitude {L : ℝ} (hL : 0 < L) (n : ℕ) (z : ℝ × Space L hL) : ℝ :=
  coefficient hL n z.2

theorem continuous_amplitude {L : ℝ} (hL : 0 < L) (n : ℕ) :
    Continuous (amplitude hL n) :=
  (continuous_coefficient hL n).comp continuous_snd

/-- A local curve expressed with a Fourier-orthogonal remainder has parameter t
as its actual population amplitude; neither amplitude equality nor continuity is assumed. -/
theorem curve_amplitude {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    {V : Set (ℝ × Space L hL)} (c : ℝ → V) (r : ℝ → Space L hL) (U : ℝ)
    {eps : ℝ}
    (hRep : ∀ t ∈ Ioo (-eps) eps, ∀ x : Icc (0 : ℝ) L,
      profileCLM hL (c t).val.2 x = U + t * neumannMode L n x + profileCLM hL (r t) x)
    (hOrth : ∀ t ∈ Ioo (-eps) eps,
      (∫ x : Icc (0 : ℝ) L, profileCLM hL (r t) x * neumannMode L n x ∂SignalWeakSource.intervalVolume L) = 0) :
    ∀ t ∈ Ioo (-eps) eps, amplitude hL n (c t) = t := by
  intro t ht
  exact coefficient_of_decomposition hL n hn (c t).val.2 (r t) U t (hRep t ht) ((coefficient_eq_zero_iff hL n (r t)).2 (hOrth t ht))

/-- A zero remainder at the base identifies its actual population as the constant
in the supplied curve expansion. No critical-parameter identity is inferred. -/
theorem curve_base_population {L : ℝ} (hL : 0 < L) (n : ℕ)
    {V : Set (ℝ × Space L hL)} (c : ℝ → V) (r : ℝ → Space L hL) (U : ℝ)
    {eps : ℝ} (heps : 0 < eps)
    (hRep : ∀ t ∈ Ioo (-eps) eps, ∀ x : Icc (0 : ℝ) L,
      profileCLM hL (c t).val.2 x = U + t * neumannMode L n x + profileCLM hL (r t) x)
    (hZero : r 0 = 0) : (c 0).val.2 = WeakH2PhaseSpace.const hL U := by
  apply profileCLM_injective hL
  apply ContinuousMap.ext
  intro x
  rw [hRep 0 ⟨by linarith,heps⟩ x,hZero,profileCLM_const]
  simp

/-- Actual logistic selected-image deduction with the physical Fourier coordinate.
Curve existence, expansion, orthogonality and chart exhaustion remain explicit. -/
theorem logistic_of_fourier_curve (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (hp : p.LogisticAdmissible)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2) (hg1 : p.gamma ≤ 1+p.alpha) (hbeta : 0 ≤ beta)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ logisticSolutionSet p hL beta)
    (c : ℝ → (AmbientClosure.admissibleSet (profileCLM hL) univ)) (r : ℝ → Space L hL) (n : ℕ) (hn : 0 < n) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps))
    (hsol : ∀ t ∈ Ioo (-eps) eps, t ≠ 0 → (c t : ℝ × Space L hL) ∈ S)
    (hRep : ∀ t ∈ Ioo (-eps) eps, ∀ x : Icc (0 : ℝ) L,
      profileCLM hL (c t).val.2 x = p.uStar + t * neumannMode L n x + profileCLM hL (r t) x)
    (hOrth : ∀ t ∈ Ioo (-eps) eps,
      (∫ x : Icc (0 : ℝ) L, profileCLM hL (r t) x * neumannMode L n x ∂SignalWeakSource.intervalVolume L) = 0)
    (hZero : r 0 = 0)
    (U : Set (AmbientClosure.admissibleSet (profileCLM hL) univ)) (hU : IsOpen U)
    (hnegative : ∀ t ∈ Ioo (-eps) 0, c t ∈ U)
    (hexhaust : ∀ x ∈ parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × Space L hL) ⁻¹' S)) (c 0),
      x ∈ U → ∃ t ∈ Ioo (-eps) eps, c t = x) :
    (IsClosed (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta)) ∧
    IsConnected (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta)) ∧
    (c 0 : ℝ × (Space L hL)) ∈ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta) ∧
    (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × (Space L hL)) '' (c '' Ico 0 eps)) ⊆ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta) ∧
    selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta) ⊆ (AmbientClosure.admissibleSet (profileCLM hL) univ) ∧
    selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta) ⊆ closure S ∧
    ∀ X : ℝ, IsCompact (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta) ∩ {z | z.1 ≤ X})) ∧ (c 0).val.2 = WeakH2PhaseSpace.const hL p.uStar := by
  refine ⟨?_,curve_base_population hL n c r p.uStar heps hRep hZero⟩
  exact ParametrizedSolutionComponents.logistic_of_local_curve p hL hp hm hm1 hg1 hbeta hS c (fun z => amplitude hL n z.val) heps hdelta hc
    ((continuous_amplitude hL n).comp continuous_subtype_val) hsol
    (curve_amplitude hL n hn c r p.uStar hRep hOrth) U hU hnegative hexhaust

/-- Actual logistic selected-image deduction with the physical Fourier coordinate.
Curve existence, expansion, orthogonality and chart exhaustion remain explicit. -/
theorem logistic_unbounded_of_fourier_curve (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (hp : p.LogisticAdmissible)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ p.alpha+2) (hg1 : p.gamma ≤ 1+p.alpha) (hbeta : 0 ≤ beta)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ logisticSolutionSet p hL beta)
    (c : ℝ → (AmbientClosure.admissibleSet (profileCLM hL) univ)) (r : ℝ → Space L hL) (n : ℕ) (hn : 0 < n) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps))
    (hsol : ∀ t ∈ Ioo (-eps) eps, t ≠ 0 → (c t : ℝ × Space L hL) ∈ S)
    (hRep : ∀ t ∈ Ioo (-eps) eps, ∀ x : Icc (0 : ℝ) L,
      profileCLM hL (c t).val.2 x = p.uStar + t * neumannMode L n x + profileCLM hL (r t) x)
    (hOrth : ∀ t ∈ Ioo (-eps) eps,
      (∫ x : Icc (0 : ℝ) L, profileCLM hL (r t) x * neumannMode L n x ∂SignalWeakSource.intervalVolume L) = 0)
    (U : Set (AmbientClosure.admissibleSet (profileCLM hL) univ)) (hU : IsOpen U)
    (hnegative : ∀ t ∈ Ioo (-eps) 0, c t ∈ U)
    (hexhaust : ∀ x ∈ parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) univ) → ℝ × Space L hL) ⁻¹' S)) (c 0),
      x ∈ U → ∃ t ∈ Ioo (-eps) eps, c t = x)
    (hNC : ¬ IsCompact (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta))) :
    (∀ M : ℝ, ∃ z ∈ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta), M < z.1) ∧
      sSup ((fun z : ℝ × Space L hL => (z.1 : EReal)) '' (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) univ) (c '' Ioo (-eps) 0) (c 0) (c delta))) = ⊤ := by
  exact ParametrizedSolutionComponents.logistic_unbounded_of_local_curve p hL hp hm hm1 hg1 hbeta hS c (fun z => amplitude hL n z.val) heps hdelta hc
    ((continuous_amplitude hL n).comp continuous_subtype_val) hsol
    (curve_amplitude hL n hn c r p.uStar hRep hOrth) U hU hnegative hexhaust hNC

/-- Actual minimal selected-image deduction with the physical Fourier coordinate.
Curve existence, expansion, orthogonality and chart exhaustion remain explicit. -/
theorem minimal_of_fourier_curve (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (halpha : 0 ≤ p.alpha)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta)
    (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hnu : 0 ≤ p.nu)
    (hgamma : 0 ≤ p.gamma) (hg1 : p.gamma ≤ 1) (heq : p.SignalEquilibrium)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ minimalSolutionSet p hL beta)
    (c : ℝ → (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))) (r : ℝ → Space L hL) (n : ℕ) (hn : 0 < n) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps))
    (hsol : ∀ t ∈ Ioo (-eps) eps, t ≠ 0 → (c t : ℝ × Space L hL) ∈ S)
    (hRep : ∀ t ∈ Ioo (-eps) eps, ∀ x : Icc (0 : ℝ) L,
      profileCLM hL (c t).val.2 x = p.uStar + t * neumannMode L n x + profileCLM hL (r t) x)
    (hOrth : ∀ t ∈ Ioo (-eps) eps,
      (∫ x : Icc (0 : ℝ) L, profileCLM hL (r t) x * neumannMode L n x ∂SignalWeakSource.intervalVolume L) = 0)
    (hZero : r 0 = 0)
    (U : Set (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))) (hU : IsOpen U)
    (hnegative : ∀ t ∈ Ioo (-eps) 0, c t ∈ U)
    (hexhaust : ∀ x ∈ parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × Space L hL) ⁻¹' S)) (c 0),
      x ∈ U → ∃ t ∈ Ioo (-eps) eps, c t = x) :
    (IsClosed (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta)) ∧
    IsConnected (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta)) ∧
    (c 0 : ℝ × (Space L hL)) ∈ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta) ∧
    (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × (Space L hL)) '' (c '' Ico 0 eps)) ⊆ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta) ∧
    selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta) ⊆ (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) ∧
    selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta) ⊆ closure S ∧
    ∀ X : ℝ, IsCompact (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta) ∩ {z | z.1 ≤ X})) ∧ (c 0).val.2 = WeakH2PhaseSpace.const hL p.uStar := by
  refine ⟨?_,curve_base_population hL n c r p.uStar heps hRep hZero⟩
  exact ParametrizedSolutionComponents.minimal_of_local_curve p hL halpha hm hm1 hbeta hu hmu hnu hgamma hg1 heq hS c (fun z => amplitude hL n z.val) heps hdelta hc
    ((continuous_amplitude hL n).comp continuous_subtype_val) hsol
    (curve_amplitude hL n hn c r p.uStar hRep hOrth) U hU hnegative hexhaust

/-- Actual minimal selected-image deduction with the physical Fourier coordinate.
Curve existence, expansion, orthogonality and chart exhaustion remain explicit. -/
theorem minimal_unbounded_of_fourier_curve (p : PhysicalParams) {L beta : ℝ} (hL : 0 < L) (halpha : 0 ≤ p.alpha)
    (hm : 1 ≤ p.m) (hm1 : p.m ≤ 2) (hbeta : 0 ≤ beta)
    (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hnu : 0 ≤ p.nu)
    (hgamma : 0 ≤ p.gamma) (hg1 : p.gamma ≤ 1) (heq : p.SignalEquilibrium)
    {S : Set (ℝ × Space L hL)} (hS : S ⊆ minimalSolutionSet p hL beta)
    (c : ℝ → (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))) (r : ℝ → Space L hL) (n : ℕ) (hn : 0 < n) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : delta ∈ Ioo 0 eps)
    (hc : ContinuousOn c (Ico 0 eps))
    (hsol : ∀ t ∈ Ioo (-eps) eps, t ≠ 0 → (c t : ℝ × Space L hL) ∈ S)
    (hRep : ∀ t ∈ Ioo (-eps) eps, ∀ x : Icc (0 : ℝ) L,
      profileCLM hL (c t).val.2 x = p.uStar + t * neumannMode L n x + profileCLM hL (r t) x)
    (hOrth : ∀ t ∈ Ioo (-eps) eps,
      (∫ x : Icc (0 : ℝ) L, profileCLM hL (r t) x * neumannMode L n x ∂SignalWeakSource.intervalVolume L) = 0)
    (U : Set (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar))) (hU : IsOpen U)
    (hnegative : ∀ t ∈ Ioo (-eps) 0, c t ∈ U)
    (hexhaust : ∀ x ∈ parentComponent
      (closure (((↑) : (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) → ℝ × Space L hL) ⁻¹' S)) (c 0),
      x ∈ U → ∃ t ∈ Ioo (-eps) eps, c t = x)
    (hNC : ¬ IsCompact (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta))) :
    (∀ M : ℝ, ∃ z ∈ selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta), M < z.1) ∧
      sSup ((fun z : ℝ × Space L hL => (z.1 : EReal)) '' (selectedImage S (AmbientClosure.admissibleSet (profileCLM hL) (fixedMeanSet hL p.uStar)) (c '' Ioo (-eps) 0) (c 0) (c delta))) = ⊤ := by
  exact ParametrizedSolutionComponents.minimal_unbounded_of_local_curve p hL halpha hm hm1 hbeta hu hmu hnu hgamma hg1 heq hS c (fun z => amplitude hL n z.val) heps hdelta hc
    ((continuous_amplitude hL n).comp continuous_subtype_val) hsol
    (curve_amplitude hL n hn c r p.uStar hRep hOrth) U hU hnegative hexhaust hNC

end
end ChemotaxisBifurcation.FourierAmplitude
