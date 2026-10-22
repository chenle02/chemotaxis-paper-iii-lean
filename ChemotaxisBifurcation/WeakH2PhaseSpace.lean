module
public import ChemotaxisBifurcation.WeakDerivative1D
public import ChemotaxisBifurcation.WeakH2Embedding
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.WeakH2PhaseSpace
open Real Set MeasureTheory Filter Topology WeakDerivative1D
noncomputable section

abbrev intervalMeasure (L : ℝ) := volume.restrict (Ioo (0 : ℝ) L)
abbrev Jet (L : ℝ) := Lp ℝ 2 (intervalMeasure L) ×
  (Lp ℝ 2 (intervalMeasure L) × Lp ℝ 2 (intervalMeasure L))

private theorem mul_integral_congr {L : ℝ} (hL : 0 < L) {f g : ℝ → ℝ}
    (h : f =ᵐ[intervalMeasure L] g) (phi : ℝ → ℝ) :
    (∫ x in (0 : ℝ)..L, f x*phi x) = ∫ x in (0 : ℝ)..L, g x*phi x := by
  apply integral_congr_ae_Ioo hL.le
  have hh := (ae_restrict_iff' measurableSet_Ioo).mp h
  filter_upwards [hh] with x hx hi
  rw [hx hi]

theorem H2_congr {L : ℝ} (hL : 0 < L) {u du ddu v dv ddv : ℝ → ℝ}
    (h : H2 L u du ddu) (h0 : u =ᵐ[intervalMeasure L] v)
    (h1 : du =ᵐ[intervalMeasure L] dv) (h2 : ddu =ᵐ[intervalMeasure L] ddv) : H2 L v dv ddv where
  memLp := (memLp_congr_ae h0).mp h.memLp
  memLp_deriv := (memLp_congr_ae h1).mp h.memLp_deriv
  memLp_deriv2 := (memLp_congr_ae h2).mp h.memLp_deriv2
  weak_deriv := by
    intro phi hp
    rw [← mul_integral_congr hL h0 (deriv phi),h.weak_deriv phi hp,mul_integral_congr hL h1 phi]
  weak_deriv2 := by
    intro phi hp
    rw [← mul_integral_congr hL h1 (deriv phi),h.weak_deriv2 phi hp,mul_integral_congr hL h2 phi]

private theorem integral_add_mul {L : ℝ} (hL : 0 < L) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (intervalMeasure L)) (hg : MemLp g 2 (intervalMeasure L))
    {phi : ℝ → ℝ} (hp : Continuous phi) :
    (∫ x in (0 : ℝ)..L, (f x+g x)*phi x) =
      (∫ x in (0 : ℝ)..L, f x*phi x)+(∫ x in (0 : ℝ)..L, g x*phi x) := by
  have hfi : IntervalIntegrable (fun x => f x*phi x) volume 0 L :=
    (intervalIntegrable_of_memLp hL hf).mul_continuousOn hp.continuousOn
  have hgi : IntervalIntegrable (fun x => g x*phi x) volume 0 L :=
    (intervalIntegrable_of_memLp hL hg).mul_continuousOn hp.continuousOn
  simp only [add_mul]
  exact intervalIntegral.integral_add hfi hgi

theorem H2_add {L : ℝ} (hL : 0 < L) {u du ddu v dv ddv : ℝ → ℝ}
    (h : H2 L u du ddu) (k : H2 L v dv ddv) :
    H2 L (fun x => u x+v x) (fun x => du x+dv x) (fun x => ddu x+ddv x) where
  memLp := h.memLp.add k.memLp
  memLp_deriv := h.memLp_deriv.add k.memLp_deriv
  memLp_deriv2 := h.memLp_deriv2.add k.memLp_deriv2
  weak_deriv := by
    intro phi hp
    rw [integral_add_mul hL h.memLp k.memLp hp.continuous_deriv,
      integral_add_mul hL h.memLp_deriv k.memLp_deriv hp.continuous,
      h.weak_deriv phi hp,k.weak_deriv phi hp]
    ring
  weak_deriv2 := by
    intro phi hp
    rw [integral_add_mul hL h.memLp_deriv k.memLp_deriv hp.continuous_deriv,
      integral_add_mul hL h.memLp_deriv2 k.memLp_deriv2 hp.continuous,
      h.weak_deriv2 phi hp,k.weak_deriv2 phi hp]
    ring

theorem H2_smul {L : ℝ} {u du ddu : ℝ → ℝ} (h : H2 L u du ddu) (c : ℝ) :
    H2 L (fun x => c*u x) (fun x => c*du x) (fun x => c*ddu x) where
  memLp := h.memLp.const_mul c
  memLp_deriv := h.memLp_deriv.const_mul c
  memLp_deriv2 := h.memLp_deriv2.const_mul c
  weak_deriv := by
    intro phi hp
    simp only [mul_assoc,intervalIntegral.integral_const_mul,h.weak_deriv phi hp]
    ring
  weak_deriv2 := by
    intro phi hp
    simp only [mul_assoc,intervalIntegral.integral_const_mul,h.weak_deriv2 phi hp]
    ring

theorem trace_congr {L : ℝ} {u v : ℝ → ℝ}
    (h : NeumannTrace L u) (hae : u =ᵐ[intervalMeasure L] v) : NeumannTrace L v := by
  obtain ⟨U,hU,hu,h0,h1⟩ := h
  refine ⟨U,hU,?_,h0,h1⟩
  have hh := (ae_restrict_iff' measurableSet_Ioo).mp hae
  filter_upwards [hu,hh] with x hx hi hxi
  rw [← hi hxi]
  exact hx hxi

theorem trace_add {L : ℝ} {u v : ℝ → ℝ}
    (h : NeumannTrace L u) (k : NeumannTrace L v) : NeumannTrace L (fun x => u x+v x) := by
  obtain ⟨U,hU,hu,h0,h1⟩ := h
  obtain ⟨V,hV,hv,k0,k1⟩ := k
  refine ⟨fun x => U x+V x,hU.add hV,?_,by simp [h0,k0],by simp [h1,k1]⟩
  filter_upwards [hu,hv] with x hx hy hi
  rw [hx hi,hy hi]

theorem trace_smul {L : ℝ} {u : ℝ → ℝ} (h : NeumannTrace L u) (c : ℝ) :
    NeumannTrace L (fun x => c*u x) := by
  obtain ⟨U,hU,hu,h0,h1⟩ := h
  refine ⟨fun x => c*U x,continuousOn_const.mul hU,?_,by simp [h0],by simp [h1]⟩
  filter_upwards [hu] with x hx hi
  rw [hx hi]

/-- The genuine weak-H2 Neumann graph in the product of three actual L2
spaces. Its inherited norm is the maximum of the component L2 norms. -/
def phaseSpace (L : ℝ) (hL : 0 < L) : Submodule ℝ (Jet L) where
  carrier := {J | H2 L J.1 J.2.1 J.2.2 ∧ NeumannTrace L J.2.1}
  zero_mem' := by
    have hh : H2 L (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) := {
      memLp := memLp_const 0
      memLp_deriv := memLp_const 0
      memLp_deriv2 := memLp_const 0
      weak_deriv := by intros; simp
      weak_deriv2 := by intros; simp }
    have hn : NeumannTrace L (fun _ => (0 : ℝ)) :=
      ⟨fun _ => 0,continuousOn_const,Eventually.of_forall (fun _ _ => rfl),rfl,rfl⟩
    exact ⟨H2_congr hL hh (Lp.coeFn_zero _ _ _).symm (Lp.coeFn_zero _ _ _).symm
      (Lp.coeFn_zero _ _ _).symm,trace_congr hn (Lp.coeFn_zero _ _ _).symm⟩
  add_mem' := by
    intro J K hJ hK
    refine ⟨H2_congr hL (H2_add hL hJ.1 hK.1)
      (Lp.coeFn_add J.1 K.1).symm (Lp.coeFn_add J.2.1 K.2.1).symm
      (Lp.coeFn_add J.2.2 K.2.2).symm,?_⟩
    exact trace_congr (trace_add hJ.2 hK.2) (Lp.coeFn_add J.2.1 K.2.1).symm
  smul_mem' := by
    intro c J hJ
    refine ⟨H2_congr hL (H2_smul hJ.1 c)
      (Lp.coeFn_smul c J.1).symm (Lp.coeFn_smul c J.2.1).symm
      (Lp.coeFn_smul c J.2.2).symm,?_⟩
    exact trace_congr (trace_smul hJ.2 c) (Lp.coeFn_smul c J.2.1).symm

abbrev Space (L : ℝ) (hL : 0 < L) := phaseSpace L hL

/-- A canonical representative selected from the proved weak-H2 theorem. -/
def repFunction {L : ℝ} {hL : 0 < L} (J : Space L hL) : ℝ → ℝ :=
  Classical.choose (J.property.1.exists_neumannW21 hL J.property.2)

def repDerivative {L : ℝ} {hL : 0 < L} (J : Space L hL) : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec (J.property.1.exists_neumannW21 hL J.property.2))

theorem rep_properties {L : ℝ} {hL : 0 < L} (J : Space L hL) :
    CosineCoefficients.NeumannW21 L (repFunction J) (repDerivative J) ∧
      (∀ᵐ x, x ∈ Ioo 0 L → J.val.1 x = repFunction J x) ∧
      (∀ᵐ x, x ∈ Ioo 0 L → J.val.2.1 x = repDerivative J x) :=
  Classical.choose_spec (Classical.choose_spec (J.property.1.exists_neumannW21 hL J.property.2))

theorem rep_continuous {L : ℝ} {hL : 0 < L} (J : Space L hL) :
    ContinuousOn (repFunction J) (Icc 0 L) := by
  simpa only [uIcc_of_le hL.le] using (rep_properties J).1.ac.continuousOn

/-- The actual canonical continuous profile on the physical closed interval. -/
def profile {L : ℝ} {hL : 0 < L} (J : Space L hL) : C(Icc (0 : ℝ) L,ℝ) :=
  ⟨fun x => repFunction J x,continuousOn_iff_continuous_domRestrict.mp (rep_continuous J)⟩

theorem rep_ae {L : ℝ} {hL : 0 < L} (J : Space L hL) :
    (J.val.1 : ℝ → ℝ) =ᵐ[intervalMeasure L] repFunction J :=
  (ae_restrict_iff' measurableSet_Ioo).mpr (rep_properties J).2.1

theorem rep_derivative_ae {L : ℝ} {hL : 0 < L} (J : Space L hL) :
    (J.val.2.1 : ℝ → ℝ) =ᵐ[intervalMeasure L] repDerivative J :=
  (ae_restrict_iff' measurableSet_Ioo).mpr (rep_properties J).2.2

/-- The continuous profile agrees with every continuous representative of
its actual L2 value component, including endpoints by uniqueness. -/
theorem rep_eqOn_of_ae {L : ℝ} {hL : 0 < L} (J : Space L hL) {U : ℝ → ℝ}
    (hU : ContinuousOn U (Icc 0 L)) (hae : (J.val.1 : ℝ → ℝ) =ᵐ[intervalMeasure L] U) :
    EqOn (repFunction J) U (Icc 0 L) := by
  apply eqOn_of_ae_eq_continuousOn hL (rep_continuous J) hU
  exact (ae_restrict_iff' measurableSet_Ioo).mp ((rep_ae J).symm.trans hae)

theorem profile_add {L : ℝ} {hL : 0 < L} (J K : Space L hL) :
    profile (J+K) = profile J+profile K := by
  have ha : (((J+K).val.1) : ℝ → ℝ) =ᵐ[intervalMeasure L]
      (fun x => repFunction J x+repFunction K x) := by
    filter_upwards [Lp.coeFn_add J.val.1 K.val.1,rep_ae J,rep_ae K] with x hx hj hk
    change ((J.val.1+K.val.1) : Lp ℝ 2 (intervalMeasure L)) x = _
    simpa only [Pi.add_apply,hj,hk] using hx
  have he := rep_eqOn_of_ae (J+K) ((rep_continuous J).add (rep_continuous K)) ha
  apply ContinuousMap.ext
  intro x
  exact he x.property

theorem profile_smul {L : ℝ} {hL : 0 < L} (c : ℝ) (J : Space L hL) :
    profile (c • J) = c • profile J := by
  have ha : (((c • J).val.1) : ℝ → ℝ) =ᵐ[intervalMeasure L]
      (fun x => c*repFunction J x) := by
    filter_upwards [Lp.coeFn_smul c J.val.1,rep_ae J] with x hx hj
    change ((c • J.val.1) : Lp ℝ 2 (intervalMeasure L)) x = _
    simpa only [Pi.smul_apply,smul_eq_mul,hj] using hx
  have he := rep_eqOn_of_ae (c • J) (continuousOn_const.mul (rep_continuous J)) ha
  apply ContinuousMap.ext
  intro x
  exact he x.property

/-- The genuine linear realization of every weak-H2 Neumann jet in actual
continuous profiles. Continuity and injectivity are proved separately below. -/
def profileLinear {L : ℝ} (hL : 0 < L) : Space L hL →ₗ[ℝ] C(Icc (0 : ℝ) L,ℝ) where
  toFun := profile
  map_add' := profile_add
  map_smul' := profile_smul

/-- Every weak-H2 Neumann jet has a quantitative actual C0 norm bound. -/
theorem profile_norm_bound {L : ℝ} (hL : 0 < L) (J : Space L hL) :
    ‖profile J‖ ≤ (1/L^(1/(2 : ℝ))+L^(1/(2 : ℝ)))*‖J‖ := by
  have hC : 0 ≤ (1/L^(1/(2 : ℝ))+L^(1/(2 : ℝ)))*‖J‖ := by positivity
  apply (ContinuousMap.norm_le _ hC).mpr
  intro x
  have hh := WeakH2Embedding.representative_sup_le_jet_norm hL J.property.1
    (rep_properties J).1 (rep_properties J).2.1 (rep_properties J).2.2 x x.property
  change |repFunction J x| ≤ (1/L^(1/(2 : ℝ))+L^(1/(2 : ℝ)))*‖J.val‖
  simpa only [Lp.toLp_coeFn,Prod.mk.eta] using hh

/-- A proved continuous linear profile realization on ALL weak-H2 Neumann
jets, not an embedding premise on a chosen family of classical solutions. -/
def profileCLM {L : ℝ} (hL : 0 < L) : Space L hL →L[ℝ] C(Icc (0 : ℝ) L,ℝ) :=
  (profileLinear hL).mkContinuous (1/L^(1/(2 : ℝ))+L^(1/(2 : ℝ))) (profile_norm_bound hL)

/-- Equality of continuous profiles implies equality of all three L2 jet
components, by uniqueness of actual weak derivatives. -/
theorem profile_injective {L : ℝ} (hL : 0 < L) :
    Function.Injective (profile (hL := hL)) := by
  intro J K hJK
  have h0 : ∀ᵐ x, x ∈ Ioo 0 L → J.val.1 x = K.val.1 x := by
    filter_upwards [(rep_properties J).2.1,(rep_properties K).2.1] with x hj hk hx
    rw [hj hx,hk hx]
    exact ContinuousMap.congr_fun hJK ⟨x,Ioo_subset_Icc_self hx⟩
  have h1 := WeakH2Embedding.weak_deriv_unique_of_ae_eq hL
    (J.property.1.hasWeakDeriv hL) (K.property.1.hasWeakDeriv hL) h0
  have h2 := WeakH2Embedding.weak_deriv_unique_of_ae_eq hL
    (J.property.1.hasWeakDeriv2 hL) (K.property.1.hasWeakDeriv2 hL) h1
  apply Subtype.ext
  exact Prod.ext (Lp.ext ((ae_restrict_iff' measurableSet_Ioo).mpr h0))
    (Prod.ext (Lp.ext ((ae_restrict_iff' measurableSet_Ioo).mpr h1))
      (Lp.ext ((ae_restrict_iff' measurableSet_Ioo).mpr h2)))

theorem profileCLM_injective {L : ℝ} (hL : 0 < L) : Function.Injective (profileCLM hL) :=
  profile_injective hL

/-- The actual constant population jet in the weak-H2 Neumann phase space. -/
def const {L : ℝ} (hL : 0 < L) (c : ℝ) : Space L hL := by
  let hc : MemLp (fun _ : ℝ => c) 2 (intervalMeasure L) := memLp_const c
  let hz : MemLp (fun _ : ℝ => (0 : ℝ)) 2 (intervalMeasure L) := memLp_const 0
  let J : Jet L := (hc.toLp (fun _ => c),(hz.toLp (fun _ => 0),hz.toLp (fun _ => 0)))
  have hh : H2 L (fun _ => c) (fun _ => 0) (fun _ => 0) :=
    ClassicalSobolevDictionary.classical_H2 hL continuousOn_const continuousOn_const continuousOn_const
      (fun x _ => hasDerivAt_const x c) (fun x _ => hasDerivAt_const x 0)
  have hn : NeumannTrace L (fun _ => (0 : ℝ)) :=
    ⟨fun _ => 0,continuousOn_const,Eventually.of_forall (fun _ _ => rfl),rfl,rfl⟩
  exact ⟨J,H2_congr hL hh (MemLp.coeFn_toLp hc).symm (MemLp.coeFn_toLp hz).symm
    (MemLp.coeFn_toLp hz).symm,trace_congr hn (MemLp.coeFn_toLp hz).symm⟩

theorem const_value_ae {L : ℝ} (hL : 0 < L) (c : ℝ) :
    (((const hL c).val.1) : ℝ → ℝ) =ᵐ[intervalMeasure L] (fun _ => c) :=
  MemLp.coeFn_toLp (memLp_const c)

theorem profile_const {L : ℝ} (hL : 0 < L) (c : ℝ) :
    profile (const hL c) = ContinuousMap.const (Icc (0 : ℝ) L) c := by
  have he := rep_eqOn_of_ae (const hL c) continuousOn_const (const_value_ae hL c)
  apply ContinuousMap.ext
  intro x
  exact he x.property

theorem profileCLM_const {L : ℝ} (hL : 0 < L) (c : ℝ) :
    profileCLM hL (const hL c) = ContinuousMap.const (Icc (0 : ℝ) L) c := profile_const hL c

/-- Every actual weak-H2 Neumann triple defines a point of the normed phase
space. This is the ordinary weak-derivative identification, not a premise. -/
def of_H2 {L : ℝ} (hL : 0 < L) {u du ddu : ℝ → ℝ}
    (h : H2 L u du ddu) (hN : NeumannTrace L du) : Space L hL :=
  ⟨(h.memLp.toLp u,(h.memLp_deriv.toLp du,h.memLp_deriv2.toLp ddu)),
    H2_congr hL h (MemLp.coeFn_toLp h.memLp).symm (MemLp.coeFn_toLp h.memLp_deriv).symm
      (MemLp.coeFn_toLp h.memLp_deriv2).symm,
    trace_congr hN (MemLp.coeFn_toLp h.memLp_deriv).symm⟩

theorem of_H2_value_ae {L : ℝ} (hL : 0 < L) {u du ddu : ℝ → ℝ}
    (h : H2 L u du ddu) (hN : NeumannTrace L du) :
    (((of_H2 hL h hN).val.1) : ℝ → ℝ) =ᵐ[intervalMeasure L] u :=
  MemLp.coeFn_toLp h.memLp

theorem profile_of_H2 {L : ℝ} (hL : 0 < L) {u du ddu : ℝ → ℝ}
    (h : H2 L u du ddu) (hN : NeumannTrace L du) (hu : ContinuousOn u (Icc 0 L)) :
    ∀ x : Icc (0 : ℝ) L, profileCLM hL (of_H2 hL h hN) x = u x := by
  have he := rep_eqOn_of_ae (of_H2 hL h hN) hu (of_H2_value_ae hL h hN)
  intro x
  exact he x.property

/-- The inherited actual product-L2 norm and the standard weak-H2 sum norm
are equivalent with proved constants1 and3, on every point of the phase. -/
theorem norm_equivalence {L : ℝ} {hL : 0 < L} (J : Space L hL) :
    ‖J‖ ≤ ‖J.val.1‖+‖J.val.2.1‖+‖J.val.2.2‖ ∧
      ‖J.val.1‖+‖J.val.2.1‖+‖J.val.2.2‖ ≤ 3*‖J‖ := by
  change max ‖J.val.1‖ (max ‖J.val.2.1‖ ‖J.val.2.2‖) ≤ _ ∧
    _ ≤ 3*max ‖J.val.1‖ (max ‖J.val.2.1‖ ‖J.val.2.2‖)
  constructor
  · apply max_le
    · linarith [norm_nonneg J.val.2.1,norm_nonneg J.val.2.2]
    · apply max_le <;> linarith [norm_nonneg J.val.1,norm_nonneg J.val.2.1,norm_nonneg J.val.2.2]
  · linarith [le_max_left ‖J.val.1‖ (max ‖J.val.2.1‖ ‖J.val.2.2‖),
      (le_max_left ‖J.val.2.1‖ ‖J.val.2.2‖).trans (le_max_right ‖J.val.1‖ (max ‖J.val.2.1‖ ‖J.val.2.2‖)),
      (le_max_right ‖J.val.2.1‖ ‖J.val.2.2‖).trans (le_max_right ‖J.val.1‖ (max ‖J.val.2.1‖ ‖J.val.2.2‖))]

end
end ChemotaxisBifurcation.WeakH2PhaseSpace
