module
public import ChemotaxisBifurcation.SignalResponseJet
public import ChemotaxisBifurcation.FourierComplement
public import Mathlib.Analysis.Normed.Operator.Asymptotics

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.CurvedSignalResponse
open Real Set Filter Topology MeasureTheory CosineCoefficients Asymptotics WeakH2PhaseSpace
noncomputable section

/-- Actual elliptic solutions with linearly small population perturbations have
negligible cubic modal residual. No projected balance or signal jet is assumed. -/
theorem actual_residual_cubic_negligible (p : PhysicalParams) {L : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hsig : p.SignalEquilibrium)
    (U V dV : ℝ → ℝ → ℝ) (B : ℝ) (hB : 0 < B) (k : ℕ)
    (hbound : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ Icc 0 L, |U t x| ≤ B*|t|)
    (hsol : ∀ᶠ t in 𝓝 (0 : ℝ), ContinuousOn (U t) (Icc 0 L) ∧
      NeumannW21 L (V t) (dV t) ∧ ∀ x ∈ Ioo 0 L,
      deriv (dV t) x-p.mu*(p.vStar+V t x)+p.nu*(p.uStar+U t x)^p.gamma=0) :
    (fun t => SignalModalResidual.modalResidual p L (U t) (V t) k)
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
  obtain ⟨C,hC,hrem⟩ := SignalModalResidual.modalResidual_quartic p hu hmu
  have hden : 0 < p.mu+(k*Real.pi/L)^2 := by positivity
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < p.uStar/(2*B) :=
    (continuous_abs.tendsto (0 : ℝ)).eventually (Iio_mem_nhds (by simpa using (show 0 < p.uStar/(2*B) by positivity)))
  have hO : (fun t => SignalModalResidual.modalResidual p L (U t) (V t) k)
      =O[𝓝 (0 : ℝ)] (fun t : ℝ => t^4) := by
    apply IsBigO.of_bound (2*C*B^4/(p.mu+(k*Real.pi/L)^2))
    filter_upwards [hsmall,hbound,hsol] with t ht hb hs
    have hN : B*|t| ≤ p.uStar/2 := by
      have hh := (lt_div_iff₀ (show 0 < 2*B by positivity)).mp ht
      nlinarith
    have heq : ∀ x ∈ Ioo 0 L, deriv (dV t) x-p.mu*V t x+
        (p.nu*(p.uStar+U t x)^p.gamma-p.nu*p.uStar^p.gamma)=0 := by
      intro x hx
      unfold PhysicalParams.SignalEquilibrium at hsig
      linarith [hs.2.2 x hx]
    have hh := hrem L (B*|t|) (U t) (V t) (dV t) hL hN hb hs.1 hs.2.1 heq
    simp only [Real.norm_eq_abs,abs_pow]
    by_cases hk : k=0
    · subst k
      have h := hh.1
      norm_num only [Nat.cast_zero,zero_mul,zero_div,zero_pow,add_zero]
      calc |SignalModalResidual.modalResidual p L (U t) (V t) 0| ≤ C*(B*|t|)^4/p.mu := h
        _ = C*B^4/p.mu*|t|^4 := by ring
        _ ≤ 2*(C*B^4/p.mu*|t|^4) := by
          have hp : 0 ≤ C*B^4/p.mu*|t|^4 := by positivity
          linarith
        _ = _ := by ring
    · calc |SignalModalResidual.modalResidual p L (U t) (V t) k| ≤
          2*(C*(B*|t|)^4)/(p.mu+(k*Real.pi/L)^2) := hh.2 k hk
        _ = _ := by ring
  exact hO.trans_isLittleO (isLittleO_pow_pow (by norm_num : 3 < 4))

/-- Cubic Peano jets in the continuous-profile algebra propagate through the
square and cube; this concerns genuine families with a norm-small remainder. -/
theorem profile_power_jets {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (a b c : C(K,ℝ)) (f : ℝ → C(K,ℝ))
    (he : (fun t => f t - (t • a + t^2 • b + t^3 • c))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3)) :
    ((fun t => (f t)^2 - (t^2 • a^2 + t^3 • (2 • (a*b))))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3)) ∧
    ((fun t => (f t)^3 - t^3 • a^3)
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3)) := by
  let P := fun t : ℝ => t • a + t^2 • b + t^3 • c
  have hP : P =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) :=
    (show ContinuousAt P 0 by dsimp [P]; fun_prop).tendsto.isBigO_one ℝ
  have ht3 : (fun t : ℝ => t^3) =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) :=
    (show ContinuousAt (fun t : ℝ => t^3) 0 by fun_prop).tendsto.isBigO_one ℝ
  have hf : f =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
    have hh := (he.isBigO.trans ht3).add hP
    convert hh using 1
    funext t
    dsimp [P]
    abel
  have h2 : (fun t => (f t)^2 - (P t)^2) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
    have hh := he.mul_isBigO (hf.add hP)
    convert hh using 1
    · funext t
      dsimp [P]
      ring
    · funext t
      simp
  have h3 : (fun t => (f t)^3 - (P t)^3) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
    have hb1 : (fun t => (f t)^2) =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by simpa using hf.pow 2
    have hb2 : (fun t => f t * P t) =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by simpa using hf.mul hP
    have hb3 : (fun t => (P t)^2) =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by simpa using hP.pow 2
    have hb' := (hb1.add hb2).add hb3
    have hh := he.mul_isBigO hb'
    convert hh using 1
    · funext t
      dsimp [P]
      ring
    · funext t
      simp
  let Q2 := fun t : ℝ => b^2 + 2 • (a*c) + t • (2 • (b*c)) + t^2 • c^2
  have hQ2 : Q2 =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) :=
    (show ContinuousAt Q2 0 by dsimp [Q2]; fun_prop).tendsto.isBigO_one ℝ
  have hp2 : (fun t => (P t)^2 - (t^2 • a^2 + t^3 • (2 • (a*b))))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
    have hh := (isLittleO_pow_pow (by norm_num : 3 < 4)).smul_isBigO hQ2
    convert hh using 1
    · funext t
      ext x
      simp only [P,Q2,ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,
        ContinuousMap.mul_apply,ContinuousMap.pow_apply,smul_eq_mul]
      ring
    · funext t
      simp
  let q := fun t : ℝ => a + t • b + t^2 • c
  let Q3 := fun t : ℝ => (b+t • c)*((q t)^2+q t*a+a^2)
  have hQ3 : Q3 =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) :=
    (show ContinuousAt Q3 0 by dsimp [Q3,q]; fun_prop).tendsto.isBigO_one ℝ
  have hp3 : (fun t => (P t)^3 - t^3 • a^3)
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
    have hh := (isLittleO_pow_pow (by norm_num : 3 < 4)).smul_isBigO hQ3
    convert hh using 1
    · funext t
      ext x
      simp only [P,Q3,q,ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,
        ContinuousMap.mul_apply,ContinuousMap.pow_apply,smul_eq_mul]
      ring
    · funext t
      simp
  constructor
  · convert h2.add hp2 using 1
    funext t
    abel
  · convert h3.add hp3 using 1
    funext t
    abel

/-- The normalized interval projection on continuous profiles. -/
def profileProjection {L : ℝ} (_hL : 0 < L) (n : ℕ) : C(Icc (0 : ℝ) L,ℝ) →L[ℝ] ℝ where
  toFun f := 2/L * ∫ x, f x * neumannMode L n x ∂SignalWeakSource.intervalVolume L
  map_add' f g := by
    have hw : Continuous (fun x : Icc (0 : ℝ) L => neumannMode L n x) := by
      unfold neumannMode; fun_prop
    have hi (f : C(Icc (0 : ℝ) L,ℝ)) : Integrable (fun x => f x * neumannMode L n x) (SignalWeakSource.intervalVolume L) :=
      (f.continuous.mul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp only [ContinuousMap.add_apply,add_mul]
    rw [integral_add (hi f) (hi g)]
    ring
  map_smul' a f := by
    simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul,RingHom.id_apply]
    ring
  cont := by
    let w : C(Icc (0 : ℝ) L,ℝ) := ⟨fun x => neumannMode L n x,by unfold neumannMode; fun_prop⟩
    let mu := SignalWeakSource.intervalVolume L
    let T := ContinuousMap.toLp (1 : ENNReal) mu ℝ (E := ℝ)
    have hF : Continuous (fun f : C(Icc (0 : ℝ) L,ℝ) => f*w) := continuous_id.mul continuous_const
    have h := (MeasureTheory.continuous_integral (μ := mu)).comp (T.continuous.comp hF)
    have he : (fun f : C(Icc (0 : ℝ) L,ℝ) => ∫ x, T (f*w) x ∂mu) =
        fun f => ∫ x, f x * neumannMode L n x ∂mu := by
      funext f
      exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (1 : ENNReal)) mu (f*w))
    change Continuous (fun f : C(Icc (0 : ℝ) L,ℝ) => ∫ x, T (f*w) x ∂mu) at h
    rw [he] at h
    exact continuous_const.mul h

/-- Projection of a genuine profile family jet, including quadratic and cubic
products. Integrability and continuity are internal to the profile functional. -/
theorem projected_source_jet {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (P : C(K,ℝ) →L[ℝ] ℝ) (a b c : C(K,ℝ)) (f : ℝ → C(K,ℝ)) (C1 C2 C3 : ℝ)
    (he : (fun t => f t - (t • a + t^2 • b + t^3 • c))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3)) :
    (fun t => C1*P (f t)+C2*P ((f t)^2)+C3*P ((f t)^3) -
      (t*(C1*P a)+t^2*(C1*P b+C2*P (a^2))+
        t^3*(C1*P c+2*C2*P (a*b)+C3*P (a^3))))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
  obtain ⟨h2,h3⟩ := profile_power_jets a b c f he
  have h1' := (P.isBigO_comp _ (𝓝 (0 : ℝ))).trans_isLittleO he
  have h2' := (P.isBigO_comp _ (𝓝 (0 : ℝ))).trans_isLittleO h2
  have h3' := (P.isBigO_comp _ (𝓝 (0 : ℝ))).trans_isLittleO h3
  have hh := ((h1'.const_mul_left C1).add (h2'.const_mul_left C2)).add (h3'.const_mul_left C3)
  convert hh using 1
  funext t
  simp only [map_sub,map_add,map_smul,smul_eq_mul,map_nsmul]
  ring

/-- Exact agreement of the continuous-profile functional with the literal
interval projection of any representative. -/
theorem profileProjection_eq {L : ℝ} (hL : 0 < L) (n : ℕ)
    (f : C(Icc (0 : ℝ) L,ℝ)) (u : ℝ → ℝ)
    (hrep : ∀ x : Icc (0 : ℝ) L, u x = f x) :
    profileProjection hL n f = actualCriticalProjection L n u := by
  change 2/L * (∫ x, f x * neumannMode L n x ∂SignalWeakSource.intervalVolume L) = _
  unfold actualCriticalProjection
  congr 1
  calc _ = ∫ x : Icc (0 : ℝ) L, u x * neumannMode L n x ∂SignalWeakSource.intervalVolume L := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by dsimp; rw [hrep x])
    _ = _ := SignalWeakSource.integral_intervalVolume hL.le (fun x => u x * neumannMode L n x)

/-- A genuine cubic norm-family expansion supplies the linear smallness used
by the actual signal Taylor bound. -/
theorem family_isBigO_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c : E) (f : ℝ → E)
    (he : (fun t => f t - (t • a+t^2 • b+t^3 • c))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3)) :
    f =O[𝓝 (0 : ℝ)] (fun t : ℝ => t) := by
  have hq : (fun t : ℝ => a+t • b+t^2 • c) =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) :=
    (show ContinuousAt (fun t : ℝ => a+t • b+t^2 • c) 0 by fun_prop).tendsto.isBigO_one ℝ
  have hp : (fun t : ℝ => t • a+t^2 • b+t^3 • c) =O[𝓝 (0 : ℝ)] (fun t : ℝ => t) := by
    have hh := (isBigO_refl (fun t : ℝ => t) (𝓝 0)).smul hq
    convert hh using 1
    · funext t
      simp only [smul_add,smul_smul]
      module
    · funext t
      simp
  have hh := (he.isBigO.trans (isLittleO_pow_id (by norm_num : 1 < 3)).isBigO).add hp
  convert hh using 1
  funext t
  abel

theorem profileProjection_eq_cosineCoeff {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (f : C(Icc (0 : ℝ) L,ℝ)) (u : ℝ → ℝ)
    (hrep : ∀ x : Icc (0 : ℝ) L, u x = f x) :
    profileProjection hL n f = cosineCoeff L u n := by
  rw [profileProjection_eq hL n f u hrep]
  simp only [cosineCoeff,ite_eq_right hn.ne',actualCriticalProjection]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  have ha : waveNumber L n * x = (n : ℝ)*Real.pi*x/L := by unfold waveNumber; ring
  simp only [neumannMode,ha]

/-- Actual nonlinear elliptic solutions inherit the cubic Peano response to a
curved continuous-profile family with a genuine norm remainder. -/
theorem actual_profile_response_jet (p : PhysicalParams) {L : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hsig : p.SignalEquilibrium)
    (n : ℕ) (hn : 0 < n) (a b c : C(Icc (0 : ℝ) L,ℝ))
    (f : ℝ → C(Icc (0 : ℝ) L,ℝ)) (U V dV : ℝ → ℝ → ℝ)
    (hrep : ∀ t (x : Icc (0 : ℝ) L), U t x = f t x)
    (he : (fun t => f t - (t • a+t^2 • b+t^3 • c))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3))
    (hsol : ∀ᶠ t in 𝓝 (0 : ℝ), ContinuousOn (U t) (Icc 0 L) ∧
      NeumannW21 L (V t) (dV t) ∧ ∀ x ∈ Ioo 0 L,
      deriv (dV t) x-p.mu*(p.vStar+V t x)+p.nu*(p.uStar+U t x)^p.gamma=0) :
    let P := profileProjection hL n
    let C1 := (rawTaylorData p 0).Cprime
    let C2 := (rawTaylorData p 0).Csecond
    let C3 := (rawTaylorData p 0).Cthird
    (fun t => cosineCoeff L (V t) n -
      (t*(C1*P a)+t^2*(C1*P b+C2*P (a^2))+
        t^3*(C1*P c+2*C2*P (a*b)+C3*P (a^3))) / (p.mu+(n*Real.pi/L)^2))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
  obtain ⟨B,hB,hbound⟩ := (family_isBigO_linear a b c f he).exists_pos
  have hb : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ Icc 0 L, |U t x| ≤ B*|t| := by
    filter_upwards [hbound.bound] with t ht
    intro x hx
    have hr := hrep t ⟨x,hx⟩
    change U t x = f t ⟨x,hx⟩ at hr
    rw [hr]
    exact ((f t).norm_coe_le_norm ⟨x,hx⟩).trans (by simpa only [Real.norm_eq_abs] using ht)
  have hR := actual_residual_cubic_negligible p hL hu hmu hsig U V dV B hB n hb hsol
  let P := profileProjection hL n
  have hS := projected_source_jet P a b c f (rawTaylorData p 0).Cprime
    (rawTaylorData p 0).Csecond (rawTaylorData p 0).Cthird he
  have hP1 (t : ℝ) : P (f t) = cosineCoeff L (U t) n :=
    profileProjection_eq_cosineCoeff hL n hn (f t) (U t) (hrep t)
  have hP2 (t : ℝ) : P ((f t)^2) = cosineCoeff L (fun x => U t x^2) n :=
    profileProjection_eq_cosineCoeff hL n hn ((f t)^2) _ (fun x => by simp only [ContinuousMap.pow_apply,hrep])
  have hP3 (t : ℝ) : P ((f t)^3) = cosineCoeff L (fun x => U t x^3) n :=
    profileProjection_eq_cosineCoeff hL n hn ((f t)^3) _ (fun x => by simp only [ContinuousMap.pow_apply,hrep])
  have hh := hR.add (hS.const_mul_left (p.mu+(n*Real.pi/L)^2)⁻¹)
  convert hh using 1
  funext t
  unfold SignalModalResidual.modalResidual
  rw [hP1,hP2,hP3]
  ring

/-- The square of the actual cosine has no positive critical-mode projection. -/
theorem profile_cosine_square_zero {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n) :
    profileProjection hL n ((profileCLM hL (WeakH2CosineMode.mode hL n))^2) = 0 := by
  rw [profileProjection_eq hL n _ (quadraticForcingProfile (1/2) (1/2) L n) ?_]
  · exact quadraticForcing_other_mode_projection_zero (1/2) (1/2) L n n hL hn (by omega)
  · intro x
    simp only [ContinuousMap.pow_apply,WeakH2CosineMode.profile_mode,quadraticForcingProfile]
    have hw : waveNumber L (2*n) * (x : ℝ) = 2*(waveNumber L n * (x : ℝ)) := by
      unfold waveNumber
      push_cast
      ring
    unfold neumannMode
    rw [hw,Real.cos_two_mul]
    ring

/-- The curved actual signal family has the physical critical cubic response.
The population expansion is a phase-norm Peano jet, not an exact polynomial
curve. Actual elliptic solutions are supplied; no projected balance, signal jet,
center manifold, or dynamical invariance equation is assumed or constructed. -/
theorem actual_phase_cubic_response (p : PhysicalParams) {L : ℝ}
    (hL : 0 < L) (hu : 0 < p.uStar) (hmu : 0 < p.mu) (hsig : p.SignalEquilibrium)
    (n : ℕ) (hn : 0 < n) (jet : QuadraticJetData)
    (H3 : Space L hL) (hH3 : FourierAmplitude.coefficient hL n H3 = 0)
    (J : ℝ → Space L hL) (U V dV : ℝ → ℝ → ℝ)
    (hrep : ∀ t (x : Icc (0 : ℝ) L), U t x = profileCLM hL (J t) x)
    (he : (fun t => J t - (t • WeakH2CosineMode.mode hL n +
        t^2 • (jet.a0 • WeakH2PhaseSpace.const hL 1 + jet.a2 • WeakH2CosineMode.mode hL (2*n)) +
        t^3 • H3)) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3))
    (hsol : ∀ᶠ t in 𝓝 (0 : ℝ), ContinuousOn (U t) (Icc 0 L) ∧
      NeumannW21 L (V t) (dV t) ∧ ∀ x ∈ Ioo 0 L,
      deriv (dV t) x-p.mu*(p.vStar+V t x)+p.nu*(p.uStar+U t x)^p.gamma=0) :
    (fun t => cosineCoeff L (V t) n -
      (t*signalMode1 p ((n*Real.pi/L)^2) + t^3*cubicH p ((n*Real.pi/L)^2) jet))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
  let e := WeakH2CosineMode.mode hL n
  let H2 := jet.a0 • WeakH2PhaseSpace.const hL 1 + jet.a2 • WeakH2CosineMode.mode hL (2*n)
  let a := profileCLM hL e
  let b := profileCLM hL H2
  let c := profileCLM hL H3
  let f := fun t => profileCLM hL (J t)
  let P := profileProjection hL n
  have he' : (fun t => f t - (t • a+t^2 • b+t^3 • c))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
    have hh := ((profileCLM hL).isBigO_comp _ (𝓝 (0 : ℝ))).trans_isLittleO he
    simpa only [f,a,b,c,e,H2,map_sub,map_add,map_smul] using hh
  have ha : P a = 1 := WeakH2CosineMode.coefficient_mode hL n hn
  have hc : P c = 0 := hH3
  have hbRep (x : Icc (0 : ℝ) L) : quadraticJetProfile jet.a0 jet.a2 L n x = b x := by
    dsimp [b,H2,quadraticJetProfile]
    simp only [map_add,map_smul,ContinuousMap.add_apply,ContinuousMap.smul_apply,
      profileCLM_const,ContinuousMap.const_apply,WeakH2CosineMode.profile_mode,smul_eq_mul,mul_one]
  have hb : P b = 0 := by
    rw [profileProjection_eq hL n b (quadraticJetProfile jet.a0 jet.a2 L n) hbRep]
    exact quadraticForcing_other_mode_projection_zero jet.a0 jet.a2 L n n hL hn (by omega)
  have ha2 : P (a^2) = 0 := profile_cosine_square_zero hL n hn
  have hab : P (a*b) = jet.a0+jet.a2/2 := by
    rw [profileProjection_eq hL n (a*b) (fun x => neumannMode L n x * quadraticJetProfile jet.a0 jet.a2 L n x) ?_]
    · exact actual_phi_quadraticJet_projection L n jet.a0 jet.a2 hL hn
    · intro x
      simp only [ContinuousMap.mul_apply,hbRep]
      dsimp only [a,e]
      rw [WeakH2CosineMode.profile_mode]
  have ha3 : P (a^3) = 3/4 := by
    rw [profileProjection_eq hL n (a^3) (fun x => neumannMode L n x^3) ?_]
    · exact actual_phi_cube_projection L n hL hn
    · intro x
      simp only [ContinuousMap.pow_apply]
      dsimp only [a,e]
      rw [WeakH2CosineMode.profile_mode]
  have hh := actual_profile_response_jet p hL hu hmu hsig n hn a b c f U V dV hrep he' hsol
  change (fun t => cosineCoeff L (V t) n -
      (t*((rawTaylorData p 0).Cprime*P a)+t^2*((rawTaylorData p 0).Cprime*P b+(rawTaylorData p 0).Csecond*P (a^2))+
        t^3*((rawTaylorData p 0).Cprime*P c+2*(rawTaylorData p 0).Csecond*P (a*b)+(rawTaylorData p 0).Cthird*P (a^3))) /
          (p.mu+(n*Real.pi/L)^2)) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) at hh
  rw [ha,hb,hc,ha2,hab,ha3,Cprime_eq_scaled p hu hsig,
    Csecond_eq_scaled p hu hsig,Cthird_eq_scaled p hu hsig] at hh
  convert hh using 1
  funext t
  unfold signalMode1 cubicH signalMode2 signalMode3
  have hd : p.mu + (n*Real.pi/L)^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

end
end ChemotaxisBifurcation.CurvedSignalResponse
