module
public import ChemotaxisBifurcation.PopulationModalResidual
public import ChemotaxisBifurcation.SignalLipschitz
public import ChemotaxisBifurcation.SignedEllipticEnergy

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.PopulationNormBridge
open Real Set MeasureTheory
noncomputable section

def signalSource (p : PhysicalParams) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  p.nu*(p.uStar+U x)^p.gamma-p.nu*p.uStar^p.gamma

/-- Actual signed signal response is C1-small whenever the population
perturbation is small; no signal norm or elliptic estimate is assumed. -/
theorem signal_response_C1_of_population_bound (p : PhysicalParams) (hu : 0 < p.uStar) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (L N : ℝ) (Ω : Set ℝ) (U V : ℝ → ℝ),
      0 < L → 0 < p.mu → IsOpen Ω → Icc 0 L ⊆ Ω →
      ContinuousOn U Ω → ContDiffOn ℝ 2 V Ω →
      0 ≤ N → N ≤ p.uStar/2 → (∀ x ∈ Icc 0 L, |U x| ≤ N) →
      deriv V 0 = 0 → deriv V L = 0 →
      (∀ x ∈ Ioo 0 L, deriv (deriv V) x - p.mu*V x + signalSource p U x = 0) →
      ∀ x ∈ Icc 0 L,
      |V x|+|deriv V x| ≤ (1/p.mu+2*L^2+2*L)*D*N := by
  obtain ⟨D,hD,hLip⟩ := signalSource_local_lipschitz p hu
  refine ⟨D,hD,?_⟩
  intro L N Ω U V hL hmu hΩ hsub hU hV hN hNu hUb hV0 hVL heq
  have hUc := hU.mono hsub
  have hbase : ∀ x ∈ Icc 0 L, 0 < p.uStar+U x := by
    intro x hx
    have h := (abs_le.mp ((hUb x hx).trans hNu)).1
    linarith
  have hFc : ContinuousOn (signalSource p U) (Icc 0 L) :=
    (continuousOn_const.mul ((continuousOn_const.add hUc).rpow_const
      (fun x hx => Or.inl (hbase x hx).ne'))).sub continuousOn_const
  let d : SignedEllipticEnergy.Profile L p.mu (signalSource p U) := {
    V := V
    dV := deriv V
    continuous_V := hV.continuousOn.mono hsub
    continuous_dV := (hV.continuousOn_deriv_of_isOpen hΩ (by norm_num)).mono hsub
    derivative_V := fun x hx =>
      ((hV x (hsub (Ioo_subset_Icc_self hx))).contDiffAt
        (hΩ.mem_nhds (hsub (Ioo_subset_Icc_self hx)))).differentiableAt (by norm_num) |>.hasDerivAt
    equation := by
      intro x hx
      have hd := (((hV.deriv_of_isOpen hΩ (m := 1) (by norm_num)) x
        (hsub (Ioo_subset_Icc_self hx))).contDiffAt
        (hΩ.mem_nhds (hsub (Ioo_subset_Icc_self hx)))).differentiableAt_one.hasDerivAt
      convert hd using 1
      linarith [heq x hx]
    neumann_left := hV0
    neumann_right := hVL }
  have hb : ∀ x ∈ Icc 0 L, |signalSource p U x| ≤ D*N := by
    intro x hx
    exact (hLip (U x) ((hUb x hx).trans hNu)).trans
      (mul_le_mul_of_nonneg_left (hUb x hx) hD)
  have h := d.c1_bound hL hmu hFc (mul_nonneg hD hN) hb
  intro x hx
  convert h x hx using 1; ring

/-- All-mode actual population Taylor remainder, controlled only by the
population sup bound. The actual nonlinear signal equation supplies both
signal amplitude and derivative bounds internally. -/
theorem actual_population_projection_population_norm_uniform (p : PhysicalParams) (beta L X : ℝ)
    (hX : 0 ≤ X)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) (hmu : 0 < p.mu)
    (hL : 0 < L) (heq : p.LogisticEquilibrium) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ chi : ℝ, |chi| ≤ X → ∀ (N : ℝ) (Ω : Set ℝ) (U V : ℝ → ℝ),
      IsOpen Ω → Icc 0 L ⊆ Ω → ContDiffOn ℝ 1 U Ω → ContDiffOn ℝ 2 V Ω →
      (∀ x ∈ Ω, 0 < p.uStar+U x) → (∀ x ∈ Ω, 0 < p.signalOffset+V x) →
      0 ≤ N → N ≤ r → (∀ x ∈ Icc 0 L, |U x| ≤ N) →
      deriv V 0 = 0 → deriv V L = 0 →
      (∀ x ∈ Ioo 0 L, deriv (deriv V) x - p.mu*V x + signalSource p U x = 0) →
      ∀ k : ℕ,
      |CosineCoefficients.cosineCoeff L (fun x => PopulationModalResidual.sourceRemainder p U x +
        deriv (PopulationModalResidual.fluxRemainder p beta chi U V) x) k| ≤
      (if k = 0 then 1/L else 2/L) * ((L+k*Real.pi)*C*N^4) := by
  obtain ⟨D,hD,hresponse⟩ := signal_response_C1_of_population_bound p hu
  obtain ⟨C,hC,hprojection⟩ :=
    PopulationModalResidual.actual_population_projection_quartic_uniform p beta X hX hu hw heq
  let A := 1/p.mu+2*L^2+2*L
  let K := max 1 (A*D)
  let R := min 1 (min (p.uStar/2) (p.signalOffset/2))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hR : 0 < R := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  refine ⟨R/K,div_pos hR hK,C*K^4,by positivity,?_⟩
  intro chi hchi N Ω U V hΩ hsub hU hV hposU hposV hN hNr hUb hV0 hVL hsig k
  have hKN : K*N ≤ R := by simpa only [mul_comm] using (le_div_iff₀ hK).mp hNr
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRu : R ≤ p.uStar/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hRv : R ≤ p.signalOffset/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hNKN : N ≤ K*N := by nlinarith [mul_nonneg (sub_nonneg.mpr hK1) hN]
  have hNV : ∀ x ∈ Icc 0 L, |V x|+|deriv V x| ≤ K*N := by
    intro x hx
    have hh := hresponse L N Ω U V hL hmu hΩ hsub hU.continuousOn hV
      hN (hNKN.trans (hKN.trans hRu)) hUb hV0 hVL hsig x hx
    have hk : A*D*N ≤ K*N := mul_le_mul_of_nonneg_right (le_max_right 1 (A*D)) hN
    exact hh.trans hk
  have hUbig : ∀ x ∈ Icc 0 L, |U x| ≤ K*N := fun x hx => (hUb x hx).trans hNKN
  have hVbig : ∀ x ∈ Icc 0 L, |V x| ≤ K*N := by
    intro x hx; have hh := hNV x hx; linarith [abs_nonneg (deriv V x)]
  have hDVbig : ∀ x ∈ Icc 0 L, |deriv V x| ≤ K*N := by
    intro x hx; have hh := hNV x hx; linarith [abs_nonneg (V x)]
  have hh := hprojection chi hchi L (K*N) Ω U V hL hΩ hsub hU hV hposU hposV
    (mul_nonneg hK.le hN) (hKN.trans hR1) (hKN.trans hRu) (hKN.trans hRv)
    hUbig hVbig hDVbig hV0 hVL k
  convert hh using 1; ring


/-- Fixed-sensitivity population-norm specialization. -/
theorem actual_population_projection_population_norm (p : PhysicalParams) (beta chi L : ℝ)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) (hmu : 0 < p.mu)
    (hL : 0 < L) (heq : p.LogisticEquilibrium) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℝ) (Ω : Set ℝ) (U V : ℝ → ℝ),
      IsOpen Ω → Icc 0 L ⊆ Ω → ContDiffOn ℝ 1 U Ω → ContDiffOn ℝ 2 V Ω →
      (∀ x ∈ Ω, 0 < p.uStar+U x) → (∀ x ∈ Ω, 0 < p.signalOffset+V x) →
      0 ≤ N → N ≤ r → (∀ x ∈ Icc 0 L, |U x| ≤ N) →
      deriv V 0 = 0 → deriv V L = 0 →
      (∀ x ∈ Ioo 0 L, deriv (deriv V) x - p.mu*V x + signalSource p U x = 0) →
      ∀ k : ℕ,
      |CosineCoefficients.cosineCoeff L (fun x => PopulationModalResidual.sourceRemainder p U x +
        deriv (PopulationModalResidual.fluxRemainder p beta chi U V) x) k| ≤
      (if k = 0 then 1/L else 2/L) * ((L+k*Real.pi)*C*N^4) := by
  obtain ⟨r,hr,C,hC,h⟩ := actual_population_projection_population_norm_uniform p beta L |chi|
    (abs_nonneg chi) hu hw hmu hL heq
  exact ⟨r,hr,C,hC,h chi le_rfl⟩

/-- The actual population profile is bounded by the l1 norm of its actual
Neumann cosine coefficients. Summability and series reconstruction are derived
from the ordinary NeumannW21 profile data. -/
theorem population_abs_le_cosine_l1 {L : ℝ} (hL : 0 < L) {U dU : ℝ → ℝ}
    (hU : CosineCoefficients.NeumannW21 L U dU) {x : ℝ} (hx : x ∈ Icc 0 L) :
    |U x| ≤ ∑' k : ℕ, |CosineCoefficients.cosineCoeff L U k| := by
  have hs := CosineCoefficients.summable_norm_cosineCoeff L hL hU
  have hb (k : ℕ) : ‖CosineCoefficients.cosineCoeff L U k * cos (k*Real.pi*x/L)‖ ≤
      ‖CosineCoefficients.cosineCoeff L U k‖ := by
    simp only [Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have hp : Summable (fun k : ℕ => ‖CosineCoefficients.cosineCoeff L U k * cos (k*Real.pi*x/L)‖) :=
    hs.of_nonneg_of_le (fun k => norm_nonneg _) hb
  calc
    |U x| = ‖∑' k : ℕ, CosineCoefficients.cosineCoeff L U k * cos (k*Real.pi*x/L)‖ := by
      rw [CosineCoefficients.tsum_cosineCoeff_eq L hL hU hx,Real.norm_eq_abs]
    _ ≤ ∑' k : ℕ, ‖CosineCoefficients.cosineCoeff L U k * cos (k*Real.pi*x/L)‖ := norm_tsum_le_tsum_norm hp
    _ ≤ ∑' k : ℕ, |CosineCoefficients.cosineCoeff L U k| := by
      simpa only [Real.norm_eq_abs] using hp.tsum_le_tsum hb hs

/-- The paper's actual coefficient-l1 population norm controls the actual
source-plus-flux modal remainder. No signal-size, Taylor, projected-balance or
Fourier-reconstruction assumption is supplied. -/
theorem actual_population_projection_cosine_l1_uniform (p : PhysicalParams) (beta L X : ℝ)
    (hX : 0 ≤ X)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) (hmu : 0 < p.mu)
    (hL : 0 < L) (heq : p.LogisticEquilibrium) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ chi : ℝ, |chi| ≤ X → ∀ (Ω : Set ℝ) (U V dU : ℝ → ℝ),
      IsOpen Ω → Icc 0 L ⊆ Ω → ContDiffOn ℝ 1 U Ω → ContDiffOn ℝ 2 V Ω →
      (∀ x ∈ Ω, 0 < p.uStar+U x) → (∀ x ∈ Ω, 0 < p.signalOffset+V x) →
      CosineCoefficients.NeumannW21 L U dU →
      (∑' k : ℕ, |CosineCoefficients.cosineCoeff L U k|) ≤ r →
      deriv V 0 = 0 → deriv V L = 0 →
      (∀ x ∈ Ioo 0 L, deriv (deriv V) x - p.mu*V x + signalSource p U x = 0) →
      ∀ k : ℕ,
      |CosineCoefficients.cosineCoeff L (fun x => PopulationModalResidual.sourceRemainder p U x +
        deriv (PopulationModalResidual.fluxRemainder p beta chi U V) x) k| ≤
      (if k = 0 then 1/L else 2/L) * ((L+k*Real.pi)*C*
        (∑' j : ℕ, |CosineCoefficients.cosineCoeff L U j|)^4) := by
  obtain ⟨r,hr,C,hC,hbound⟩ := actual_population_projection_population_norm_uniform p beta L X hX hu hw hmu hL heq
  refine ⟨r,hr,C,hC,?_⟩
  intro chi hchi Ω U V dU hΩ hsub hU hV hposU hposV hNeu hsmall hV0 hVL hsig k
  exact hbound chi hchi _ Ω U V hΩ hsub hU hV hposU hposV
    (tsum_nonneg (fun _ => abs_nonneg _)) hsmall
    (fun x hx => population_abs_le_cosine_l1 hL hNeu hx) hV0 hVL hsig k

/-- Fixed-sensitivity actual coefficient-l1 specialization. -/
theorem actual_population_projection_cosine_l1 (p : PhysicalParams) (beta chi L : ℝ)
    (hu : 0 < p.uStar) (hw : 0 < p.signalOffset) (hmu : 0 < p.mu)
    (hL : 0 < L) (heq : p.LogisticEquilibrium) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Set ℝ) (U V dU : ℝ → ℝ),
      IsOpen Ω → Icc 0 L ⊆ Ω → ContDiffOn ℝ 1 U Ω → ContDiffOn ℝ 2 V Ω →
      (∀ x ∈ Ω, 0 < p.uStar+U x) → (∀ x ∈ Ω, 0 < p.signalOffset+V x) →
      CosineCoefficients.NeumannW21 L U dU →
      (∑' k : ℕ, |CosineCoefficients.cosineCoeff L U k|) ≤ r →
      deriv V 0 = 0 → deriv V L = 0 →
      (∀ x ∈ Ioo 0 L, deriv (deriv V) x - p.mu*V x + signalSource p U x = 0) →
      ∀ k : ℕ,
      |CosineCoefficients.cosineCoeff L (fun x => PopulationModalResidual.sourceRemainder p U x +
        deriv (PopulationModalResidual.fluxRemainder p beta chi U V) x) k| ≤
      (if k = 0 then 1/L else 2/L) * ((L+k*Real.pi)*C*
        (∑' j : ℕ, |CosineCoefficients.cosineCoeff L U j|)^4) := by
  obtain ⟨r,hr,C,hC,h⟩ := actual_population_projection_cosine_l1_uniform p beta L |chi|
    (abs_nonneg chi) hu hw hmu hL heq
  exact ⟨r,hr,C,hC,h chi le_rfl⟩

end
end ChemotaxisBifurcation.PopulationNormBridge
