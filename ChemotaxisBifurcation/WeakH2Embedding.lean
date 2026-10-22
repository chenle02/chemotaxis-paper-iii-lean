module
public import ChemotaxisBifurcation.ClassicalSobolevDictionary

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.WeakH2Embedding
open Real Set MeasureTheory Filter Topology WeakDerivative1D SignalWeakSource
noncomputable section

/-- Actual weak derivatives are unique a.e., even when their original
population representatives agree only a.e. The proof uses their literal
smooth compact-test identities and the fundamental lemma of distributions. -/
theorem weak_deriv_unique_of_ae_eq {L : ℝ} (hL : 0 < L) {u v g h : ℝ → ℝ}
    (hg : HasWeakDeriv L u g) (hh : HasWeakDeriv L v h)
    (huv : ∀ᵐ x, x ∈ Ioo 0 L → u x = v x) :
    ∀ᵐ x, x ∈ Ioo 0 L → g x = h x := by
  have hi : IntegrableOn (fun x => g x-h x) (Ioo 0 L) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le).mp (hg.integrable_deriv.sub hh.integrable_deriv)
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hi.locallyIntegrableOn ?_
  · filter_upwards [hz] with x hx hxI using sub_eq_zero.mp (hx hxI)
  intro phi hphi hcompact hsupp
  have hp : IsTestFunction L phi := ⟨hphi,hcompact,hsupp⟩
  simp only [smul_eq_mul]
  rw [hp.integral_mul_eq]
  have hleft : (∫ x in (0 : ℝ)..L, u x*deriv phi x) = ∫ x in (0 : ℝ)..L, v x*deriv phi x := by
    apply integral_congr_ae_Ioo hL.le
    filter_upwards [huv] with x hx hxI
    rw [hx hxI]
  have htests : (∫ x in (0 : ℝ)..L, g x*phi x) = ∫ x in (0 : ℝ)..L, h x*phi x := by
    rw [hg.integral_eq phi hp,hh.integral_eq phi hp] at hleft
    linarith
  have hig := hg.integrable_deriv.mul_continuousOn hp.continuous.continuousOn
  have hih := hh.integrable_deriv.mul_continuousOn hp.continuous.continuousOn
  calc (∫ x in (0 : ℝ)..L, phi x*(g x-h x)) =
      (∫ x in (0 : ℝ)..L, g x*phi x)-(∫ x in (0 : ℝ)..L, h x*phi x) := by
        rw [← intervalIntegral.integral_sub hig hih]
        exact intervalIntegral.integral_congr (fun x _ => by ring)
    _ = 0 := sub_eq_zero.mpr htests

theorem weak_deriv_unique {L : ℝ} (hL : 0 < L) {u g h : ℝ → ℝ}
    (hg : HasWeakDeriv L u g) (hh : HasWeakDeriv L u h) :
    ∀ᵐ x, x ∈ Ioo 0 L → g x = h x :=
  weak_deriv_unique_of_ae_eq hL hg hh (Eventually.of_forall (fun _ _ => rfl))

/-- The actual interval-subtype L2 norm of a continuous representative equals
the raw restricted-Ioo L2 norm of any a.e. equal original representative. -/
theorem norm_functionToLp_eq_raw {L : ℝ} (hL : 0 < L) {w U : ℝ → ℝ}
    (hw : MemLp w 2 (volume.restrict (Ioo 0 L)))
    (hU : ContinuousOn U (Icc 0 L)) (heq : ∀ᵐ x, x ∈ Ioo 0 L → w x = U x) :
    ‖functionToLp U hU 2‖ = ‖hw.toLp w‖ := by
  have hnorm := norm_functionToLp U hU hL.le (q := 2) (by norm_num)
  have ht : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [ht] at hnorm
  rw [hnorm,Lp.norm_toLp,toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp) hw.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,Real.norm_eq_abs]
  congr 1
  rw [intervalIntegral.integral_of_le hL.le,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_ae measurableSet_Ioo
  filter_upwards [heq] with x hx hxI
  rw [hx hxI]

/-- Every actual AC/C1 representative produced from weak H2 Neumann data has
a quantitative C0 bound in the original raw L2 norms. No embedding or maximum
estimate is an input. This works for every representative, hence for canonical
ones chosen later by the normed phase-space construction. -/
theorem representative_sup_bound {L : ℝ} (hL : 0 < L) {w w1 w2 U DU : ℝ → ℝ}
    (h : H2 L w w1 w2) (hU : CosineCoefficients.NeumannW21 L U DU)
    (heq : ∀ᵐ x, x ∈ Ioo 0 L → w x = U x)
    (heq1 : ∀ᵐ x, x ∈ Ioo 0 L → w1 x = DU x) :
    ∀ x ∈ Icc 0 L, |U x| ≤ ‖h.memLp.toLp w‖/L^(1/(2 : ℝ))+
      ‖h.memLp_deriv.toLp w1‖*L^(1/(2 : ℝ)) := by
  have hc : ContinuousOn U (Icc 0 L) := by simpa only [uIcc_of_le hL.le] using hU.ac.continuousOn
  have hdc : ContinuousOn DU (Icc 0 L) := by simpa only [uIcc_of_le hL.le] using hU.ac_deriv.continuousOn
  have hh := ClassicalSobolevDictionary.classical_sup_bound hL U DU hc hdc hU.hasDerivAt
  rw [norm_functionToLp_eq_raw hL h.memLp hc heq,
    norm_functionToLp_eq_raw hL h.memLp_deriv hdc heq1] at hh
  exact hh

/-- Sup control by the original raw derivative jet product norm. -/
theorem representative_sup_le_jet_norm {L : ℝ} (hL : 0 < L) {w w1 w2 U DU : ℝ → ℝ}
    (h : H2 L w w1 w2) (hU : CosineCoefficients.NeumannW21 L U DU)
    (heq : ∀ᵐ x, x ∈ Ioo 0 L → w x = U x)
    (heq1 : ∀ᵐ x, x ∈ Ioo 0 L → w1 x = DU x) :
    ∀ x ∈ Icc 0 L, |U x| ≤ (1/L^(1/(2 : ℝ))+L^(1/(2 : ℝ)))*
      ‖(h.memLp.toLp w,(h.memLp_deriv.toLp w1,h.memLp_deriv2.toLp w2))‖ := by
  intro x hx
  let J := (h.memLp.toLp w,(h.memLp_deriv.toLp w1,h.memLp_deriv2.toLp w2))
  have h0 : ‖h.memLp.toLp w‖ ≤ ‖J‖ := norm_fst_le J
  have h1 : ‖h.memLp_deriv.toLp w1‖ ≤ ‖J‖ := (norm_fst_le J.2).trans (norm_snd_le J)
  have hq : 0 ≤ L^(1/(2 : ℝ)) := Real.rpow_nonneg hL.le _
  calc |U x| ≤ ‖h.memLp.toLp w‖/L^(1/(2 : ℝ))+‖h.memLp_deriv.toLp w1‖*L^(1/(2 : ℝ)) :=
      representative_sup_bound hL h hU heq heq1 x hx
    _ ≤ ‖J‖/L^(1/(2 : ℝ))+‖J‖*L^(1/(2 : ℝ)) :=
      add_le_add (div_le_div_of_nonneg_right h0 hq) (mul_le_mul_of_nonneg_right h1 hq)
    _ = _ := by ring

end
end ChemotaxisBifurcation.WeakH2Embedding
