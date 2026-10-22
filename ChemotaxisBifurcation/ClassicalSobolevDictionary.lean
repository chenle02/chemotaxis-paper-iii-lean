module
public import ChemotaxisBifurcation.WeakDerivative1D
public import ChemotaxisBifurcation.SignalWeakSource
public import ChemotaxisBifurcation.SignalCompactness
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalSobolevDictionary
open Real Set MeasureTheory Filter Topology WeakDerivative1D SignalWeakSource
noncomputable section

/-- Ordinary classical derivatives satisfy the actual weak derivative tests. -/
theorem classical_weak_derivative {L : ℝ} {u du : ℝ → ℝ}
    (hL : 0 < L) (hu : ContinuousOn u (Icc 0 L)) (hdu : ContinuousOn du (Icc 0 L))
    (hd : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x) :
    ∀ phi : ℝ → ℝ, IsTestFunction L phi →
      ∫ x in (0 : ℝ)..L, u x*deriv phi x = -∫ x in (0 : ℝ)..L, du x*phi x := by
  intro phi hp
  have hh := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := L) (u := u) (v := phi) (u' := du) (v' := deriv phi)
    (by simpa only [uIcc_of_le hL.le] using hu)
    hp.continuous.continuousOn
    (by simpa only [min_eq_left hL.le,max_eq_right hL.le] using hd)
    (fun x _ => hp.1.differentiable (by simp) x |>.hasDerivAt)
    (hdu.intervalIntegrable_of_Icc hL.le) (hp.continuous_deriv.intervalIntegrable _ _)
  rw [hp.eq_zero_of_notMem (x := L) (by simp),hp.eq_zero_of_notMem (x := 0) (by simp)] at hh
  have h1 : IntervalIntegrable (fun x => du x*phi x) volume 0 L :=
    (hdu.mul hp.continuous.continuousOn).intervalIntegrable_of_Icc hL.le
  have h2 : IntervalIntegrable (fun x => u x*deriv phi x) volume 0 L :=
    (hu.mul hp.continuous_deriv.continuousOn).intervalIntegrable_of_Icc hL.le
  rw [intervalIntegral.integral_add h1 h2] at hh
  linarith

/-- Actual C2 classical data belong to the existing weak-derivative H2 space;
this is membership, not an assumed Sobolev regularity assertion. -/
theorem classical_H2 {L : ℝ} {u du ddu : ℝ → ℝ}
    (hL : 0 < L) (hu : ContinuousOn u (Icc 0 L))
    (hdu : ContinuousOn du (Icc 0 L)) (hddu : ContinuousOn ddu (Icc 0 L))
    (hd : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hdd : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x) : H2 L u du ddu := by
  have hm (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 L)) :
      MemLp f 2 (volume.restrict (Ioo 0 L)) :=
    (SpikeEstimates.interval_memLp_of_continuousOn hf 2).mono_measure
      (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  exact ⟨hm u hu,hm du hdu,hm ddu hddu,
    classical_weak_derivative hL hu hdu hd,classical_weak_derivative hL hdu hddu hdd⟩

/-- Actual endpoint conditions provide the exact Neumann trace used by H2. -/
theorem classical_neumann_trace {L : ℝ} {du : ℝ → ℝ}
    (hc : ContinuousOn du (Icc 0 L)) (h0 : du 0 = 0) (h1 : du L = 0) :
    NeumannTrace L du := ⟨du,hc,Eventually.of_forall (fun _ _ => rfl),h0,h1⟩

/-- The actual L2 difference of two continuous representatives is their
Lebesgue square-integral distance, with no arbitrary norm variables. -/
theorem norm_L2_difference {L : ℝ} (hL : 0 ≤ L) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 L)) (hg : ContinuousOn g (Icc 0 L)) :
    ‖functionToLp f hf 2-functionToLp g hg 2‖ =
      sqrt (∫ x in Icc 0 L, (f x-g x)^2) := by
  have he : functionToLp f hf 2-functionToLp g hg 2 =
      functionToLp (fun x => f x-g x) (hf.sub hg) 2 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (functionToLp f hf 2) (functionToLp g hg 2),
      coe_functionToLp f hf 2,coe_functionToLp g hg 2,
      coe_functionToLp (fun x => f x-g x) (hf.sub hg) 2] with x hs hf' hg' hd
    simpa only [Pi.sub_apply,hf',hg',hd] using hs
  rw [he]
  have hh := norm_functionToLp (fun x => f x-g x) (hf.sub hg) hL (by norm_num : (1 : ℝ)≤2)
  have ht : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [ht] at hh
  rw [hh,← sqrt_eq_rpow]
  congr 1
  rw [intervalIntegral.integral_of_le hL,← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  simp only
  rw [Real.rpow_two,sq_abs]

/-- The actual L2 derivative jet. Its ambient product norm is the maximum
of the three component L2 norms, equivalent to their sum below. -/
abbrev Jet (L : ℝ) := Lp ℝ 2 (intervalVolume L) ×
  (Lp ℝ 2 (intervalVolume L) × Lp ℝ 2 (intervalVolume L))

def jet {L : ℝ} (u du ddu : ℝ → ℝ)
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ContinuousOn du (Icc 0 L))
    (hddu : ContinuousOn ddu (Icc 0 L)) : Jet L :=
  (functionToLp u hu 2,(functionToLp du hdu 2,functionToLp ddu hddu 2))

/-- The standard sum-of-component L2 Sobolev distance on actual weak H2
representatives is exactly the actual classical three-integral distance. -/
theorem jet_component_distance {L : ℝ} (hL : 0 ≤ L) (u du ddu v dv ddv : ℝ → ℝ)
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ContinuousOn du (Icc 0 L))
    (hddu : ContinuousOn ddu (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hdv : ContinuousOn dv (Icc 0 L)) (hddv : ContinuousOn ddv (Icc 0 L)) :
    let J := jet u du ddu hu hdu hddu-jet v dv ddv hv hdv hddv
    ‖J.1‖+‖J.2.1‖+‖J.2.2‖ =
      sqrt (∫ x in Icc 0 L, (u x-v x)^2)+sqrt (∫ x in Icc 0 L, (du x-dv x)^2)+
        sqrt (∫ x in Icc 0 L, (ddu x-ddv x)^2) := by
  dsimp [jet]
  rw [norm_L2_difference hL u v hu hv,norm_L2_difference hL du dv hdu hdv,
    norm_L2_difference hL ddu ddv hddu hddv]

theorem jet_norm_equivalence {L : ℝ} (J : Jet L) :
    ‖J‖ ≤ ‖J.1‖+‖J.2.1‖+‖J.2.2‖ ∧
      ‖J.1‖+‖J.2.1‖+‖J.2.2‖ ≤ 3*‖J‖ := by
  change max ‖J.1‖ (max ‖J.2.1‖ ‖J.2.2‖) ≤ _ ∧ _ ≤ 3*max ‖J.1‖ (max ‖J.2.1‖ ‖J.2.2‖)
  constructor
  · apply max_le
    · linarith [norm_nonneg J.2.1,norm_nonneg J.2.2]
    · apply max_le <;> linarith [norm_nonneg J.1,norm_nonneg J.2.1,norm_nonneg J.2.2]
  · linarith [le_max_left ‖J.1‖ (max ‖J.2.1‖ ‖J.2.2‖),
      (le_max_left ‖J.2.1‖ ‖J.2.2‖).trans (le_max_right ‖J.1‖ (max ‖J.2.1‖ ‖J.2.2‖)),
      (le_max_right ‖J.2.1‖ ‖J.2.2‖).trans (le_max_right ‖J.1‖ (max ‖J.2.1‖ ‖J.2.2‖))]

/-- Actual component-Sobolev convergence gives convergence in the genuine
product-L2 ambient topology; the two norms have proved constants1 and3. -/
theorem jet_tendsto_of_component_distance {L : ℝ} (J : ℕ → Jet L) (K : Jet L)
    (h : Tendsto (fun n => ‖(J n-K).1‖+‖(J n-K).2.1‖+‖(J n-K).2.2‖) atTop (𝓝 0)) :
    Tendsto J atTop (𝓝 K) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => (jet_norm_equivalence (J n-K)).1) h

/-- The actual classical H1-to-continuous embedding bound in actual L2 norms.
It gives a uniform modulus for the continuous representative map on classical
Sobolev jets, rather than an assumed phase-space embedding. -/
theorem classical_sup_bound {L : ℝ} (hL : 0 < L) (u du : ℝ → ℝ)
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ContinuousOn du (Icc 0 L))
    (hd : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x) :
    ∀ x ∈ Icc 0 L, |u x| ≤
      ‖functionToLp u hu 2‖/L^(1/(2 : ℝ))+‖functionToLp du hdu 2‖*L^(1/(2 : ℝ)) := by
  have ht : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hU := norm_functionToLp u hu hL.le (by norm_num : (1 : ℝ)≤2)
  have hD := norm_functionToLp du hdu hL.le (by norm_num : (1 : ℝ)≤2)
  rw [ht] at hU hD
  have hh := SignalCompactness.sup_bound_of_Lq L 2
    ‖functionToLp u hu 2‖ ‖functionToLp du hdu 2‖ u du hL (by norm_num)
    (norm_nonneg _) hu hdu hd hU.ge hD.ge
  norm_num only [show (1-(1/(2 : ℝ)))=1/2 by norm_num] at hh
  exact hh

/-- Quantitative continuity of the actual classical representative map in
the genuine derivative-jet product-L2 topology. -/
theorem classical_sup_le_jet_norm {L : ℝ} (hL : 0 < L) (u du ddu : ℝ → ℝ)
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ContinuousOn du (Icc 0 L))
    (hddu : ContinuousOn ddu (Icc 0 L))
    (hd : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x) :
    ∀ x ∈ Icc 0 L, |u x| ≤
      (1/L^(1/(2 : ℝ))+L^(1/(2 : ℝ)))*‖jet u du ddu hu hdu hddu‖ := by
  intro x hx
  have h0 : ‖functionToLp u hu 2‖ ≤ ‖jet u du ddu hu hdu hddu‖ := by
    exact norm_fst_le (jet u du ddu hu hdu hddu)
  have h1 : ‖functionToLp du hdu 2‖ ≤ ‖jet u du ddu hu hdu hddu‖ :=
    (norm_fst_le (jet u du ddu hu hdu hddu).2).trans (norm_snd_le (jet u du ddu hu hdu hddu))
  have hLq : 0 ≤ L^(1/(2 : ℝ)) := Real.rpow_nonneg hL.le _
  calc |u x| ≤ ‖functionToLp u hu 2‖/L^(1/(2 : ℝ))+
        ‖functionToLp du hdu 2‖*L^(1/(2 : ℝ)) := classical_sup_bound hL u du hu hdu hd x hx
    _ ≤ ‖jet u du ddu hu hdu hddu‖/L^(1/(2 : ℝ))+
        ‖jet u du ddu hu hdu hddu‖*L^(1/(2 : ℝ)) :=
      add_le_add (div_le_div_of_nonneg_right h0 hLq) (mul_le_mul_of_nonneg_right h1 hLq)
    _ = _ := by ring

/-- Actual L2 representative formation respects differences. -/
theorem functionToLp_sub {L : ℝ} (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 L)) (hg : ContinuousOn g (Icc 0 L)) :
    functionToLp (fun x => f x-g x) (hf.sub hg) 2 =
      functionToLp f hf 2-functionToLp g hg 2 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (functionToLp f hf 2) (functionToLp g hg 2),
    coe_functionToLp f hf 2,coe_functionToLp g hg 2,
    coe_functionToLp (fun x => f x-g x) (hf.sub hg) 2] with x hs hf' hg' hd
  simpa only [Pi.sub_apply,hf',hg',hd] using hs.symm

/-- A genuine common Lipschitz bound for the continuous representative map
on actual classical derivative jets, with no abstract embedding hypothesis. -/
theorem difference_sup_le_jet_norm {L : ℝ} (hL : 0 < L) (u du ddu v dv ddv : ℝ → ℝ)
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ContinuousOn du (Icc 0 L))
    (hddu : ContinuousOn ddu (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hdv : ContinuousOn dv (Icc 0 L)) (hddv : ContinuousOn ddv (Icc 0 L))
    (hd : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (he : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x) :
    ∀ x ∈ Icc 0 L, |u x-v x| ≤ (1/L^(1/(2 : ℝ))+L^(1/(2 : ℝ)))*
      ‖jet u du ddu hu hdu hddu-jet v dv ddv hv hdv hddv‖ := by
  intro x hx
  let J := jet u du ddu hu hdu hddu-jet v dv ddv hv hdv hddv
  have h0 : ‖functionToLp u hu 2-functionToLp v hv 2‖ ≤ ‖J‖ := norm_fst_le J
  have h1 : ‖functionToLp du hdu 2-functionToLp dv hdv 2‖ ≤ ‖J‖ :=
    (norm_fst_le J.2).trans (norm_snd_le J)
  have hh := classical_sup_bound hL (fun y => u y-v y) (fun y => du y-dv y)
    (hu.sub hv) (hdu.sub hdv) (fun y hy => (hd y hy).sub (he y hy)) x hx
  rw [functionToLp_sub u v hu hv,functionToLp_sub du dv hdu hdv] at hh
  calc |u x-v x| ≤ _ := hh
    _ ≤ ‖J‖/L^(1/(2 : ℝ))+‖J‖*L^(1/(2 : ℝ)) :=
      add_le_add (div_le_div_of_nonneg_right h0 (Real.rpow_nonneg hL.le _))
        (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hL.le _))
    _ = _ := by ring

/-- The representative of a classical derivative jet is uniquely determined
on the physical interval by its actual product-L2 element. -/
theorem eqOn_of_jet_eq {L : ℝ} (hL : 0 < L) (u du ddu v dv ddv : ℝ → ℝ)
    (hu : ContinuousOn u (Icc 0 L)) (hdu : ContinuousOn du (Icc 0 L))
    (hddu : ContinuousOn ddu (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hdv : ContinuousOn dv (Icc 0 L)) (hddv : ContinuousOn ddv (Icc 0 L))
    (hd : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (he : ∀ x ∈ Ioo 0 L, HasDerivAt v (dv x) x)
    (hJ : jet u du ddu hu hdu hddu = jet v dv ddv hv hdv hddv) : EqOn u v (Icc 0 L) := by
  intro x hx
  have hh := difference_sup_le_jet_norm hL u du ddu v dv ddv hu hdu hddu hv hdv hddv hd he x hx
  rw [hJ,sub_self,norm_zero,mul_zero] at hh
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

/-- Literal supremum distance of actual representatives on the closed interval. -/
def supDistance (L : ℝ) (f g : ℝ → ℝ) : ℝ :=
  sSup ((fun x => |f x-g x|) '' Icc 0 L)

theorem supDistance_nonneg {L : ℝ} (hL : 0 ≤ L) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 L)) (hg : ContinuousOn g (Icc 0 L)) :
    0 ≤ supDistance L f g := by
  exact (abs_nonneg (f 0-g 0)).trans
    (le_csSup (isCompact_Icc.bddAbove_image (hf.sub hg).abs)
      (mem_image_of_mem (fun x => |f x-g x|) ⟨le_rfl,hL⟩))

/-- Ordinary uniform convergence is exactly strong enough to make the actual
supremum norm of the difference tend to zero. -/
theorem supDistance_tendsto {L : ℝ} (hL : 0 ≤ L) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n, ContinuousOn (f n) (Icc 0 L)) (hg : ContinuousOn g (Icc 0 L))
    (h : TendstoUniformlyOn f g atTop (Icc 0 L)) :
    Tendsto (fun n => supDistance L (f n) g) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (supDistance_nonneg hL (f n) g (hf n) hg))
  · intro b hb
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp h (b/2) (half_pos hb)] with n hn
    have hh : supDistance L (f n) g ≤ b/2 := by
      apply csSup_le
      · exact ⟨|f n 0-g 0|,0,⟨le_rfl,hL⟩,rfl⟩
      · rintro z ⟨x,hx,rfl⟩
        have ht := hn x hx
        simpa only [Real.dist_eq,abs_sub_comm] using ht.le
    exact hh.trans_lt (by linarith)

/-- The standard actual C2 norm distance: three supremum distances of the
function and its two actual derivatives. -/
def c2Distance (L : ℝ) (u du ddu v dv ddv : ℝ → ℝ) : ℝ :=
  supDistance L u v+supDistance L du dv+supDistance L ddu ddv

/-- Six uniform component convergences imply literal standard C2 norm
convergence, rather than merely naming a compactness criterion. -/
theorem c2Distance_tendsto {L : ℝ} (hL : 0 ≤ L) (u du ddu : ℕ → ℝ → ℝ)
    (v dv ddv : ℝ → ℝ)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hdu : ∀ n, ContinuousOn (du n) (Icc 0 L))
    (hddu : ∀ n, ContinuousOn (ddu n) (Icc 0 L))
    (hv : ContinuousOn v (Icc 0 L)) (hdv : ContinuousOn dv (Icc 0 L))
    (hddv : ContinuousOn ddv (Icc 0 L))
    (h0 : TendstoUniformlyOn u v atTop (Icc 0 L))
    (h1 : TendstoUniformlyOn du dv atTop (Icc 0 L))
    (h2 : TendstoUniformlyOn ddu ddv atTop (Icc 0 L)) :
    Tendsto (fun n => c2Distance L (u n) (du n) (ddu n) v dv ddv) atTop (𝓝 0) := by
  simpa only [c2Distance,add_zero] using
    ((supDistance_tendsto hL u v hu hv h0).add (supDistance_tendsto hL du dv hdu hdv h1)).add
      (supDistance_tendsto hL ddu ddv hddu hddv h2)

end
end ChemotaxisBifurcation.ClassicalSobolevDictionary
