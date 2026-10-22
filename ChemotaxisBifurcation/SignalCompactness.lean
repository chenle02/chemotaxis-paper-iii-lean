module
public import ChemotaxisBifurcation.SignalTesting
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.Order.ProjIcc

/-!
# Classical signal C1 subsequence compactness

Actual interval Lq bounds give a Holder modulus by FTC and Holder, and a
supremum bound via a minimum point. Pair-valued Arzela--Ascoli then produces
a subsequence converging uniformly in both v and its derivative. The
uniform-limit derivative theorem proves that the limit pair is compatible.
The final logistic-signal wrapper derives the actual W2q bound as well.

This does not prove weak extraction for the population source or its limiting
elliptic equation. It discharges the classical signal C1 extraction component
of the paper's larger analytic subsequence-extraction input.
-/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
namespace ChemotaxisBifurcation.SignalCompactness
noncomputable section

private theorem memLp_Icc {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (p : ENNReal) :
    MemLp f p (volume.restrict (Icc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hf.norm
  apply MemLp.of_bound hf.integrableOn_Icc.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC (mem_image_of_mem (fun x => ‖f x‖) hx)

/-- Actual Holder estimate for the L1 integral on any subinterval. -/
theorem integral_abs_le_Lq (a b q : ℝ) (f : ℝ → ℝ)
    (hab : a ≤ b) (hq : 1 < q) (hf : ContinuousOn f (Icc a b)) :
    (∫ x in a..b, |f x|) ≤
      (∫ x in a..b, |f x| ^ q) ^ (1 / q) * (b - a) ^ (1 - 1 / q) := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q - 1 := by linarith
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.HolderConjugate.conjExponent hq)
    (f := fun x => |f x|) (g := fun _ : ℝ => (1 : ℝ))
    (μ := volume.restrict (Icc a b))
    (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall fun _ => zero_le_one)
    (memLp_Icc hf.abs _) (memLp_const 1)
  simp only [mul_one, Real.one_rpow] at hh
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at hh
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at hh
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] at hh
  have he : 1 / Real.conjExponent q = 1 - 1 / q := by
    dsimp [Real.conjExponent]
    field_simp
  rwa [he] at hh

/-- FTC and Holder give the one-dimensional Sobolev modulus directly from
an actual derivative integral. -/
theorem derivative_holder (L q C : ℝ) (F f : ℝ → ℝ)
    (hL : 0 ≤ L) (hq : 1 < q) (_hC : 0 ≤ C)
    (hF : ContinuousOn F (Icc 0 L)) (hf : ContinuousOn f (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt F (f x) x)
    (hbound : (∫ x in (0 : ℝ)..L, |f x| ^ q) ^ (1 / q) ≤ C) :
    ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L,
      |F y - F x| ≤ C * |y - x| ^ (1 - 1 / q) := by
  have hq0 : 0 < q := by linarith
  have ordered : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L, x ≤ y →
      |F y - F x| ≤ C * |y - x| ^ (1 - 1 / q) := by
    intro x hx y hy hxy
    have hsub : Icc x y ⊆ Icc 0 L := Icc_subset_Icc hx.1 hy.2
    have hfi : IntervalIntegrable f volume x y := (hf.mono hsub).intervalIntegrable_of_Icc hxy
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy (hF.mono hsub)
      (fun t ht => hderiv t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩) hfi
    have hpow := hf.abs.rpow_const (p := q) (fun _ _ => Or.inr hq0.le)
    have hmono := intervalIntegral.integral_mono_interval (μ := volume) hx.1 hxy hy.2
      (Eventually.of_forall fun t => Real.rpow_nonneg (abs_nonneg (f t)) q)
      (hpow.intervalIntegrable_of_Icc hL)
    have hi0 : 0 ≤ ∫ t in x..y, |f t| ^ q :=
      intervalIntegral.integral_nonneg hxy fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
    have hp := Real.rpow_le_rpow hi0 hmono (by positivity : 0 ≤ 1 / q)
    have hnorm := hp.trans hbound
    calc |F y - F x| = |∫ t in x..y, f t| := by rw [hFTC]
      _ ≤ ∫ t in x..y, |f t| := intervalIntegral.abs_integral_le_integral_abs hxy
      _ ≤ (∫ t in x..y, |f t| ^ q) ^ (1 / q) * (y - x) ^ (1 - 1 / q) :=
        integral_abs_le_Lq x y q f hxy hq (hf.mono hsub)
      _ ≤ C * |y - x| ^ (1 - 1 / q) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
        exact mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg (sub_nonneg.mpr hxy) _)
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact ordered x hx y hy hxy
  · simpa only [abs_sub_comm] using ordered y hy x hx hyx

/-- Arzela--Ascoli and sequential compactness produce an actual subsequence;
no extraction hypothesis is used. -/
theorem exists_uniform_subsequence_of_modulus {L B : ℝ}
    (F : ℕ → Icc (0 : ℝ) L →ᵇ ℝ × ℝ) (b : ℝ → ℝ)
    (hb : Tendsto b (𝓝 0) (𝓝 0))
    (hbound : ∀ n x, ‖F n x‖ ≤ B)
    (hmod : ∀ n x y, dist (F n x) (F n y) ≤ b (dist x y)) :
    ∃ G : Icc (0 : ℝ) L →ᵇ ℝ × ℝ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ TendstoUniformly (fun n x => F (phi n) x) G atTop := by
  have hc : IsCompact (closure (range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ × ℝ) B)
      (isCompact_closedBall _ _) (range F)
    · intro f x hf
      obtain ⟨n, rfl⟩ := hf
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n x
    · apply Metric.equicontinuous_of_continuity_modulus b hb
      intro x y i
      rcases i with ⟨f, hf⟩
      obtain ⟨n, rfl⟩ := hf
      exact hmod n x y
  obtain ⟨G, _, phi, hphi, hlim⟩ := hc.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  exact ⟨G, phi, hphi, BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim⟩

/-- The classical signal and its derivative packaged on the compact interval. -/
def pairProfile {L : ℝ} (v dv : ℝ → ℝ)
    (hv : ContinuousOn v (Icc 0 L)) (hdv : ContinuousOn dv (Icc 0 L)) :
    Icc (0 : ℝ) L →ᵇ ℝ × ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (v x, dv x), continuousOn_iff_continuous_domRestrict.mp (hv.prodMk hdv)⟩

/-- Uniform actual derivative-integral bounds yield C1 subsequence compactness
for classical profiles. Uniform bounds are on the functions themselves,
not an abstract extraction or compact-embedding hypothesis. -/
theorem exists_pair_subsequence (L q B C D : ℝ) (v dv ddv : ℕ → ℝ → ℝ)
    (hL : 0 ≤ L) (hq : 1 < q) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hddv : ∀ n, ContinuousOn (ddv n) (Icc 0 L))
    (hderiv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x)
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (hbound : ∀ n x, x ∈ Icc 0 L → max |v n x| |dv n x| ≤ B)
    (hCq : ∀ n, (∫ x in (0 : ℝ)..L, |dv n x| ^ q) ^ (1 / q) ≤ C)
    (hDq : ∀ n, (∫ x in (0 : ℝ)..L, |ddv n x| ^ q) ^ (1 / q) ≤ D) :
    ∃ G : Icc (0 : ℝ) L →ᵇ ℝ × ℝ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ TendstoUniformly
        (fun n (x : Icc (0 : ℝ) L) => (v (phi n) x, dv (phi n) x)) G atTop := by
  have htheta : 0 < 1 - 1 / q := by
    have hq0 : 0 < q := by linarith
    have hh : 1 / q < 1 := (div_lt_one hq0).mpr hq
    linarith
  let F := fun n => pairProfile (v n) (dv n) (hv n) (hdv n)
  let b := fun t : ℝ => max C D * t ^ (1 - 1 / q)
  have hb : Tendsto b (𝓝 0) (𝓝 0) := by
    have ht := (Real.continuous_rpow_const htheta.le).tendsto (0 : ℝ)
    have hh := tendsto_const_nhds.mul ht (a := max C D)
    simpa only [Real.zero_rpow htheta.ne', mul_zero] using hh
  apply exists_uniform_subsequence_of_modulus F b hb
  · intro n x
    change max |v n x| |dv n x| ≤ B
    exact hbound n x x.property
  · intro n x y
    have h1 := derivative_holder L q C (v n) (dv n) hL hq hC (hv n) (hdv n)
      (hderiv n) (hCq n) y y.property x x.property
    have h2 := derivative_holder L q D (dv n) (ddv n) hL hq hD (hdv n) (hddv n)
      (hderiv2 n) (hDq n) y y.property x x.property
    change max |v n x - v n y| |dv n x - dv n y| ≤ _
    change max |v n x - v n y| |dv n x - dv n y| ≤
      max C D * |(x : ℝ) - (y : ℝ)| ^ (1 - 1 / q)
    apply max_le
    · exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left C D)
        (Real.rpow_nonneg (abs_nonneg _) _))
    · exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right C D)
        (Real.rpow_nonneg (abs_nonneg _) _))
/-- Derivatives pass to the extracted uniform limit on the interior, using the
actual derivative witnesses, not an assumed compatibility of the limit pair. -/
theorem derivative_consistent_of_pair_limit {L : ℝ} (v dv : ℕ → ℝ → ℝ)
    (V DV : ℝ → ℝ)
    (hlim : TendstoUniformlyOn (fun n x => (v n x, dv n x))
      (fun x => (V x, DV x)) atTop (Icc 0 L))
    (hderiv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x) :
    ∀ x ∈ Ioo 0 L, HasDerivAt V (DV x) x := by
  have hV := uniformContinuous_fst.comp_tendstoUniformlyOn hlim
  have hDV := uniformContinuous_snd.comp_tendstoUniformlyOn hlim
  intro x hx
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo
    (hDV.mono Ioo_subset_Icc_self) (Eventually.of_forall hderiv)
    (fun y hy => hV.tendsto_at (Ioo_subset_Icc_self hy)) hx

/-- Actual C1 subsequence extraction from uniform classical bounds and the
Lq derivative integrals, with the derivative of the limit identified. -/
theorem exists_classical_C1_subsequence (L q B C D : ℝ) (v dv ddv : ℕ → ℝ → ℝ)
    (hL : 0 ≤ L) (hq : 1 < q) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hddv : ∀ n, ContinuousOn (ddv n) (Icc 0 L))
    (hderiv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x)
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (hbound : ∀ n x, x ∈ Icc 0 L → max |v n x| |dv n x| ≤ B)
    (hCq : ∀ n, (∫ x in (0 : ℝ)..L, |dv n x| ^ q) ^ (1 / q) ≤ C)
    (hDq : ∀ n, (∫ x in (0 : ℝ)..L, |ddv n x| ^ q) ^ (1 / q) ≤ D) :
    ∃ V DV : ℝ → ℝ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ContinuousOn V (Icc 0 L) ∧ ContinuousOn DV (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => v (phi n)) V atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => dv (phi n)) DV atTop (Icc 0 L) ∧
      ∀ x ∈ Ioo 0 L, HasDerivAt V (DV x) x := by
  obtain ⟨G, phi, hphi, hlim⟩ := exists_pair_subsequence L q B C D v dv ddv hL hq hC hD
    hv hdv hddv hderiv hderiv2 hbound hCq hDq
  let pair := IccExtend hL G
  have hpair_cont : Continuous pair := continuous_IccExtend_iff.mpr G.continuous
  have hpair : TendstoUniformlyOn (fun n x => (v (phi n) x, dv (phi n) x)) pair
      atTop (Icc 0 L) := by
    rw [tendstoUniformlyOn_iff_restrict]
    have heq : (Icc 0 L).domRestrict pair = (G : Icc (0 : ℝ) L → ℝ × ℝ) := by
      funext x
      exact IccExtend_of_mem hL G x.property
    rw [heq]
    exact hlim
  refine ⟨fun x => (pair x).1, fun x => (pair x).2, phi, hphi,
    hpair_cont.fst.continuousOn, hpair_cont.snd.continuousOn, ?_, ?_, ?_⟩
  · exact uniformContinuous_fst.comp_tendstoUniformlyOn hpair
  · exact uniformContinuous_snd.comp_tendstoUniformlyOn hpair
  · exact derivative_consistent_of_pair_limit (fun n => v (phi n)) (fun n => dv (phi n))
      (fun x => (pair x).1) (fun x => (pair x).2) hpair (fun n => hderiv (phi n))
/-- The actual Lq norms of a function and derivative control its supremum.
This eliminates any separately assumed pointwise bound in the compactness
application. -/
theorem sup_bound_of_Lq (L q A C : ℝ) (F f : ℝ → ℝ)
    (hL : 0 < L) (hq : 1 < q) (hC : 0 ≤ C)
    (hF : ContinuousOn F (Icc 0 L)) (hf : ContinuousOn f (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt F (f x) x)
    (hFnorm : (∫ x in (0 : ℝ)..L, |F x| ^ q) ^ (1 / q) ≤ A)
    (hfnorm : (∫ x in (0 : ℝ)..L, |f x| ^ q) ^ (1 / q) ≤ C) :
    ∀ x ∈ Icc 0 L, |F x| ≤ A / L ^ (1 / q) + C * L ^ (1 - 1 / q) := by
  have hq0 : 0 < q := by linarith
  have htheta : 0 ≤ 1 - 1 / q := by
    have : 1 / q ≤ 1 := (div_le_one hq0).mpr hq.le
    linarith
  have hc := hF.abs.rpow_const (p := q) (fun _ _ => Or.inr hq0.le)
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hF.abs
  have hlow : L * |F y| ^ q ≤ ∫ x in (0 : ℝ)..L, |F x| ^ q :=
    IntervalMoments.le_integral_of_le hL.le hc
      (fun x hx => Real.rpow_le_rpow (abs_nonneg _) (hmin hx) hq0.le)
  have hlowpow := Real.rpow_le_rpow
    (mul_nonneg hL.le (Real.rpow_nonneg (abs_nonneg _) q)) hlow (by positivity : 0 ≤ 1 / q)
  rw [Real.mul_rpow hL.le (Real.rpow_nonneg (abs_nonneg _) q),
    ← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hq0.ne', Real.rpow_one] at hlowpow
  have hLq : 0 < L ^ (1 / q) := Real.rpow_pos_of_pos hL _
  have hybound : |F y| ≤ A / L ^ (1 / q) := by
    apply (le_div_iff₀ hLq).mpr
    nlinarith [hlowpow.trans hFnorm]
  intro x hx
  have hosci := derivative_holder L q C F f hL.le hq hC hF hf hderiv hfnorm y hy x hx
  have hdist : |x - y| ≤ L := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hd := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) hdist htheta) hC
  calc |F x| ≤ |F x - F y| + |F y| := by simpa using abs_add_le (F x - F y) (F y)
    _ ≤ A / L ^ (1 / q) + C * L ^ (1 - 1 / q) := by linarith

/-- Uniform actual W2q norm sums, q>1, give an actual C1-convergent
subsequence with identified derivative. No assumed embedding, equicontinuity,
supremum bound or extraction remains. -/
theorem exists_C1_subsequence_of_W2q_bound (L q W : ℝ) (v dv ddv : ℕ → ℝ → ℝ)
    (hL : 0 < L) (hq : 1 < q) (hW : 0 ≤ W)
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hddv : ∀ n, ContinuousOn (ddv n) (Icc 0 L))
    (hderiv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x)
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (hbound : ∀ n,
      (∫ x in (0 : ℝ)..L, |v n x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |dv n x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |ddv n x| ^ q) ^ (1 / q) ≤ W) :
    ∃ V DV : ℝ → ℝ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ContinuousOn V (Icc 0 L) ∧ ContinuousOn DV (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => v (phi n)) V atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => dv (phi n)) DV atTop (Icc 0 L) ∧
      ∀ x ∈ Ioo 0 L, HasDerivAt V (DV x) x := by
  have hnonneg : ∀ f : ℝ → ℝ, 0 ≤ (∫ x in (0 : ℝ)..L, |f x| ^ q) ^ (1 / q) :=
    fun f => Real.rpow_nonneg (intervalIntegral.integral_nonneg hL.le
      (fun x _ => Real.rpow_nonneg (abs_nonneg (f x)) q)) _
  have hcomponent : ∀ n,
      (∫ x in (0 : ℝ)..L, |v n x| ^ q) ^ (1 / q) ≤ W ∧
      (∫ x in (0 : ℝ)..L, |dv n x| ^ q) ^ (1 / q) ≤ W ∧
      (∫ x in (0 : ℝ)..L, |ddv n x| ^ q) ^ (1 / q) ≤ W := by
    intro n
    have h := hbound n
    have h0 := hnonneg (v n)
    have h1 := hnonneg (dv n)
    have h2 := hnonneg (ddv n)
    constructor
    · linarith
    constructor <;> linarith
  apply exists_classical_C1_subsequence L q
    (W / L ^ (1 / q) + W * L ^ (1 - 1 / q)) W W v dv ddv hL.le hq hW hW
    hv hdv hddv hderiv hderiv2
  · intro n x hx
    apply max_le
    · exact sup_bound_of_Lq L q W W (v n) (dv n) hL hq hW (hv n) (hdv n)
        (hderiv n) (hcomponent n).1 (hcomponent n).2.1 x hx
    · exact sup_bound_of_Lq L q W W (dv n) (ddv n) hL hq hW (hdv n) (hddv n)
        (hderiv2 n) (hcomponent n).2.1 (hcomponent n).2.2 x hx
  · exact fun n => (hcomponent n).2.1
  · exact fun n => (hcomponent n).2.2
/-- Classical logistic signal equations with uniform population moment give
an actual C1-convergent subsequence. The W2q estimate and compact embedding
are derived, not premises. Population weak extraction remains separate. -/
theorem exists_C1_subsequence_of_logistic_signal (L mu nu gamma alpha uStar q : ℝ)
    (u v dv ddv : ℕ → ℝ → ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hnu : 0 ≤ nu) (halpha : 0 < alpha)
    (hgamma : 0 < gamma) (huStar : 0 ≤ uStar) (hq : 1 < q)
    (hgq : gamma * q = 1 + alpha)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hu0 : ∀ n x, x ∈ Icc 0 L → 0 ≤ u n x)
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hvpos : ∀ n x, x ∈ Icc 0 L → 0 < v n x)
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hddv : ∀ n, ContinuousOn (ddv n) (Icc 0 L))
    (hderiv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x)
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (heq : ∀ n x, x ∈ Ioo 0 L → ddv n x - mu * v n x + nu * u n x ^ gamma = 0)
    (hbc0 : ∀ n, dv n 0 = 0) (hbcL : ∀ n, dv n L = 0)
    (hmoment : ∀ n, ∫ x in (0 : ℝ)..L, u n x ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha)) :
    ∃ V DV : ℝ → ℝ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ContinuousOn V (Icc 0 L) ∧ ContinuousOn DV (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => v (phi n)) V atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => dv (phi n)) DV atTop (Icc 0 L) ∧
      DV 0 = 0 ∧ DV L = 0 ∧
      ∀ x ∈ Ioo 0 L, HasDerivAt V (DV x) x := by
  let W := L ^ (1 / q) * uStar ^ gamma * (nu / mu + 2 * nu + 2 * nu * L)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hbounds : ∀ n,
      (∫ x in (0 : ℝ)..L, |v n x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |dv n x| ^ q) ^ (1 / q) +
      (∫ x in (0 : ℝ)..L, |ddv n x| ^ q) ^ (1 / q) ≤ W := by
    intro n
    exact SpikeEstimates.logistic_W2q_actual L mu nu gamma alpha uStar q (u n) (v n) (dv n) (ddv n)
      hL hmu hnu halpha hgamma huStar hq hgq (hu n) (hu0 n) (hv n) (hvpos n)
      (hdv n) (hddv n) (hderiv n) (hderiv2 n) (heq n) (hbc0 n) (hbcL n) (hmoment n)
  obtain ⟨V, DV, phi, hphi, hV, hDV, hvlim, hdvlim, hderivlim⟩ :=
    exists_C1_subsequence_of_W2q_bound L q W v dv ddv hL hq hW hv hdv hddv hderiv hderiv2 hbounds
  refine ⟨V, DV, phi, hphi, hV, hDV, hvlim, hdvlim, ?_, ?_, hderivlim⟩
  · have h := hdvlim.tendsto_at ⟨le_rfl, hL.le⟩
    simp only [hbc0] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · have h := hdvlim.tendsto_at ⟨hL.le, le_rfl⟩
    simp only [hbcL] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
end
end ChemotaxisBifurcation.SignalCompactness
