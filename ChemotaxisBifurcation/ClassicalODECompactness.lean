module
public import ChemotaxisBifurcation.SignalCompactness
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalODECompactness
open Set MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

/-- Bounded classical trajectories of a continuous autonomous vector field
have a derived common Lipschitz modulus on a compact time interval. -/
theorem trajectory_modulus (H : E → E) (hH : Continuous H)
    {L B : ℝ} (_hL : 0 ≤ L) (f : ℕ → ℝ → E)
    (hc : ∀ n, ContinuousOn (f n) (Icc 0 L))
    (hd : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (f n) (H (f n x)) x)
    (hb : ∀ n x, x ∈ Icc 0 L → ‖f n x‖ ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, x ∈ Icc 0 L → ∀ y, y ∈ Icc 0 L →
      ‖f n y-f n x‖ ≤ M*|y-x| := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : E) B).exists_bound_of_continuousOn hH.continuousOn
  refine ⟨max M 0,le_max_right _ _,?_⟩
  have hbound : ∀ n x, x ∈ Icc 0 L → ‖H (f n x)‖ ≤ max M 0 := by
    intro n x hx
    exact (hM (f n x) (by simpa only [Metric.mem_closedBall,dist_zero_right] using hb n x hx)).trans
      (le_max_left _ _)
  have ordered : ∀ n x, x ∈ Icc 0 L → ∀ y, y ∈ Icc 0 L → x ≤ y →
      ‖f n y-f n x‖ ≤ max M 0*|y-x| := by
    intro n x hx y hy hxy
    have hsub : Icc x y ⊆ Icc 0 L := Icc_subset_Icc hx.1 hy.2
    have hsource : ContinuousOn (fun t => H (f n t)) (Icc x y) := hH.comp_continuousOn ((hc n).mono hsub)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy ((hc n).mono hsub)
      (fun t ht => hd n t ⟨hx.1.trans_lt ht.1,ht.2.trans_le hy.2⟩)
      (hsource.intervalIntegrable_of_Icc hxy)
    rw [← hFTC]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => hbound n t (hsub (by rw [uIoc_of_le hxy] at ht; exact Ioc_subset_Icc_self ht)))
  intro n x hx y hy
  rcases le_total x y with hxy | hyx
  · exact ordered n x hx y hy hxy
  · simpa only [norm_sub_rev,abs_sub_comm] using ordered n y hy x hx hyx

/-- Continuous interior derivatives extend to one-sided endpoint derivatives
on a closed interval. The primitive identity is derived by FTC. -/
theorem derivativeWithin_closed_interval {L : ℝ} {g h : ℝ → E}
    (hg : ContinuousOn g (Icc 0 L)) (hh : ContinuousOn h (Icc 0 L))
    (hd : ∀ x ∈ Ioo 0 L, HasDerivAt g (h x) x) :
    ∀ x ∈ Icc 0 L, HasDerivWithinAt g (h x) (Icc 0 L) x := by
  have heq : ∀ y ∈ Icc 0 L, g y = g 0 + ∫ t in (0 : ℝ)..y, h t := by
    intro y hy
    have hsub : Icc 0 y ⊆ Icc 0 L := Icc_subset_Icc_right hy.2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy.1
      (hg.mono hsub) (fun t ht => hd t ⟨ht.1,ht.2.trans_le hy.2⟩)
      ((hh.mono hsub).intervalIntegrable_of_Icc hy.1)
    rw [hFTC]
    abel
  intro x hx
  let : Fact (x ∈ Icc (0 : ℝ) L) := ⟨hx⟩
  have hsub : Icc 0 x ⊆ Icc 0 L := Icc_subset_Icc_right hx.2
  have hi : IntervalIntegrable h volume 0 x := (hh.mono hsub).intervalIntegrable_of_Icc hx.1
  have hp := (intervalIntegral.integral_hasDerivWithinAt_right
    (s := Icc 0 L) (t := Icc 0 L) hi
    (hh.stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Icc x) (hh x hx)).const_add (g 0)
  exact hp.congr (fun y hy => heq y hy) (heq x hx)

/-- Actual uniform subsequence and limiting ODE, from a bounded family of
classical trajectories. No extraction or limiting differential equation is
an assumption. The vector field need not be globally Lipschitz. -/
theorem exists_stationary_subsequence (H : E → E) (hH : Continuous H)
    {L B : ℝ} (hL : 0 ≤ L) (f : ℕ → ℝ → E)
    (hc : ∀ n, ContinuousOn (f n) (Icc 0 L))
    (hd : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (f n) (H (f n x)) x)
    (hb : ∀ n x, x ∈ Icc 0 L → ‖f n x‖ ≤ B) :
    ∃ g : ℝ → E, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ContinuousOn g (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => f (phi n)) g atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n x => H (f (phi n) x)) (fun x => H (g x)) atTop (Icc 0 L) ∧
      (∀ x ∈ Icc 0 L, ‖g x‖ ≤ B) ∧
      ∀ x ∈ Ioo 0 L, HasDerivAt g (H (g x)) x := by
  obtain ⟨M,hM,hmod⟩ := trajectory_modulus H hH hL f hc hd hb
  let F : ℕ → Icc (0 : ℝ) L →ᵇ E := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f n x,continuousOn_iff_continuous_domRestrict.mp (hc n)⟩
  have hcompact : IsCompact (closure (range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : E) B)
      (isCompact_closedBall _ _) (range F)
    · intro g x hg
      obtain ⟨n,rfl⟩ := hg
      rw [Metric.mem_closedBall,dist_zero_right]
      change ‖f n x‖ ≤ B
      exact hb n x x.property
    · apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => M*t)
        (by simpa using (show Continuous (fun t : ℝ => M*t) by fun_prop).tendsto 0)
      intro x y i
      rcases i with ⟨g,hg⟩
      obtain ⟨n,rfl⟩ := hg
      change dist (f n x) (f n y) ≤ M*dist x y
      rw [dist_eq_norm,Subtype.dist_eq,Real.dist_eq]
      exact hmod n y y.property x x.property
  obtain ⟨G,_,phi,hphi,hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have huni := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  let g := IccExtend hL G
  have hgc : Continuous g := continuous_IccExtend_iff.mpr G.continuous
  have hu : TendstoUniformlyOn (fun n => f (phi n)) g atTop (Icc 0 L) := by
    rw [tendstoUniformlyOn_iff_restrict]
    have heq : (Icc 0 L).domRestrict g = (G : Icc (0 : ℝ) L → E) := by
      funext x; exact IccExtend_of_mem hL G x.property
    rw [heq]
    convert huni using 1
    funext n x
    rfl
  have hgb : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ B := by
    intro x hx
    exact isClosed_le continuous_norm continuous_const |>.mem_of_tendsto
      (hu.tendsto_at hx) (Eventually.of_forall (fun n => hb (phi n) x hx))
  have hsrc : TendstoUniformlyOn (fun n x => H (f (phi n) x)) (fun x => H (g x))
      atTop (Icc 0 L) := by
    apply UniformContinuousOn.comp_tendstoUniformlyOn_eventually
      (s := Metric.closedBall (0 : E) B) ?_ ?_
      ((isCompact_closedBall (0 : E) B).uniformContinuousOn_of_continuous hH.continuousOn) hu
    · exact Eventually.of_forall (fun n x hx => by
        simpa only [Metric.mem_closedBall,dist_zero_right] using hb (phi n) x hx)
    · intro x hx
      simpa only [Metric.mem_closedBall,dist_zero_right] using hgb x hx
  refine ⟨g,phi,hphi,hgc.continuousOn,hu,hsrc,hgb,?_⟩
  intro x hx
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hsrc.mono Ioo_subset_Icc_self)
    (Eventually.of_forall (fun n => hd (phi n)))
    (fun y hy => hu.tendsto_at (Ioo_subset_Icc_self hy)) hx

end
end ChemotaxisBifurcation.ClassicalODECompactness
