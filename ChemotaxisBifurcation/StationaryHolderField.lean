module
public import ChemotaxisBifurcation.UniformHolderAlgebra
public import ChemotaxisBifurcation.PhysicalClassicalAdapter

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.StationaryHolderField
open Real Set MeasureTheory Filter Topology StationaryODEState UniformHolderAlgebra
noncomputable section
variable {ι : Type*}

theorem trajectory_modulus (H : State → State) (hH : Continuous H)
    {L B : ℝ} (_hL : 0 ≤ L) (f : ι → ℝ → State)
    (hc : ∀ n, ContinuousOn (f n) (Icc 0 L))
    (hd : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (f n) (H (f n x)) x)
    (hb : ∀ n x, x ∈ Icc 0 L → ‖f n x‖ ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, x ∈ Icc 0 L → ∀ y, y ∈ Icc 0 L →
      ‖f n y-f n x‖ ≤ M*|y-x| := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : State) B).exists_bound_of_continuousOn hH.continuousOn
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

/-- A state coordinate inherits the derived common trajectory Lipschitz modulus. -/
def coordinate {L B M : ℝ} (f : ι → ℝ → State) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hb : ∀ n x, x ∈ Icc 0 L → ‖f n x‖ ≤ B)
    (hl : ∀ n x, x ∈ Icc 0 L → ∀ y, y ∈ Icc 0 L → ‖f n y-f n x‖ ≤ M*|y-x|)
    (q : State → ℝ) (hq : ∀ z, |q z| ≤ ‖z‖)
    (hsub : ∀ z w, q (z-w) = q z-q w) : Control L (fun n x => q (f n x)) :=
  Control.of_lipschitz B M hB hM
    (fun n x hx => (hq _).trans (hb n x hx))
    (fun n x hx y hy => by rw [← hsub]; exact (hq _).trans (hl n x hx y hy))

/-- The actual nonlinear ODE field has a derived common bounded Hölder
modulus on every bounded physical family with a common state Lipschitz modulus. -/
theorem field_controls {L B M a b alpha m beta mu nu gamma : ℝ}
    (f : ι → ℝ → State) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hb : ∀ n x, x ∈ Icc 0 L → ‖f n x‖ ≤ B)
    (hl : ∀ n x, x ∈ Icc 0 L → ∀ y, y ∈ Icc 0 L → ‖f n y-f n x‖ ≤ M*|y-x|)
    (hu : ∀ n x, x ∈ Icc 0 L → 0 ≤ (f n x).2.1.1)
    (hv : ∀ n x, x ∈ Icc 0 L → 0 ≤ (f n x).2.2.1)
    (halpha : 0 ≤ alpha) (hm : 1 ≤ m) (hgamma : 0 ≤ gamma) :
    Nonempty (Control L (fun n x => (field a b alpha m beta mu nu gamma (f n x)).2.1.2)) ∧
    Nonempty (Control L (fun n x => (field a b alpha m beta mu nu gamma (f n x)).2.2.2)) := by
  let hChi := coordinate f hB hM hb hl (fun z => z.1)
    (fun z => norm_fst_le z) (fun _ _ => rfl)
  let hU := coordinate f hB hM hb hl (fun z => z.2.1.1)
    (fun z => (norm_fst_le _).trans ((norm_fst_le _).trans (norm_snd_le z)))
    (fun _ _ => rfl)
  let hDU := coordinate f hB hM hb hl (fun z => z.2.1.2)
    (fun z => (norm_snd_le _).trans ((norm_fst_le _).trans (norm_snd_le z)))
    (fun _ _ => rfl)
  let hV := coordinate f hB hM hb hl (fun z => z.2.2.1)
    (fun z => (norm_fst_le _).trans ((norm_snd_le _).trans (norm_snd_le z)))
    (fun _ _ => rfl)
  let hDV := coordinate f hB hM hb hl (fun z => z.2.2.2)
    (fun z => (norm_snd_le _).trans ((norm_snd_le _).trans (norm_snd_le z)))
    (fun _ _ => rfl)
  let hW := (Control.const L 1).add hV
  have hWpos : ∀ n x, x ∈ Icc 0 L → 1 ≤ 1+(f n x).2.2.1 := by
    intro n x hx; linarith [hv n x hx]
  let hInv := hW.rpow_positive (-beta) 1 zero_lt_one hWpos
  let hInv1 := hW.rpow_positive (-(beta+1)) 1 zero_lt_one hWpos
  let hR := hU.rpow (m-1) (by linarith) hu
  let hA := hU.rpow alpha halpha hu
  let hG := hU.rpow gamma hgamma hu
  let hS := ((Control.const L mu).mul hV).add ((Control.const L (-nu)).mul hG)
  let hZ := ((Control.const L a).add ((Control.const L (-b)).mul hA)).add
    (((Control.const L (-1)).mul (hChi.mul hR)).mul
      ((hS.mul hInv).add (((Control.const L (-beta)).mul (hDV.mul hDV)).mul hInv1)))
  let hD := (((hChi.mul (Control.const L m)).mul hR).mul hDV).mul hInv
  let hP := (((Control.const L (-1)).mul hZ).mul hU).add (hD.mul hDU)
  constructor
  · refine ⟨hP.congr ?_⟩
    intro n x hx
    have hbase : 0 ≤ 1+(f n x).2.2.1 := by linarith [hv n x hx]
    have hmax : max 1 (1+(f n x).2.2.1) = 1+(f n x).2.2.1 := max_eq_right (hWpos n x hx)
    change (-1)*(a+ -b*(f n x).2.1.1^alpha +
      (-1*((f n x).1*(f n x).2.1.1^(m-1)))*
        ((mu*(f n x).2.2.1 + -nu*(f n x).2.1.1^gamma)*(1+(f n x).2.2.1)^(-beta) +
          (-beta*((f n x).2.2.2*(f n x).2.2.2))*(1+(f n x).2.2.1)^(-(beta+1))))*(f n x).2.1.1 +
      (((f n x).1*m*(f n x).2.1.1^(m-1))*(f n x).2.2.2)*(1+(f n x).2.2.1)^(-beta)*(f n x).2.1.2 = _
    dsimp [field,zero,drift,signalRHS,offset]
    rw [hmax,Real.rpow_neg hbase,Real.rpow_neg hbase]
    simp only [div_eq_mul_inv]
    ring
  · refine ⟨hS.congr ?_⟩
    intro n x hx
    dsimp [field,signalRHS]
    ring

end
end ChemotaxisBifurcation.StationaryHolderField
