module
public import ChemotaxisBifurcation.BranchCurves

@[expose] public section

/-!
# The mixed remainder interface from smoothness and jets (Eq. 2.16, Eq. 2.43, Eq. 2.48)

`MixedRemainder` and `BranchCurves` take as inputs, on a box `|η|, |s| ≤ r ≤ 1`,
a value bound `|R(η, s)| ≤ C (|s| η² + |s|³ |η| + s⁴)`, a derivative bound
`|∂ₛR(η, s)| ≤ C (η² + s² |η| + |s|³)`, `HasDerivAt (R η) (∂ₛR(η, s)) s`, and
continuity of `η ↦ R(η, s)`. The arXiv v1 manuscript stated only a value `O(·)`.
Frozen v2 states the derivative estimate in Step 5 and invokes it in Step 4'.
This module supplies its conditional derivation; `RemainderAxis` additionally
derives the exact-axis cancellation used by the stronger v2 estimate.

This module derives all four inputs from honest hypotheses on the remainder
`R(η, s) = f(η, s) - α η s + β s³` of the reduced field (`JetHyp`):

* `R` is `C⁴` on an open set containing the box (the manuscript's center graph
  `\label{E:center-manifold-eq}`, Eq. 2.16, TeX line 1407, is `C⁴`);
* `R(η, 0) = 0` (trivial branch; from `h̃(0, χ̃) = 0`, TeX line 1404);
* at `(0, 0)`: `∂ₛR = 0` (`σ_{n₀}(χ*) = 0`), `∂_η∂ₛR = 0` (`α = ∂_{χ₀}σ_{n₀}`),
  `∂ₛ²R = 0` (no quadratic term in the `n₀` mode), `∂_η∂ₛ²R = 0`
  (`a_{k,2} = 0`, `\label{E:a_k,i-zero}`, and `Γ_{n₀} = 0`), `∂ₛ³R = 0`
  (`β = β_{n₀}`, `\label{E:beta-n0}`).

The route is the one-variable mean-value inequality applied eight times along
the segments `t ↦ (η, t)` and `t ↦ (t, 0)`, with uniform bounds on the third
and fourth derivatives from compactness of the box (`mixed_interface_of_jet`).
The resulting bounds include the weaker arXiv v1 Remark 1.1 form. The v2
Remark 1.1 / Eq. 2.43 form
(`u² χ̃²` instead of `|u| χ̃²`) holds, under the same hypotheses, if and only if
`∂ₛR(η, 0) = 0` on the box (`final_value_bound_iff`), i.e. the trivial-branch
eigenvalue is exactly `α χ̃`; this is not implied by the point jets.

The corollaries `jet_branch_eventually` and `jet_branch_curves` feed
`MixedRemainder.mixed_branch_eventually` and `BranchCurves.branch_curves` from
`JetHyp` alone. Center-manifold existence, the `C⁴` regularity of the reduced
field and the jet values themselves are hypotheses here, not conclusions.
Notation: `e = η = χ̃`, `s = u_{n₀}`; `eEta`, `eS` are the coordinate directions.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.RemainderFromJet

open ChemotaxisBifurcation.MixedRemainder ChemotaxisBifurcation.BranchCurves Filter Topology

/-- The parameter direction `∂_η` (`η = χ̃`) in `ℝ × ℝ`. -/
def eEta : ℝ × ℝ := (1, 0)

/-- The amplitude direction `∂_s` (`s = u_{n₀}`) in `ℝ × ℝ`. -/
def eS : ℝ × ℝ := (0, 1)

theorem norm_eEta : ‖eEta‖ = 1 := by simp [eEta, Prod.norm_def]

theorem norm_eS : ‖eS‖ = 1 := by simp [eS, Prod.norm_def]

theorem mem_box (r e s : ℝ) : ((e, s) : ℝ × ℝ) ∈ Metric.closedBall (0 : ℝ × ℝ) r ↔
    |e| ≤ r ∧ |s| ≤ r := by
  simp [Prod.norm_def, Real.norm_eq_abs]

/-- One mean-value step on the segment `[-|x|, |x|]`. -/
theorem abs_sub_le_of_deriv_bound (φ ψ : ℝ → ℝ) (x B : ℝ)
    (hd : ∀ t, |t| ≤ |x| → HasDerivAt φ (ψ t) t)
    (hb : ∀ t, |t| ≤ |x| → |ψ t| ≤ B) :
    |φ x - φ 0| ≤ B * |x| := by
  have hconv : Convex ℝ (Set.Icc (-|x|) |x|) := convex_Icc _ _
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ) (f' := ψ)
    (fun t ht => (hd t (abs_le.mpr ht)).hasDerivWithinAt)
    (fun t ht => by simpa [Real.norm_eq_abs] using hb t (abs_le.mpr ht))
    (⟨by simp, abs_nonneg x⟩ : (0 : ℝ) ∈ Set.Icc (-|x|) |x|)
    (⟨neg_abs_le x, le_abs_self x⟩ : x ∈ Set.Icc (-|x|) |x|)
  simpa [Real.norm_eq_abs] using h

/-- Derivative of a directional iterated derivative along a line. -/
theorem hasDerivAt_iteratedFDeriv_line (F : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hF : ContDiffOn ℝ 4 F U) {k : ℕ} (hk : k < 4) (p v : ℝ × ℝ) (m : Fin k → ℝ × ℝ)
    (t : ℝ) (ht : p + t • v ∈ U) :
    HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ k F (p + τ • v) m)
      (iteratedFDeriv ℝ (k + 1) F (p + t • v) (Fin.cons v m)) t := by
  have hca : ContDiffAt ℝ 4 F (p + t • v) := hF.contDiffAt (hU.mem_nhds ht)
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) (p + t • v) :=
    hca.differentiableAt_iteratedFDeriv (by exact_mod_cast hk)
  have hline : HasDerivAt (fun τ : ℝ => p + τ • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have h := (hdiff.hasFDerivAt.continuousMultilinear_apply_const m).comp_hasDerivAt t hline
  have hval : iteratedFDeriv ℝ (k + 1) F (p + t • v) (Fin.cons v m) =
      ((fderiv ℝ (iteratedFDeriv ℝ k F) (p + t • v)).flipMultilinear m) v := by
    rw [iteratedFDeriv_succ_apply_left]
    simp
  rw [hval]
  exact h


/-- Smoothness and jet hypotheses on the remainder `R(η, s)` (uncurried as `F`). -/
structure JetHyp (F : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ) : Prop where
  isOpen : IsOpen U
  smooth : ContDiffOn ℝ 4 F U
  r_pos : 0 < r
  r_le_one : r ≤ 1
  box_sub : Metric.closedBall (0 : ℝ × ℝ) r ⊆ U
  trivial : ∀ e, |e| ≤ r → F (e, 0) = 0
  jet_s : iteratedFDeriv ℝ 1 F 0 ![eS] = 0
  jet_eta_s : iteratedFDeriv ℝ 2 F 0 ![eEta, eS] = 0
  jet_ss : iteratedFDeriv ℝ 2 F 0 ![eS, eS] = 0
  jet_eta_ss : iteratedFDeriv ℝ 3 F 0 ![eEta, eS, eS] = 0
  jet_sss : iteratedFDeriv ℝ 3 F 0 ![eS, eS, eS] = 0

variable {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {r : ℝ}

theorem JetHyp.mem_U (h : JetHyp F U r) {e s : ℝ} (he : |e| ≤ r) (hs : |s| ≤ r) :
    ((e, s) : ℝ × ℝ) ∈ U :=
  h.box_sub ((mem_box r e s).2 ⟨he, hs⟩)

/-- Derivative in `s` of a directional iterated derivative at `(e, t)`. -/
theorem JetHyp.hasDerivAt_s (h : JetHyp F U r) {k : ℕ} (hk : k < 4) (m : Fin k → ℝ × ℝ)
    {e t : ℝ} (he : |e| ≤ r) (ht : |t| ≤ r) :
    HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ k F (e, τ) m)
      (iteratedFDeriv ℝ (k + 1) F (e, t) (Fin.cons eS m)) t := by
  have hp (τ : ℝ) : ((e, 0) : ℝ × ℝ) + τ • eS = (e, τ) := by ext <;> simp [eS]
  have := hasDerivAt_iteratedFDeriv_line F U h.isOpen h.smooth hk (e, 0) eS m t
    (by rw [hp]; exact h.mem_U he ht)
  simp only [hp] at this
  exact this

/-- Derivative in `η` of a directional iterated derivative at `(t, 0)`. -/
theorem JetHyp.hasDerivAt_eta (h : JetHyp F U r) {k : ℕ} (hk : k < 4) (m : Fin k → ℝ × ℝ)
    {t : ℝ} (ht : |t| ≤ r) :
    HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ k F (τ, 0) m)
      (iteratedFDeriv ℝ (k + 1) F (t, 0) (Fin.cons eEta m)) t := by
  have hp (τ : ℝ) : (0 : ℝ × ℝ) + τ • eEta = (τ, 0) := by ext <;> simp [eEta]
  have := hasDerivAt_iteratedFDeriv_line F U h.isOpen h.smooth hk 0 eEta m t
    (by rw [hp]; exact h.mem_U ht (by simpa using h.r_pos.le))
  simp only [hp] at this
  exact this

/-- Uniform bounds on the third and fourth derivatives on the closed box. -/
theorem JetHyp.exists_bound (h : JetHyp F U r) : ∃ M, 0 ≤ M ∧
    (∀ e s, |e| ≤ r → |s| ≤ r → ∀ m : Fin 3 → ℝ × ℝ,
      |iteratedFDeriv ℝ 3 F (e, s) m| ≤ M * ∏ i, ‖m i‖) ∧
    (∀ e s, |e| ≤ r → |s| ≤ r → ∀ m : Fin 4 → ℝ × ℝ,
      |iteratedFDeriv ℝ 4 F (e, s) m| ≤ M * ∏ i, ‖m i‖) := by
  have hK : IsCompact (Metric.closedBall (0 : ℝ × ℝ) r) := isCompact_closedBall _ _
  have hc (k : ℕ) (hk : k ≤ 4) :
      ContinuousOn (iteratedFDeriv ℝ k F) (Metric.closedBall (0 : ℝ × ℝ) r) := fun q hq =>
    ((h.smooth.contDiffAt (h.isOpen.mem_nhds (h.box_sub hq))).continuousAt_iteratedFDeriv
      (by exact_mod_cast hk)).continuousWithinAt
  obtain ⟨M3, hM3⟩ := hK.exists_bound_of_continuousOn (hc 3 (by norm_num))
  obtain ⟨M4, hM4⟩ := hK.exists_bound_of_continuousOn (hc 4 le_rfl)
  refine ⟨max (max M3 M4) 0, le_max_right _ _, ?_, ?_⟩
  · intro e s he hs m
    have hq := hM3 _ ((mem_box r e s).2 ⟨he, hs⟩)
    have hle := (iteratedFDeriv ℝ 3 F (e, s)).le_opNorm m
    rw [Real.norm_eq_abs] at hle
    have hp : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    calc _ ≤ _ := hle
      _ ≤ max (max M3 M4) 0 * ∏ i, ‖m i‖ :=
        mul_le_mul_of_nonneg_right (hq.trans ((le_max_left _ _).trans (le_max_left _ _))) hp
  · intro e s he hs m
    have hq := hM4 _ ((mem_box r e s).2 ⟨he, hs⟩)
    have hle := (iteratedFDeriv ℝ 4 F (e, s)).le_opNorm m
    rw [Real.norm_eq_abs] at hle
    have hp : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    calc _ ≤ _ := hle
      _ ≤ max (max M3 M4) 0 * ∏ i, ‖m i‖ :=
        mul_le_mul_of_nonneg_right (hq.trans ((le_max_right _ _).trans (le_max_left _ _))) hp


/-- A bound `M` for the third and fourth derivatives on the box. -/
def DerivBound (F : ℝ × ℝ → ℝ) (r M : ℝ) : Prop :=
  0 ≤ M ∧ (∀ e s, |e| ≤ r → |s| ≤ r → ∀ m : Fin 3 → ℝ × ℝ,
      |iteratedFDeriv ℝ 3 F (e, s) m| ≤ M * ∏ i, ‖m i‖) ∧
    (∀ e s, |e| ≤ r → |s| ≤ r → ∀ m : Fin 4 → ℝ × ℝ,
      |iteratedFDeriv ℝ 4 F (e, s) m| ≤ M * ∏ i, ‖m i‖)

variable {M : ℝ}

theorem DerivBound.b3 (hB : DerivBound F r M) {e s : ℝ} (he : |e| ≤ r) (hs : |s| ≤ r)
    (m : Fin 3 → ℝ × ℝ) (hm : ∏ i, ‖m i‖ = 1) : |iteratedFDeriv ℝ 3 F (e, s) m| ≤ M := by
  simpa [hm] using hB.2.1 e s he hs m

theorem DerivBound.b4 (hB : DerivBound F r M) {e s : ℝ} (he : |e| ≤ r) (hs : |s| ≤ r)
    (m : Fin 4 → ℝ × ℝ) (hm : ∏ i, ‖m i‖ = 1) : |iteratedFDeriv ℝ 4 F (e, s) m| ≤ M := by
  simpa [hm] using hB.2.2 e s he hs m

theorem JetHyp.zero_le_r (h : JetHyp F U r) : |(0 : ℝ)| ≤ r := by simpa using h.r_pos.le

/-- `|∂ₛ³R(η, 0)| ≤ M |η|`. -/
theorem sss_axis (h : JetHyp F U r) (hB : DerivBound F r M) {e : ℝ} (he : |e| ≤ r) :
    |iteratedFDeriv ℝ 3 F (e, 0) ![eS, eS, eS]| ≤ M * |e| := by
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 3 F (τ, 0) ![eS, eS, eS])
    (fun τ => iteratedFDeriv ℝ 4 F (τ, 0) ![eEta, eS, eS, eS]) e M
    (fun t ht => h.hasDerivAt_eta (by norm_num) _ (ht.trans he))
    (fun t ht => hB.b4 (ht.trans he) h.zero_le_r _
      (by simp [Fin.prod_univ_succ, norm_eS, norm_eEta]))
  simp only [Prod.mk_zero_zero, h.jet_sss, sub_zero] at key
  exact key

/-- `|∂ₛ³R(η, s)| ≤ M (|η| + |s|)`. -/
theorem sss_bound (h : JetHyp F U r) (hB : DerivBound F r M) {e s : ℝ} (he : |e| ≤ r)
    (hs : |s| ≤ r) :
    |iteratedFDeriv ℝ 3 F (e, s) ![eS, eS, eS]| ≤ M * (|e| + |s|) := by
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 3 F (e, τ) ![eS, eS, eS])
    (fun τ => iteratedFDeriv ℝ 4 F (e, τ) ![eS, eS, eS, eS]) s M
    (fun t ht => h.hasDerivAt_s (by norm_num) _ he (ht.trans hs))
    (fun t ht => hB.b4 he (ht.trans hs) _
      (by simp [Fin.prod_univ_succ, norm_eS]))
  have h0 := sss_axis h hB he
  have := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ 3 F (e, s) ![eS, eS, eS])
    (iteratedFDeriv ℝ 3 F (e, 0) ![eS, eS, eS])
  linarith

/-- `|∂_η ∂ₛ²R(η, 0)| ≤ M |η|`. -/
theorem etass_axis (h : JetHyp F U r) (hB : DerivBound F r M) {e : ℝ} (he : |e| ≤ r) :
    |iteratedFDeriv ℝ 3 F (e, 0) ![eEta, eS, eS]| ≤ M * |e| := by
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 3 F (τ, 0) ![eEta, eS, eS])
    (fun τ => iteratedFDeriv ℝ 4 F (τ, 0) ![eEta, eEta, eS, eS]) e M
    (fun t ht => h.hasDerivAt_eta (by norm_num) _ (ht.trans he))
    (fun t ht => hB.b4 (ht.trans he) h.zero_le_r _
      (by simp [Fin.prod_univ_succ, norm_eS, norm_eEta]))
  simp only [Prod.mk_zero_zero, h.jet_eta_ss, sub_zero] at key
  exact key

/-- `|∂ₛ²R(η, 0)| ≤ M η²`. -/
theorem ss_axis (h : JetHyp F U r) (hB : DerivBound F r M) {e : ℝ} (he : |e| ≤ r) :
    |iteratedFDeriv ℝ 2 F (e, 0) ![eS, eS]| ≤ M * e ^ 2 := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 2 F (τ, 0) ![eS, eS])
    (fun τ => iteratedFDeriv ℝ 3 F (τ, 0) ![eEta, eS, eS]) e (M * |e|)
    (fun t ht => h.hasDerivAt_eta (by norm_num) _ (ht.trans he))
    (fun t ht => (etass_axis h hB (ht.trans he)).trans (mul_le_mul_of_nonneg_left ht hM))
  simp only [Prod.mk_zero_zero, h.jet_ss, sub_zero] at key
  rw [← sq_abs e]
  linarith [key]


/-- `|∂ₛ²R(η, s)| ≤ M (η² + |s| (|η| + |s|))`. -/
theorem ss_bound (h : JetHyp F U r) (hB : DerivBound F r M) {e s : ℝ} (he : |e| ≤ r)
    (hs : |s| ≤ r) :
    |iteratedFDeriv ℝ 2 F (e, s) ![eS, eS]| ≤ M * (e ^ 2 + |s| * (|e| + |s|)) := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 2 F (e, τ) ![eS, eS])
    (fun τ => iteratedFDeriv ℝ 3 F (e, τ) ![eS, eS, eS]) s (M * (|e| + |s|))
    (fun t ht => h.hasDerivAt_s (by norm_num) _ he (ht.trans hs))
    (fun t ht => (sss_bound h hB he (ht.trans hs)).trans
      (mul_le_mul_of_nonneg_left (by linarith) hM))
  have h0 := ss_axis h hB he
  have := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ 2 F (e, s) ![eS, eS])
    (iteratedFDeriv ℝ 2 F (e, 0) ![eS, eS])
  nlinarith

/-- `|∂_η ∂ₛR(η, 0)| ≤ M |η|`. -/
theorem etas_axis (h : JetHyp F U r) (hB : DerivBound F r M) {e : ℝ} (he : |e| ≤ r) :
    |iteratedFDeriv ℝ 2 F (e, 0) ![eEta, eS]| ≤ M * |e| := by
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 2 F (τ, 0) ![eEta, eS])
    (fun τ => iteratedFDeriv ℝ 3 F (τ, 0) ![eEta, eEta, eS]) e M
    (fun t ht => h.hasDerivAt_eta (by norm_num) _ (ht.trans he))
    (fun t ht => hB.b3 (ht.trans he) h.zero_le_r _
      (by simp [Fin.prod_univ_succ, norm_eS, norm_eEta]))
  simp only [Prod.mk_zero_zero, h.jet_eta_s, sub_zero] at key
  exact key

/-- `|∂ₛR(η, 0)| ≤ M η²`. -/
theorem s_axis (h : JetHyp F U r) (hB : DerivBound F r M) {e : ℝ} (he : |e| ≤ r) :
    |iteratedFDeriv ℝ 1 F (e, 0) ![eS]| ≤ M * e ^ 2 := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 1 F (τ, 0) ![eS])
    (fun τ => iteratedFDeriv ℝ 2 F (τ, 0) ![eEta, eS]) e (M * |e|)
    (fun t ht => h.hasDerivAt_eta (by norm_num) _ (ht.trans he))
    (fun t ht => (etas_axis h hB (ht.trans he)).trans (mul_le_mul_of_nonneg_left ht hM))
  simp only [Prod.mk_zero_zero, h.jet_s, sub_zero] at key
  rw [← sq_abs e]
  linarith [key]

/-- The derivative bound `|∂ₛR(η, s)| ≤ 2M (η² + s² |η| + |s|³)` (`|s| ≤ 1`). -/
theorem s_bound (h : JetHyp F U r) (hB : DerivBound F r M) {e s : ℝ} (he : |e| ≤ r)
    (hs : |s| ≤ r) :
    |iteratedFDeriv ℝ 1 F (e, s) ![eS]| ≤ 2 * M * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3) := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 1 F (e, τ) ![eS])
    (fun τ => iteratedFDeriv ℝ 2 F (e, τ) ![eS, eS]) s (M * (e ^ 2 + |s| * (|e| + |s|)))
    (fun t ht => h.hasDerivAt_s (by norm_num) _ he (ht.trans hs))
    (fun t ht => (ss_bound h hB he (ht.trans hs)).trans
      (mul_le_mul_of_nonneg_left (by
        have := mul_le_mul ht (add_le_add_left ht |e|) (by positivity) (abs_nonneg s)
        linarith) hM))
  have h0 := s_axis h hB he
  have := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ 1 F (e, s) ![eS])
    (iteratedFDeriv ℝ 1 F (e, 0) ![eS])
  have hs1 : |s| ≤ 1 := hs.trans h.r_le_one
  have hes : e ^ 2 * |s| ≤ e ^ 2 := by nlinarith [sq_nonneg e, abs_nonneg s]
  have hid : M * (e ^ 2 + |s| * (|e| + |s|)) * |s| =
      M * (e ^ 2 * |s| + s ^ 2 * |e| + |s| ^ 3) := by rw [← sq_abs s]; ring
  have hle : M * (e ^ 2 * |s| + s ^ 2 * |e| + |s| ^ 3) ≤ M * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3) :=
    mul_le_mul_of_nonneg_left (by linarith) hM
  have he2 : M * e ^ 2 ≤ M * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3) :=
    mul_le_mul_of_nonneg_left (by
      have : 0 ≤ s ^ 2 * |e| + |s| ^ 3 := by positivity
      linarith) hM
  linarith


/-- `R(η, ·)` has derivative `∂ₛR(η, t)` at `t`. -/
theorem hasDerivAt_F (h : JetHyp F U r) {e t : ℝ} (he : |e| ≤ r) (ht : |t| ≤ r) :
    HasDerivAt (fun τ : ℝ => F (e, τ)) (iteratedFDeriv ℝ 1 F (e, t) ![eS]) t :=
  h.hasDerivAt_s (k := 0) (by norm_num) (![] : Fin 0 → ℝ × ℝ) he ht

/-- Value bound in the Remark 1.1 / Eq. 2.48 form:
`|R(η, s)| ≤ 2M (|s| η² + |s|³ |η| + s⁴)`. -/
theorem value_bound (h : JetHyp F U r) (hB : DerivBound F r M) {e s : ℝ} (he : |e| ≤ r)
    (hs : |s| ≤ r) :
    |F (e, s)| ≤ 2 * M * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4) := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => F (e, τ))
    (fun τ => iteratedFDeriv ℝ 1 F (e, τ) ![eS]) s (2 * M * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (fun t ht => hasDerivAt_F h he (ht.trans hs))
    (fun t ht => (s_bound h hB he (ht.trans hs)).trans
      (mul_le_mul_of_nonneg_left (by
        have h2 : t ^ 2 ≤ s ^ 2 := by rw [← sq_abs t, ← sq_abs s]; gcongr
        have h3 : |t| ^ 3 ≤ |s| ^ 3 := by gcongr
        have := mul_le_mul_of_nonneg_right h2 (abs_nonneg e)
        linarith) (by positivity)))
  simp only [h.trivial e he, sub_zero] at key
  calc |F (e, s)| ≤ 2 * M * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3) * |s| := key
    _ = 2 * M * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4) := by
      rw [← (by decide : Even 4).pow_abs s, ← sq_abs s]; ring

/-- Under the extra condition `∂ₛR(η, 0) = 0` (exact linearity of the trivial-branch
eigenvalue in `χ̃`), the derivative bound in the Eq. 2.43 form. -/
theorem s_bound_final (h : JetHyp F U r) (hB : DerivBound F r M)
    (hlin : ∀ e, |e| ≤ r → iteratedFDeriv ℝ 1 F (e, 0) ![eS] = 0) {e s : ℝ} (he : |e| ≤ r)
    (hs : |s| ≤ r) :
    |iteratedFDeriv ℝ 1 F (e, s) ![eS]| ≤ M * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3) := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => iteratedFDeriv ℝ 1 F (e, τ) ![eS])
    (fun τ => iteratedFDeriv ℝ 2 F (e, τ) ![eS, eS]) s (M * (e ^ 2 + |s| * (|e| + |s|)))
    (fun t ht => h.hasDerivAt_s (by norm_num) _ he (ht.trans hs))
    (fun t ht => (ss_bound h hB he (ht.trans hs)).trans
      (mul_le_mul_of_nonneg_left (by
        have := mul_le_mul ht (add_le_add_left ht |e|) (by positivity) (abs_nonneg s)
        linarith) hM))
  simp only [hlin e he, sub_zero] at key
  calc _ ≤ M * (e ^ 2 + |s| * (|e| + |s|)) * |s| := key
    _ = M * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3) := by rw [← sq_abs s]; ring

/-- Under `∂ₛR(η, 0) = 0`, the value bound in the Eq. 2.43 form
`|R(η, s)| ≤ M (s² η² + |s|³ |η| + s⁴)`. -/
theorem value_bound_final (h : JetHyp F U r) (hB : DerivBound F r M)
    (hlin : ∀ e, |e| ≤ r → iteratedFDeriv ℝ 1 F (e, 0) ![eS] = 0) {e s : ℝ} (he : |e| ≤ r)
    (hs : |s| ≤ r) :
    |F (e, s)| ≤ M * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4) := by
  have hM : 0 ≤ M := hB.1
  have key := abs_sub_le_of_deriv_bound (fun τ => F (e, τ))
    (fun τ => iteratedFDeriv ℝ 1 F (e, τ) ![eS]) s (M * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3))
    (fun t ht => hasDerivAt_F h he (ht.trans hs))
    (fun t ht => (s_bound_final h hB hlin he (ht.trans hs)).trans
      (mul_le_mul_of_nonneg_left (by
        have h1 := mul_le_mul_of_nonneg_right ht (sq_nonneg e)
        have h2 : t ^ 2 ≤ s ^ 2 := by rw [← sq_abs t, ← sq_abs s]; gcongr
        have h3 : |t| ^ 3 ≤ |s| ^ 3 := by gcongr
        have := mul_le_mul_of_nonneg_right h2 (abs_nonneg e)
        linarith) hM))
  simp only [h.trivial e he, sub_zero] at key
  calc |F (e, s)| ≤ M * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3) * |s| := key
    _ = M * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4) := by
      rw [← (by decide : Even 4).pow_abs s, ← sq_abs s]; ring


/-! ## The `MixedRemainder` interface from smoothness and jets -/

/-- The `s`-derivative `∂ₛR(η, s)` of a two-variable remainder, as a directional
iterated Fréchet derivative. -/
noncomputable def jetRs (R : ℝ → ℝ → ℝ) (e s : ℝ) : ℝ :=
  iteratedFDeriv ℝ 1 (Function.uncurry R) (e, s) ![eS]

/-- **The `MixedRemainder` interface follows from smoothness and jets.** If the
remainder `R(η, s)` is `C⁴` on an open set containing the box `|η|, |s| ≤ r ≤ 1`,
vanishes on the trivial branch `s = 0`, and satisfies the five point conditions
`∂ₛR = ∂_η∂ₛR = ∂ₛ²R = ∂_η∂ₛ²R = ∂ₛ³R = 0` at `(0, 0)`, then there is `C ≥ 0` with
the weak value bound, the `s`-derivative `jetRs R`, the matching derivative
bound, and continuity of `η ↦ R(η, s)`: exactly the hypotheses of
`MixedRemainder.mixed_branch_eventually` and `BranchCurves.branch_curves`. -/
theorem mixed_interface_of_jet (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (h : JetHyp (Function.uncurry R) U r) :
    ∃ C, 0 ≤ C ∧
      (∀ e s, |e| ≤ r → |s| ≤ r → |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4)) ∧
      (∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (jetRs R e s) s) ∧
      (∀ e s, |e| ≤ r → |s| ≤ r → |jetRs R e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) ∧
      (∀ e s, |e| < r → |s| ≤ r → ContinuousAt (fun e' => R e' s) e) := by
  obtain ⟨M, hM, h3, h4⟩ := h.exists_bound
  have hB : DerivBound (Function.uncurry R) r M := ⟨hM, h3, h4⟩
  refine ⟨2 * M, by positivity, fun e s he hs => value_bound h hB he hs,
    fun e s he hs => hasDerivAt_F h he hs, fun e s he hs => s_bound h hB he hs, ?_⟩
  intro e s he hs
  have hF : ContinuousAt (Function.uncurry R) (e, s) :=
    h.smooth.continuousOn.continuousAt (h.isOpen.mem_nhds (h.mem_U he.le hs))
  exact hF.comp (f := fun e' : ℝ => ((e', s) : ℝ × ℝ)) (by fun_prop)

/-- The Eq. 2.43 (`\label{E:center-ODE-final}`) form of both bounds follows when
in addition `∂ₛR(η, 0) = 0` on the box. -/
theorem final_interface_of_jet (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (h : JetHyp (Function.uncurry R) U r)
    (hlin : ∀ e, |e| ≤ r → jetRs R e 0 = 0) :
    ∃ C, 0 ≤ C ∧
      (∀ e s, |e| ≤ r → |s| ≤ r → |R e s| ≤ C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4)) ∧
      (∀ e s, |e| ≤ r → |s| ≤ r →
        |jetRs R e s| ≤ C * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) := by
  obtain ⟨M, hM, h3, h4⟩ := h.exists_bound
  have hB : DerivBound (Function.uncurry R) r M := ⟨hM, h3, h4⟩
  exact ⟨M, hM, fun e s he hs => value_bound_final h hB hlin he hs,
    fun e s he hs => s_bound_final h hB hlin he hs⟩

/-- Converse: an Eq. 2.43 value bound forces `∂ₛR(η, 0) = 0`. A differentiable
`φ` with `|φ s| ≤ K s²` near `0` has derivative `0` at `0`. -/
theorem deriv_zero_of_sq_bound (φ : ℝ → ℝ) (d K δ : ℝ) (hδ : 0 < δ)
    (hd : HasDerivAt φ d 0) (hb : ∀ s, |s| ≤ δ → |φ s| ≤ K * s ^ 2) : d = 0 := by
  have h0 : φ 0 = 0 := by simpa using hb 0 (by simpa using hδ.le)
  have hK : HasDerivAt φ 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, h0, sub_zero, smul_zero]
    have hsq : (fun s : ℝ => s ^ 2) =o[𝓝 0] fun s => s := by
      have := (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num))
      simpa using this
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hsq
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hδ] with s hs
    have := hb s (by simpa [Real.dist_eq] using hs)
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)] using this
  exact hd.unique hK

/-- Under the jet hypotheses, the Eq. 2.43 value bound holds on the box if and only if
`∂ₛR(η, 0) = 0` on the box. -/
theorem final_value_bound_iff (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (h : JetHyp (Function.uncurry R) U r) :
    (∃ C, ∀ e s, |e| ≤ r → |s| ≤ r → |R e s| ≤ C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4)) ↔
      ∀ e, |e| ≤ r → jetRs R e 0 = 0 := by
  constructor
  · rintro ⟨C, hC⟩ e he
    refine deriv_zero_of_sq_bound (R e) _ (C * (r ^ 2 + r + 1)) r h.r_pos
      (hasDerivAt_F h he h.zero_le_r) fun s hs => ?_
    have h1 := hC e s he hs
    have hr1 := h.r_le_one
    have hs1 : |s| ≤ 1 := hs.trans hr1
    have hC0 : 0 ≤ C := by
      by_contra hneg
      replace hneg := lt_of_not_ge hneg
      have := hC e r he (by rw [abs_of_pos h.r_pos])
      have hpos : 0 < r ^ 2 * e ^ 2 + |r| ^ 3 * |e| + r ^ 4 := by
        have : 0 < r ^ 4 := by have := h.r_pos; positivity
        positivity
      nlinarith [abs_nonneg (R e r)]
    have he2 : e ^ 2 ≤ r ^ 2 := by rw [← sq_abs e]; gcongr
    have hs3 : |s| ^ 3 * |e| ≤ s ^ 2 * r := by
      have : |s| ^ 3 ≤ s ^ 2 := by
        rw [← sq_abs s]; nlinarith [abs_nonneg s, sq_nonneg |s|]
      nlinarith [abs_nonneg e, pow_nonneg (abs_nonneg s) 3, sq_nonneg s]
    have hs4 : s ^ 4 ≤ s ^ 2 := by
      have : s ^ 2 ≤ 1 := by rw [← sq_abs s]; nlinarith [abs_nonneg s]
      nlinarith [sq_nonneg s]
    calc |R e s| ≤ C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4) := h1
      _ ≤ C * (s ^ 2 * r ^ 2 + s ^ 2 * r + s ^ 2) := by
        have := mul_le_mul_of_nonneg_left he2 (sq_nonneg s)
        exact mul_le_mul_of_nonneg_left (by linarith) hC0
      _ = C * (r ^ 2 + r + 1) * s ^ 2 := by ring
  · intro hlin
    obtain ⟨C, -, hv, -⟩ := final_interface_of_jet R U r h hlin
    exact ⟨C, hv⟩

/-- Non-vacuity: the zero remainder satisfies all smoothness and jet hypotheses
(on `U = univ`, any `0 < r ≤ 1`). -/
theorem jetHyp_zero (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    JetHyp (Function.uncurry fun _ _ : ℝ => (0 : ℝ)) Set.univ r := by
  have hz : Function.uncurry (fun _ _ : ℝ => (0 : ℝ)) = fun _ => 0 := rfl
  refine ⟨isOpen_univ, contDiffOn_const, hr, hr1, Set.subset_univ _, fun _ _ => rfl, ?_, ?_,
    ?_, ?_, ?_⟩ <;> simp [hz]

/-! ## Corollaries: the scalar endgame from smoothness and jets -/

/-- `MixedRemainder.mixed_branch_eventually` with the derivative bound discharged
by `mixed_interface_of_jet`: from `C⁴` smoothness and the jet conditions alone, for
all small `η` on the side `η β > 0` there are equilibria of both signs with
amplitude `√(αη/β) + O(|η|)` and `(∂ₛ field) · β < 0` (Step 5, TeX line 1975). -/
theorem jet_branch_eventually (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (h : JetHyp (Function.uncurry R) U r) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ eta in 𝓝 (0 : ℝ), 0 < eta * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ s, 0 < sgn * s ∧
        reducedField alpha beta R eta s = 0 ∧
        abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
          (2 * alpha * absorbedConst alpha beta C *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| ∧
        deriv (reducedField alpha beta R eta) s * beta < 0 := by
  obtain ⟨C, hC, hv, hd, hs, -⟩ := mixed_interface_of_jet R U r h
  exact ⟨C, hC, mixed_branch_eventually alpha beta C r R (jetRs R) halpha hbeta hC h.r_pos
    h.r_le_one hv hd hs⟩

/-- `BranchCurves.branch_curves` from `C⁴` smoothness and the jet conditions alone:
the continuous branch curves `Γ^±`, their local uniqueness, amplitude and
derivative sign, with no derivative bound taken as input. -/
theorem jet_branch_curves (alpha beta : ℝ) (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (h : JetHyp (Function.uncurry R) U r) :
    ∃ C, 0 ≤ C ∧
      0 < branchRadius alpha beta C r ∧ IsOpen {eta | CurveSmall alpha beta C r eta} ∧
      {eta | CurveSmall alpha beta C r eta} ∈ 𝓝 (0 : ℝ) ∧
      (∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
        ContinuousOn (branch alpha beta (branchRadius alpha beta C r) R sgn)
            {eta | CurveSmall alpha beta C r eta} ∧
          branch alpha beta (branchRadius alpha beta C r) R sgn 0 = 0 ∧
          Tendsto (branch alpha beta (branchRadius alpha beta C r) R sgn) (𝓝 0) (𝓝 0) ∧
          (∀ eta, CurveSmall alpha beta C r eta → eta * beta ≤ 0 →
            branch alpha beta (branchRadius alpha beta C r) R sgn eta = 0) ∧
          (∀ eta, CurveSmall alpha beta C r eta → 0 < eta * beta →
            (∃! s, BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta s) ∧
            BranchRoot alpha beta (branchRadius alpha beta C r) R sgn eta
                (branch alpha beta (branchRadius alpha beta C r) R sgn eta) ∧
            abs (|branch alpha beta (branchRadius alpha beta C r) R sgn eta| -
                Real.sqrt (alpha * eta / beta)) ≤ ampErr alpha beta C * |eta| ∧
            deriv (reducedField alpha beta R eta)
                (branch alpha beta (branchRadius alpha beta C r) R sgn eta) * beta < 0)) ∧
      (∀ eta s, CurveSmall alpha beta C r eta → s ≠ 0 →
        |s| ≤ branchRadius alpha beta C r → reducedField alpha beta R eta s = 0 →
        0 < eta * beta ∧
          (s = branch alpha beta (branchRadius alpha beta C r) R 1 eta ∨
            s = branch alpha beta (branchRadius alpha beta C r) R (-1) eta)) := by
  obtain ⟨C, hC, hv, hd, hs, hc⟩ := mixed_interface_of_jet R U r h
  exact ⟨C, hC, branch_curves alpha beta C r R (jetRs R) halpha hbeta hC h.r_pos h.r_le_one
    hv hd hs hc⟩

end ChemotaxisBifurcation.RemainderFromJet
