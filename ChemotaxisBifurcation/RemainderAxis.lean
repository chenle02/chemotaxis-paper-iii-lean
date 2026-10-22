module
public import ChemotaxisBifurcation.RemainderFromJet
public import ChemotaxisBifurcation.CrossingCoefficient

@[expose] public section

/-!
# The trivial-branch axis condition for the reduced field (Eq. 2.43)

`RemainderFromJet.final_value_bound_iff` shows that, under the smoothness and jet
hypotheses `JetHyp`, the Eq. 2.43 (`\label{E:center-ODE-final}`, TeX line 1943) value
bound `|R(η, s)| ≤ C (s² η² + |s|³ |η| + s⁴)` holds if and only if the axis condition
`∂ₛR(η, 0) = 0` holds on the box. This module closes the two remaining questions.

* **The point jets are not enough** (`jetHyp_not_sufficient`). The remainder
  `R(η, s) = η² s` is polynomial, vanishes on `s = 0`, and all five point jets of
  `JetHyp` vanish at `(0, 0)`, but `∂ₛR(η, 0) = η² ≠ 0`; taking `s ≪ η` the ratio
  `η² |s| / (s² η² + |s|³ |η| + s⁴)` is unbounded, so no Eq. 2.43 bound holds on any box.

* **The axis condition from the model** (`axis_of_reduction`). The manuscript's
  scalar ODE (Eq. `\label{E:center-ODE-initial}`, TeX line 1782) has linear part
  `∂_{χ₀}σ_{n₀}(χ*) χ̃ u_{n₀}`: the linearization of the full system at the trivial
  branch `u ≡ u*` is diagonal in the cosine modes with eigenvalues `σ_n(χ₀)`
  (Eq. `\label{E:sigma_n}`, TeX line 468), and the center coordinate `s = u_{n₀}` is
  the `n₀` mode with `h̃(0, χ̃) = 0` (TeX line 1403). The honest analytic input is
  therefore the named hypothesis `TrivialBranchLinearization`:
  `∂ₛf(η, 0) = σ_{n₀}(χ* + η)` for the reduced field `f`. Because `σ_{n₀}` is affine
  in `χ₀` with slope `α_{n₀}` (`CrossingCoefficient.modalGrowth_eq_affine`) and
  `σ_{n₀}(χ*) = 0` (`sigmaN0_chiStar`), this gives `∂ₛR(η, 0) = 0` for
  `R(η, s) = f(η, s) - α_{n₀} η s + β_{n₀} s³`, hence both Eq. 2.43 bounds
  (`model_final_interface`, `model_branch_curves`).

The center-manifold reduction itself (existence of `f`, its `C⁴` regularity, the jet
values, and `TrivialBranchLinearization`) is a hypothesis, not a conclusion.
Notation: `e = η = χ̃`, `s = u_{n₀}`, `x = λ_{n₀}`, `beta` is the sensitivity exponent
and `betaN0` the cubic coefficient `β_{n₀}`.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcation.RemainderAxis

open ChemotaxisBifurcation.MixedRemainder ChemotaxisBifurcation.BranchCurves
  ChemotaxisBifurcation.RemainderFromJet Filter Topology

/-! ## Part 1: the point jets do not give Eq. 2.43 -/

/-- Line-derivative characterization of a directional iterated derivative:
`D^{k+1}F(p)[v, m] = d/dτ D^kF(p + τ v)[m] |_{τ = 0}`. -/
theorem iteratedFDeriv_succ_eq_of_line (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 4 F) {k : ℕ}
    (hk : k < 4) (p v : ℝ × ℝ) (m : Fin k → ℝ × ℝ) (d : ℝ)
    (hd : HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ k F (p + τ • v) m) d 0) :
    iteratedFDeriv ℝ (k + 1) F p (Fin.cons v m) = d := by
  have h := hasDerivAt_iteratedFDeriv_line F Set.univ isOpen_univ hF.contDiffOn hk p v m 0
    (Set.mem_univ _)
  rw [zero_smul, add_zero] at h
  exact h.unique hd

/-- The counterexample remainder `R(η, s) = η² s`. -/
def cexR (e s : ℝ) : ℝ := e ^ 2 * s

theorem uncurry_cexR : Function.uncurry cexR = fun q : ℝ × ℝ => q.1 ^ 2 * q.2 := by
  funext q
  rfl

theorem contDiff_cexR : ContDiff ℝ 4 (Function.uncurry cexR) := by
  rw [uncurry_cexR]
  exact (contDiff_fst.pow 2).mul contDiff_snd

/-- `∂ₛR(η, s) = η²` for `R = η² s`. -/
theorem cex_d_s (e s : ℝ) :
    iteratedFDeriv ℝ 1 (Function.uncurry cexR) (e, s) ![eS] = e ^ 2 := by
  refine iteratedFDeriv_succ_eq_of_line _ contDiff_cexR (k := 0) (by norm_num) (e, s) eS ![]
    (e ^ 2) ?_
  have hfun : (fun τ : ℝ => iteratedFDeriv ℝ 0 (Function.uncurry cexR) ((e, s) + τ • eS) ![]) =
      fun τ => e ^ 2 * (s + τ) := by
    funext τ
    simp [eS, cexR]
  rw [hfun]
  simpa using ((hasDerivAt_id (0 : ℝ)).const_add s).const_mul (e ^ 2)

/-- `∂_η∂ₛR(η, s) = 2η` for `R = η² s`. -/
theorem cex_d_eta_s (e s : ℝ) :
    iteratedFDeriv ℝ 2 (Function.uncurry cexR) (e, s) ![eEta, eS] = 2 * e := by
  refine iteratedFDeriv_succ_eq_of_line _ contDiff_cexR (k := 1) (by norm_num) (e, s) eEta
    ![eS] (2 * e) ?_
  have hfun : (fun τ : ℝ =>
      iteratedFDeriv ℝ 1 (Function.uncurry cexR) ((e, s) + τ • eEta) ![eS]) =
      fun τ => (e + τ) ^ 2 := by
    funext τ
    have hp : ((e, s) : ℝ × ℝ) + τ • eEta = (e + τ, s) := by ext <;> simp [eEta]
    rw [hp, cex_d_s]
  rw [hfun]
  simpa using ((hasDerivAt_id (0 : ℝ)).const_add e).fun_pow 2

/-- `∂ₛ²R(η, s) = 0` for `R = η² s`. -/
theorem cex_d_ss (e s : ℝ) :
    iteratedFDeriv ℝ 2 (Function.uncurry cexR) (e, s) ![eS, eS] = 0 := by
  refine iteratedFDeriv_succ_eq_of_line _ contDiff_cexR (k := 1) (by norm_num) (e, s) eS
    ![eS] 0 ?_
  have hfun : (fun τ : ℝ =>
      iteratedFDeriv ℝ 1 (Function.uncurry cexR) ((e, s) + τ • eS) ![eS]) =
      fun _ => e ^ 2 := by
    funext τ
    have hp : ((e, s) : ℝ × ℝ) + τ • eS = (e, s + τ) := by ext <;> simp [eS]
    rw [hp, cex_d_s]
  rw [hfun]
  exact hasDerivAt_const _ _

/-- `∂ₛ∂_v∂ₛR(η, s) = 0` for `R = η² s` and either direction `v` placed first. -/
theorem cex_d3 (v : ℝ × ℝ) (e s : ℝ) :
    iteratedFDeriv ℝ 3 (Function.uncurry cexR) (e, s) ![v, eS, eS] = 0 := by
  refine iteratedFDeriv_succ_eq_of_line _ contDiff_cexR (k := 2) (by norm_num) (e, s) v
    ![eS, eS] 0 ?_
  have hfun : (fun τ : ℝ =>
      iteratedFDeriv ℝ 2 (Function.uncurry cexR) ((e, s) + τ • v) ![eS, eS]) =
      fun _ => 0 := by
    funext τ
    have hp : ((e, s) : ℝ × ℝ) + τ • v = (e + τ * v.1, s + τ * v.2) := by ext <;> simp
    rw [hp, cex_d_ss]
  rw [hfun]
  exact hasDerivAt_const _ _

/-- The counterexample satisfies all smoothness and jet hypotheses of `JetHyp`
(on `U = univ`, any `0 < r ≤ 1`). -/
theorem jetHyp_cex (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    JetHyp (Function.uncurry cexR) Set.univ r := by
  have h0 : (0 : ℝ × ℝ) = ((0 : ℝ), (0 : ℝ)) := rfl
  refine ⟨isOpen_univ, contDiff_cexR.contDiffOn, hr, hr1, Set.subset_univ _,
    fun e _ => by simp [cexR], ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, cex_d_s]; ring
  · rw [h0, cex_d_eta_s]; ring
  · rw [h0, cex_d_ss]
  · rw [h0, cex_d3]
  · rw [h0, cex_d3]

/-- The axis derivative of the counterexample: `∂ₛR(η, 0) = η²`. -/
theorem jetRs_cex (e s : ℝ) : jetRs cexR e s = e ^ 2 := cex_d_s e s

/-- **The counterexample violates Eq. 2.43 on every box.** For `R(η, s) = η² s` and
any `r > 0` there is no `C` with
`|R(η, s)| ≤ C (s² η² + |s|³ |η| + s⁴)` for `|η|, |s| ≤ r`. -/
theorem cex_not_final (r : ℝ) (hr : 0 < r) :
    ¬ ∃ C, ∀ e s, |e| ≤ r → |s| ≤ r →
      |cexR e s| ≤ C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4) := by
  rintro ⟨C, hC⟩
  set r' := min r 1 with hr'
  have hr'0 : 0 < r' := lt_min hr one_pos
  have hiff := final_value_bound_iff cexR Set.univ r' (jetHyp_cex r' hr'0 (min_le_right _ _))
  have hax := hiff.1 ⟨C, fun e s he hs => hC e s (he.trans (min_le_left _ _))
    (hs.trans (min_le_left _ _))⟩ r' (by rw [abs_of_pos hr'0])
  rw [jetRs_cex] at hax
  exact hr'0.ne' (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hax)

/-- **The point jets alone do not give Eq. 2.43.** It is false that every remainder
satisfying `JetHyp` admits the Eq. 2.43 value bound; the axis condition of
`final_value_bound_iff` is genuinely needed. -/
theorem jetHyp_not_sufficient :
    ¬ ∀ (R : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (r : ℝ), JetHyp (Function.uncurry R) U r →
      ∃ C, ∀ e s, |e| ≤ r → |s| ≤ r →
        |R e s| ≤ C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4) := fun hall =>
  cex_not_final 1 one_pos (hall cexR Set.univ 1 (jetHyp_cex 1 one_pos le_rfl))

/-! ## Part 2: the axis condition from the model -/

/-- The modal growth rate `σ_{n₀}(χ₀)` (Eq. `\label{E:sigma_n}`, TeX line 468)
at the eigenvalue `x = λ_{n₀}`:
`σ_{n₀}(χ₀) = -x + χ₀ νγ (u*)^{m+γ-1}/(1+v*)^β · x/(μ+x) - aα`, written through the
project's `LinearRegime.modalGrowth` with drive `p.thresholdK beta`. -/
noncomputable def sigmaN0 (p : PhysicalParams) (x beta chi : ℝ) : ℝ :=
  LinearRegime.modalGrowth chi (p.thresholdK beta) p.logisticSlope p.mu x

/-- `σ_{n₀}(χ*) = 0`: the threshold `χ*` is the zero of the modal growth rate. -/
theorem sigmaN0_chiStar (p : PhysicalParams) (x beta : ℝ)
    (hp : PhysicalModeGuards.PositiveModeParameters p) (hx : 0 < x) :
    sigmaN0 p x beta (p.chiStar x beta) = 0 := by
  unfold sigmaN0
  rw [CrossingCoefficient.modalGrowth_eq_affine]
  have hK := PhysicalModeGuards.thresholdK_pos p beta hp
  have hmx : p.mu + x ≠ 0 := (add_pos hp.mu_pos hx).ne'
  unfold PhysicalParams.alphaN0 PhysicalParams.chiStar
  field_simp
  ring

/-- `σ_{n₀}(χ* + η) = α_{n₀} η`: the modal growth rate is exactly linear in the
distance `χ̃ = χ₀ - χ*` to the threshold, with slope `α_{n₀}` (Eq. 2.44). -/
theorem sigmaN0_shift (p : PhysicalParams) (x beta e : ℝ)
    (hp : PhysicalModeGuards.PositiveModeParameters p) (hx : 0 < x) :
    sigmaN0 p x beta (p.chiStar x beta + e) = p.alphaN0 x beta * e := by
  have h0 := sigmaN0_chiStar p x beta hp hx
  unfold sigmaN0 at h0 ⊢
  rw [CrossingCoefficient.modalGrowth_eq_affine] at h0 ⊢
  linarith

/-- The remainder of a reduced field `f` after the normal form:
`R(η, s) = f(η, s) - α_{n₀} η s + β_{n₀} s³`. -/
noncomputable def remainderOf (p : PhysicalParams) (x beta betaN0 : ℝ) (f : ℝ → ℝ → ℝ)
    (e s : ℝ) : ℝ :=
  f e s - p.alphaN0 x beta * e * s + betaN0 * s ^ 3

/-- The reduced field is recovered from its remainder:
`f(η, s) = α_{n₀} η s - β_{n₀} s³ + R(η, s)`. -/
theorem reducedField_remainderOf (p : PhysicalParams) (x beta betaN0 : ℝ)
    (f : ℝ → ℝ → ℝ) (e s : ℝ) :
    reducedField (p.alphaN0 x beta) betaN0 (remainderOf p x beta betaN0 f) e s = f e s := by
  unfold reducedField remainderOf
  ring

/-- **The named reduction hypothesis.** Along the trivial branch `s = 0`, the
`s`-linear part of the reduced field is the `n₀` modal growth rate:
`∂ₛf(η, 0) = σ_{n₀}(χ* + η)` for `|η| ≤ r`.

This is what the center-manifold reduction gives: the linearization of the full
system at `u ≡ u*` is diagonal in the cosine modes with eigenvalues `σ_n(χ₀)`, the
center graph satisfies `h̃(0, χ̃) = 0` and `D h̃(0, 0) = 0` (TeX line 1403), and the
reduced field is the `n₀` component restricted to the center graph, whose
`s`-derivative at `s = 0` is the `n₀` eigenvalue `σ_{n₀}(χ* + χ̃)`. -/
def TrivialBranchLinearization (p : PhysicalParams) (x beta : ℝ) (f : ℝ → ℝ → ℝ)
    (r : ℝ) : Prop :=
  ∀ e, |e| ≤ r → HasDerivAt (f e) (sigmaN0 p x beta (p.chiStar x beta + e)) 0

/-- **The axis condition from the model.** Under `JetHyp` for the remainder and the
reduction hypothesis, `∂ₛR(η, 0) = σ_{n₀}(χ* + η) - α_{n₀} η = 0` on the box. -/
theorem axis_of_reduction (p : PhysicalParams) (x beta betaN0 : ℝ) (f : ℝ → ℝ → ℝ)
    (U : Set (ℝ × ℝ)) (r : ℝ) (hp : PhysicalModeGuards.PositiveModeParameters p)
    (hx : 0 < x) (h : JetHyp (Function.uncurry (remainderOf p x beta betaN0 f)) U r)
    (hred : TrivialBranchLinearization p x beta f r) :
    ∀ e, |e| ≤ r → jetRs (remainderOf p x beta betaN0 f) e 0 = 0 := by
  intro e he
  have h1 := hasDerivAt_F h he h.zero_le_r
  have h2 := ((hred e he).sub ((hasDerivAt_id (0 : ℝ)).const_mul (p.alphaN0 x beta * e))).add
    ((hasDerivAt_pow 3 (0 : ℝ)).const_mul betaN0)
  have h3 : jetRs (remainderOf p x beta betaN0 f) e 0 = _ := h1.unique h2
  rw [h3, sigmaN0_shift p x beta e hp hx]
  simp

/-- **Eq. 2.43 for the model.** Under `JetHyp` and the reduction hypothesis, the
remainder obeys both Eq. 2.43 (`\label{E:center-ODE-final}`) bounds
`|R| ≤ C (s² η² + |s|³ |η| + s⁴)` and `|∂ₛR| ≤ C (|s| η² + s² |η| + |s|³)`, and
`f = α_{n₀} η s - β_{n₀} s³ + R`. -/
theorem model_final_interface (p : PhysicalParams) (x beta betaN0 : ℝ) (f : ℝ → ℝ → ℝ)
    (U : Set (ℝ × ℝ)) (r : ℝ) (hp : PhysicalModeGuards.PositiveModeParameters p)
    (hx : 0 < x) (h : JetHyp (Function.uncurry (remainderOf p x beta betaN0 f)) U r)
    (hred : TrivialBranchLinearization p x beta f r) :
    ∃ C, 0 ≤ C ∧
      (∀ e s, |e| ≤ r → |s| ≤ r → |remainderOf p x beta betaN0 f e s| ≤
        C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4)) ∧
      (∀ e s, |e| ≤ r → |s| ≤ r → |jetRs (remainderOf p x beta betaN0 f) e s| ≤
        C * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) ∧
      (∀ e s, reducedField (p.alphaN0 x beta) betaN0 (remainderOf p x beta betaN0 f) e s =
        f e s) := by
  obtain ⟨C, hC, hv, hd⟩ := final_interface_of_jet _ U r h
    (axis_of_reduction p x beta betaN0 f U r hp hx h hred)
  exact ⟨C, hC, hv, hd, reducedField_remainderOf p x beta betaN0 f⟩

/-! ## Part 3: the branch curves with the Eq. 2.43 remainder -/

/-- **Branch curves for the model, with the Eq. 2.43 remainder.** Under `JetHyp`,
the reduction hypothesis and `β_{n₀} ≠ 0`, one constant `C ≥ 0` gives both Eq. 2.43
bounds and the full `BranchCurves.branch_curves` package (continuous curves `Γ^±`,
local uniqueness, amplitude `√(α_{n₀} η / β_{n₀}) + O(|η|)` and derivative sign)
for the reduced field `f = α_{n₀} η s - β_{n₀} s³ + R`. -/
theorem model_branch_curves (p : PhysicalParams) (x beta betaN0 : ℝ) (f : ℝ → ℝ → ℝ)
    (U : Set (ℝ × ℝ)) (r : ℝ) (hp : PhysicalModeGuards.PositiveModeParameters p)
    (hx : 0 < x) (hbeta : betaN0 ≠ 0)
    (h : JetHyp (Function.uncurry (remainderOf p x beta betaN0 f)) U r)
    (hred : TrivialBranchLinearization p x beta f r) :
    let alpha := p.alphaN0 x beta
    let R := remainderOf p x beta betaN0 f
    ∃ C, 0 ≤ C ∧
      (∀ e s, |e| ≤ r → |s| ≤ r → |R e s| ≤ C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4)) ∧
      (∀ e s, |e| ≤ r → |s| ≤ r →
        |jetRs R e s| ≤ C * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) ∧
      (∀ e s, reducedField alpha betaN0 R e s = f e s) ∧
      0 < branchRadius alpha betaN0 C r ∧ IsOpen {eta | CurveSmall alpha betaN0 C r eta} ∧
      {eta | CurveSmall alpha betaN0 C r eta} ∈ 𝓝 (0 : ℝ) ∧
      (∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
        ContinuousOn (branch alpha betaN0 (branchRadius alpha betaN0 C r) R sgn)
            {eta | CurveSmall alpha betaN0 C r eta} ∧
          branch alpha betaN0 (branchRadius alpha betaN0 C r) R sgn 0 = 0 ∧
          Tendsto (branch alpha betaN0 (branchRadius alpha betaN0 C r) R sgn) (𝓝 0) (𝓝 0) ∧
          (∀ eta, CurveSmall alpha betaN0 C r eta → eta * betaN0 ≤ 0 →
            branch alpha betaN0 (branchRadius alpha betaN0 C r) R sgn eta = 0) ∧
          (∀ eta, CurveSmall alpha betaN0 C r eta → 0 < eta * betaN0 →
            (∃! s, BranchRoot alpha betaN0 (branchRadius alpha betaN0 C r) R sgn eta s) ∧
            BranchRoot alpha betaN0 (branchRadius alpha betaN0 C r) R sgn eta
                (branch alpha betaN0 (branchRadius alpha betaN0 C r) R sgn eta) ∧
            abs (|branch alpha betaN0 (branchRadius alpha betaN0 C r) R sgn eta| -
                Real.sqrt (alpha * eta / betaN0)) ≤ ampErr alpha betaN0 C * |eta| ∧
            deriv (reducedField alpha betaN0 R eta)
                (branch alpha betaN0 (branchRadius alpha betaN0 C r) R sgn eta) * betaN0 < 0)) ∧
      (∀ eta s, CurveSmall alpha betaN0 C r eta → s ≠ 0 →
        |s| ≤ branchRadius alpha betaN0 C r → reducedField alpha betaN0 R eta s = 0 →
        0 < eta * betaN0 ∧
          (s = branch alpha betaN0 (branchRadius alpha betaN0 C r) R 1 eta ∨
            s = branch alpha betaN0 (branchRadius alpha betaN0 C r) R (-1) eta)) := by
  intro alpha R
  have halpha : 0 < alpha := PhysicalModeGuards.alphaN0_pos p x beta hp hx
  have hlin := axis_of_reduction p x beta betaN0 f U r hp hx h hred
  obtain ⟨M, hM, h3, h4⟩ := h.exists_bound
  have hB : DerivBound (Function.uncurry R) r M := ⟨hM, h3, h4⟩
  have hcont : ∀ e s, |e| < r → |s| ≤ r → ContinuousAt (fun e' => R e' s) e := by
    intro e s he hs
    have hF : ContinuousAt (Function.uncurry R) (e, s) :=
      h.smooth.continuousOn.continuousAt (h.isOpen.mem_nhds (h.mem_U he.le hs))
    exact hF.comp (f := fun e' : ℝ => ((e', s) : ℝ × ℝ)) (by fun_prop)
  refine ⟨2 * M, by positivity, fun e s he hs => ?_, fun e s he hs => ?_,
    reducedField_remainderOf p x beta betaN0 f, branch_curves alpha betaN0 (2 * M) r R (jetRs R)
      halpha hbeta (by positivity) h.r_pos h.r_le_one
      (fun e s he hs => value_bound h hB he hs) (fun e s he hs => hasDerivAt_F h he hs)
      (fun e s he hs => s_bound h hB he hs) hcont⟩
  · have : |R e s| ≤ M * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4) :=
      value_bound_final h hB hlin he hs
    have hp0 : 0 ≤ M * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4) := by positivity
    linarith
  · have : |jetRs R e s| ≤ M * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3) :=
      s_bound_final h hB hlin he hs
    have hp0 : 0 ≤ M * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3) := by positivity
    linarith

/-! ## Non-vacuity and the counterexample inside the model -/

/-- Non-vacuity: the exact normal form `f(η, s) = α_{n₀} η s - β_{n₀} s³` satisfies
the reduction hypothesis, and its remainder satisfies `JetHyp` (on `U = univ`,
any `0 < r ≤ 1`). -/
theorem normalForm_reduction (p : PhysicalParams) (x beta betaN0 r : ℝ)
    (hp : PhysicalModeGuards.PositiveModeParameters p) (hx : 0 < x) (hr : 0 < r)
    (hr1 : r ≤ 1) :
    TrivialBranchLinearization p x beta
        (fun e s => p.alphaN0 x beta * e * s - betaN0 * s ^ 3) r ∧
      JetHyp (Function.uncurry (remainderOf p x beta betaN0
        (fun e s => p.alphaN0 x beta * e * s - betaN0 * s ^ 3))) Set.univ r := by
  refine ⟨fun e _ => ?_, ?_⟩
  · rw [sigmaN0_shift p x beta e hp hx]
    have h := ((hasDerivAt_id (0 : ℝ)).const_mul (p.alphaN0 x beta * e)).sub
      ((hasDerivAt_pow 3 (0 : ℝ)).const_mul betaN0)
    convert h using 1
    · funext y
      simp
    · simp
  · have hR : remainderOf p x beta betaN0
        (fun e s => p.alphaN0 x beta * e * s - betaN0 * s ^ 3) = fun _ _ => 0 := by
      funext e s
      unfold remainderOf
      ring
    rw [hR]
    exact jetHyp_zero r hr hr1

/-- The counterexample, placed in the model: the reduced field
`f(η, s) = α_{n₀} η s - β_{n₀} s³ + η² s` has remainder `η² s`, which satisfies
`JetHyp`, but `f` violates the reduction hypothesis (its trivial-branch eigenvalue
`α_{n₀} η + η²` is not `σ_{n₀}(χ* + η)`). -/
theorem cex_violates_reduction (p : PhysicalParams) (x beta betaN0 r : ℝ)
    (hp : PhysicalModeGuards.PositiveModeParameters p) (hx : 0 < x) (hr : 0 < r)
    (hr1 : r ≤ 1) :
    JetHyp (Function.uncurry (remainderOf p x beta betaN0
        (fun e s => p.alphaN0 x beta * e * s - betaN0 * s ^ 3 + cexR e s))) Set.univ r ∧
      ¬ TrivialBranchLinearization p x beta
        (fun e s => p.alphaN0 x beta * e * s - betaN0 * s ^ 3 + cexR e s) r := by
  have hR : remainderOf p x beta betaN0
      (fun e s => p.alphaN0 x beta * e * s - betaN0 * s ^ 3 + cexR e s) = cexR := by
    funext e s
    unfold remainderOf
    ring
  have hJ : JetHyp (Function.uncurry (remainderOf p x beta betaN0
      (fun e s => p.alphaN0 x beta * e * s - betaN0 * s ^ 3 + cexR e s))) Set.univ r := by
    rw [hR]
    exact jetHyp_cex r hr hr1
  refine ⟨hJ, fun hred => ?_⟩
  have hax := axis_of_reduction p x beta betaN0 _ Set.univ r hp hx hJ hred r
    (by rw [abs_of_pos hr])
  rw [hR, jetRs_cex] at hax
  exact hr.ne' (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hax)

end ChemotaxisBifurcation.RemainderAxis
