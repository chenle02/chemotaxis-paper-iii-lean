module
public import ChemotaxisBifurcation.MonotoneLocus
public import ChemotaxisBifurcation.AmbientClosure

@[expose] public section

/-! One-dimensional Neumann strong positivity from linear ODE uniqueness.
This formalizes the existing maximum-principle argument, with classical
regularity and the limit equation supplied, not PDE existence or regularity.
-/
set_option autoImplicit false
namespace ChemotaxisBifurcation.IntervalStrongPositivity
open Set Filter Topology
noncomputable section

theorem linear_drift_eq_zero {L : ℝ} {y z a b : ℝ → ℝ}
    (hy : ∀ x ∈ Icc 0 L, HasDerivWithinAt y (z x) (Icc 0 L) x)
    (hz : ∀ x ∈ Icc 0 L, HasDerivWithinAt z (a x * y x + b x * z x) (Icc 0 L) x)
    (ha : ContinuousOn a (Icc 0 L)) (hb : ContinuousOn b (Icc 0 L)) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc 0 L)
    (hy0 : y x₀ = 0) (hz0 : z x₀ = 0) :
    ∀ x ∈ Icc 0 L, y x = 0 ∧ z x = 0 := by
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hb
  set K : NNReal := Real.toNNReal (max 1 (A + B)) with hK
  have hKval : (K : ℝ) = max 1 (A + B) := Real.coe_toNNReal _ (le_trans zero_le_one (le_max_left _ _))
  set V : ℝ → ℝ × ℝ → ℝ × ℝ := fun t p => (p.2, a t * p.1 + b t * p.2) with hV
  have hLip : ∀ t ∈ Icc 0 L, LipschitzOnWith K (V t) univ := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun p _ q _ => ?_
    simp only [hV, Prod.dist_eq, Real.dist_eq, hKval]
    have hat : |a t| ≤ A := by simpa using hA t ht
    have h1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
    have h2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
    have h0 : 0 ≤ max |p.1 - q.1| |p.2 - q.2| := le_trans (abs_nonneg _) h1
    refine max_le ?_ ?_
    · calc |p.2 - q.2| ≤ 1 * max |p.1 - q.1| |p.2 - q.2| := by linarith
        _ ≤ max 1 (A + B) * max |p.1 - q.1| |p.2 - q.2| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    · have hbt : |b t| ≤ B := by simpa using hB t ht
      have hA0 : 0 ≤ A := (abs_nonneg _).trans hat
      have hB0 : 0 ≤ B := (abs_nonneg _).trans hbt
      calc |a t * p.1 + b t * p.2 - (a t * q.1 + b t * q.2)|
          = |a t * (p.1 - q.1) + b t * (p.2 - q.2)| := by congr 1; ring
        _ ≤ |a t * (p.1 - q.1)| + |b t * (p.2 - q.2)| := abs_add_le _ _
        _ = |a t| * |p.1 - q.1| + |b t| * |p.2 - q.2| := by rw [abs_mul, abs_mul]
        _ ≤ A * max |p.1 - q.1| |p.2 - q.2| + B * max |p.1 - q.1| |p.2 - q.2| :=
          add_le_add (mul_le_mul hat h1 (abs_nonneg _) hA0)
            (mul_le_mul hbt h2 (abs_nonneg _) hB0)
        _ = (A + B) * max |p.1 - q.1| |p.2 - q.2| := by ring
        _ ≤ max 1 (A + B) * max |p.1 - q.1| |p.2 - q.2| :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) h0
  set f : ℝ → ℝ × ℝ := fun x => (y x, z x) with hf
  have hfd : ∀ x ∈ Icc 0 L, HasDerivWithinAt f (V x (f x)) (Icc 0 L) x :=
    fun x hx => (hy x hx).prodMk (hz x hx)
  have hfc : ContinuousOn f (Icc 0 L) := fun x hx => (hfd x hx).continuousWithinAt
  have hgd : ∀ x : ℝ, HasDerivWithinAt (fun _ : ℝ => (0 : ℝ × ℝ)) (V x 0) (Icc 0 L) x := by
    intro x
    have : V x 0 = 0 := by simp [hV]
    rw [this]; exact hasDerivWithinAt_const _ _ _
  have hgc : ContinuousOn (fun _ : ℝ => (0 : ℝ × ℝ)) (Icc 0 L) := continuousOn_const
  have hEq0 : f x₀ = 0 := by simp [hf, hy0, hz0]
  have hright : EqOn f (fun _ => (0 : ℝ × ℝ)) (Icc x₀ L) := by
    have hsub : Icc x₀ L ⊆ Icc 0 L := Icc_subset_Icc_left hx₀.1
    have hsub' : ∀ t ∈ Ico x₀ L, t ∈ Ico 0 L := fun t ht => ⟨hx₀.1.trans ht.1, ht.2⟩
    refine ODE_solution_unique_of_mem_Icc_right (v := V) (s := fun _ => univ) (K := K)
      (fun t ht => hLip t (Ico_subset_Icc_self (hsub' t ht)))
      (hfc.mono hsub) (fun t ht => ?_) (fun _ _ => mem_univ _)
      (hgc.mono hsub) (fun t ht => ?_) (fun _ _ => mem_univ _) hEq0
    · exact (hfd t (Ico_subset_Icc_self (hsub' t ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem (hsub' t ht))
    · exact (hgd t).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem (hsub' t ht))
  have hleft : EqOn f (fun _ => (0 : ℝ × ℝ)) (Icc 0 x₀) := by
    have hsub : Icc 0 x₀ ⊆ Icc 0 L := Icc_subset_Icc_right hx₀.2
    have hsub' : ∀ t ∈ Ioc 0 x₀, t ∈ Ioc 0 L := fun t ht => ⟨ht.1, ht.2.trans hx₀.2⟩
    refine ODE_solution_unique_of_mem_Icc_left (v := V) (s := fun _ => univ) (K := K)
      (fun t ht => hLip t (Ioc_subset_Icc_self (hsub' t ht)))
      (hfc.mono hsub) (fun t ht => ?_) (fun _ _ => mem_univ _)
      (hgc.mono hsub) (fun t ht => ?_) (fun _ _ => mem_univ _) hEq0
    · exact (hfd t (Ioc_subset_Icc_self (hsub' t ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem (hsub' t ht))
    · exact (hgd t).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem (hsub' t ht))
  intro x hx
  have hfx : f x = 0 := by
    rcases le_total x x₀ with h | h
    · exact hleft ⟨hx.1, h⟩
    · exact hright ⟨h, hx.2⟩
  simp only [hf, Prod.mk_eq_zero] at hfx
  exact hfx


/-- A nonnegative classical solution of a homogeneous linear second-order
interval equation, with Neumann endpoint data and one positive value, is
strictly positive everywhere. Coefficients need no sign condition. -/
theorem positive_of_nonnegative {L : ℝ} (_hL : 0 < L)
    {u du a b : ℝ → ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (du x) (Icc 0 L) x)
    (hdu : ∀ x ∈ Icc 0 L,
      HasDerivWithinAt du (a x * u x + b x * du x) (Icc 0 L) x)
    (ha : ContinuousOn a (Icc 0 L)) (hb : ContinuousOn b (Icc 0 L))
    (h0 : du 0 = 0) (h1 : du L = 0)
    (hnonneg : ∀ x ∈ Icc 0 L, 0 ≤ u x)
    (hpos : ∃ x ∈ Icc 0 L, 0 < u x) :
    ∀ x ∈ Icc 0 L, 0 < u x := by
  intro x hx
  by_contra hnot
  have huz : u x = 0 := le_antisymm (not_lt.mp hnot) (hnonneg x hx)
  have hduz : du x = 0 := by
    by_cases hx0 : x = 0
    · simpa [hx0] using h0
    by_cases hx1 : x = L
    · simpa [hx1] using h1
    have hxint : x ∈ Ioo 0 L := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),
      lt_of_le_of_ne hx.2 hx1⟩
    have hmin : IsLocalMin u x := by
      filter_upwards [Icc_mem_nhds hxint.1 hxint.2] with t ht
      rw [huz]
      exact hnonneg t ht
    exact hmin.hasDerivAt_eq_zero
      ((hu x hx).hasDerivAt (Icc_mem_nhds hxint.1 hxint.2))
  obtain ⟨y, hy, hpositive⟩ := hpos
  have hyz := (linear_drift_eq_zero hu hdu ha hb hx huz hduz y hy).1
  linarith


/-- Classical limit-equation data, not a positivity hypothesis. The equation
is `u'' = a*u + b*u'`, equivalently the homogeneous linear elliptic equation.
One-sided derivative statements at endpoints express classical regularity. -/
structure LinearNeumannProfile (L : ℝ) where
  u : ℝ → ℝ
  du : ℝ → ℝ
  a : ℝ → ℝ
  b : ℝ → ℝ
  derivative_u : ∀ x ∈ Icc 0 L, HasDerivWithinAt u (du x) (Icc 0 L) x
  derivative_du : ∀ x ∈ Icc 0 L,
    HasDerivWithinAt du (a x * u x + b x * du x) (Icc 0 L) x
  continuous_a : ContinuousOn a (Icc 0 L)
  continuous_b : ContinuousOn b (Icc 0 L)
  neumann_left : du 0 = 0
  neumann_right : du L = 0

/-- Ambient admissibility with the strong maximum principle discharged by
ODE uniqueness. Limit passage, phase-space continuity, zero-sensitivity
uniqueness and local implicit-function uniqueness remain explicit inputs. -/
theorem closure_subset_admissible_of_linear_ode
    {E : Type*} [TopologicalSpace E] {L : ℝ} (hL : 0 < L)
    {prof : E → C(Icc (0 : ℝ) L, ℝ)} {Aff : Set E} {S Sol : Set (ℝ × E)}
    {uStar : E} {cStar : ℝ}
    (hProf : Continuous prof) (hAff : IsClosed Aff) (hc : 0 < cStar)
    (hS : S ⊆ AmbientClosure.admissibleSet prof Aff)
    (hSne : ∀ p ∈ S, p.2 ≠ uStar)
    (hMax : ∀ p ∈ S, ∃ x, cStar ≤ prof p.2 x)
    (hSSol : S ⊆ Sol) (hLimit : closure S ⊆ Sol)
    (d : ∀ p ∈ Sol, LinearNeumannProfile L)
    (hRep : ∀ p (hp : p ∈ Sol) (x : ℝ) (hx : x ∈ Icc 0 L),
      (d p hp).u x = prof p.2 ⟨x, hx⟩)
    (hZero : ∀ u, ((0 : ℝ), u) ∈ Sol → u ∈ Aff →
      (∀ x, 0 < prof u x) → u = uStar)
    (hIFT : ∀ᶠ p in nhds ((0 : ℝ), uStar), p ∈ Sol → p.2 = uStar) :
    closure S ⊆ AmbientClosure.admissibleSet prof Aff := by
  apply AmbientClosure.closure_subset_admissible hProf hAff hc hS hSne hMax
    hSSol hLimit ?_ hZero hIFT
  intro p hp _ _ hnonneg hpos x
  have hnn : ∀ y ∈ Icc 0 L, 0 ≤ (d p hp).u y := by
    intro y hy
    rw [hRep p hp y hy]
    exact hnonneg ⟨y, hy⟩
  have hpositive : ∃ y ∈ Icc 0 L, 0 < (d p hp).u y := by
    obtain ⟨y, hy⟩ := hpos
    exact ⟨y, y.property, by rw [hRep p hp y y.property]; exact hy⟩
  have hout := positive_of_nonnegative hL (d p hp).derivative_u
    (d p hp).derivative_du (d p hp).continuous_a (d p hp).continuous_b
    (d p hp).neumann_left (d p hp).neumann_right hnn hpositive x x.property
  rwa [hRep p hp x x.property] at hout

end
end ChemotaxisBifurcation.IntervalStrongPositivity
