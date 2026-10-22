module
public import ChemotaxisBifurcation.ClassicalStationaryHolder

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalHolderNorm
open Real Set MeasureTheory Filter Topology ClassicalStationaryHolder
noncomputable section

/-- Actual supremum norm of a scalar representative on the closed interval. -/
def supAbs (L : ℝ) (f : ℝ → ℝ) : ℝ := sSup ((fun x => |f x|) '' Icc 0 L)

/-- Actual Hölder seminorm as the supremum of the difference quotients. -/
def holderSeminorm (L theta : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup {q : ℝ | ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, x ≠ y ∧ q = |f y-f x|/|y-x|^theta}

/-- Standard one-dimensional C2+theta norm on actual classical representatives:
three supremum norms plus the second derivative Hölder seminorm. -/
def c2HolderNorm (L theta : ℝ) (u du ddu : ℝ → ℝ) : ℝ :=
  supAbs L u + supAbs L du + supAbs L ddu + holderSeminorm L theta ddu

theorem supAbs_le {L C : ℝ} {f : ℝ → ℝ} (hL : 0 ≤ L)
    (h : ∀ x ∈ Icc 0 L, |f x| ≤ C) : supAbs L f ≤ C := by
  apply csSup_le
  · exact ⟨|f 0|,0,⟨le_rfl,hL⟩,rfl⟩
  · rintro z ⟨x,hx,rfl⟩
    exact h x hx

theorem holderSeminorm_le {L theta C : ℝ} {f : ℝ → ℝ} (hL : 0 < L)
    (h : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L, |f y-f x| ≤ C*|y-x|^theta) :
    holderSeminorm L theta f ≤ C := by
  apply csSup_le
  · exact ⟨|f L-f 0|/|L-0|^theta,0,⟨le_rfl,hL.le⟩,L,⟨hL.le,le_rfl⟩,hL.ne,rfl⟩
  · rintro z ⟨x,hx,y,hy,hxy,rfl⟩
    have hd : 0 < |y-x|^theta := Real.rpow_pos_of_pos
      (abs_pos.mpr (sub_ne_zero.mpr hxy.symm)) _
    exact (div_le_iff₀ hd).mpr (h x hx y hy)

/-- The explicit actual derivative criterion bounds both standard C2+theta
norms. The harmless factor four changes only the uniform constant. -/
theorem norm_bound_of_criterion {L theta C : ℝ} {u du ddu v dv ddv : ℝ → ℝ}
    (hL : 0 < L) (h : C2HolderBound L theta C u du ddu v dv ddv) :
    c2HolderNorm L theta u du ddu ≤ 4*C ∧ c2HolderNorm L theta v dv ddv ≤ 4*C := by
  have hu := supAbs_le hL.le (fun x hx => (h.1 x hx).1)
  have hdu := supAbs_le hL.le (fun x hx => (h.1 x hx).2.1)
  have hddu := supAbs_le hL.le (fun x hx => (h.1 x hx).2.2.1)
  have hv := supAbs_le hL.le (fun x hx => (h.1 x hx).2.2.2.1)
  have hdv := supAbs_le hL.le (fun x hx => (h.1 x hx).2.2.2.2.1)
  have hddv := supAbs_le hL.le (fun x hx => (h.1 x hx).2.2.2.2.2)
  have hhdu := holderSeminorm_le hL (fun x hx y hy => (h.2 x hx y hy).1)
  have hhdv := holderSeminorm_le hL (fun x hx y hy => (h.2 x hx y hy).2)
  constructor <;> dsimp [c2HolderNorm] <;> linarith

/-- Parameter-uniform bounds of the actual standard C2+theta norms for the
literal logistic stationary system, throughout the full manuscript range. -/
theorem logistic_uniform_norm_bound {L a b alpha m beta mu nu gamma X : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha) :
    ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
      ∀ (chi : ℝ) (q : PhysicalStrongPositivity.StationaryProfile L a b alpha chi m beta),
      (∀ x ∈ Icc 0 L, 0 ≤ q.v x) → q.dv 0 = 0 → q.dv L = 0 →
      (∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) →
      |chi| ≤ X → (∀ x ∈ Icc 0 L, 0 < q.u x) →
      (∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, q.u x ≠ q.u y) →
      c2HolderNorm L theta q.u q.du q.ddu ≤ C ∧ c2HolderNorm L theta q.v q.dv q.ddv ≤ C := by
  obtain ⟨theta,ht,C,hC,hall⟩ := logistic_uniform_physical_C2_holder hL ha hb halpha hm hm1 hbeta
    hmu hnu hgamma hgamma1 (X := X)
  refine ⟨theta,ht,4*C,by positivity,?_⟩
  intro chi q hv hN0 hNL heq hchi hpos hnonconst
  exact norm_bound_of_criterion hL (hall chi q hv hN0 hNL heq hchi hpos hnonconst)

/-- Parameter-uniform bounds of the actual standard C2+theta norms for the
prescribed-mass minimal stationary system, including m=2. -/
theorem minimal_uniform_norm_bound {L m beta mu nu gamma X uStar : ℝ}
    (hL : 0 < L) (hm : 1 ≤ m) (hm1 : m ≤ 2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) :
    ∃ theta ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
      ∀ (chi : ℝ) (q : PhysicalStrongPositivity.StationaryProfile L 0 0 0 chi m beta),
      (∀ x ∈ Icc 0 L, 0 ≤ q.v x) → q.dv 0 = 0 → q.dv L = 0 →
      (∀ x ∈ Ioo 0 L, q.ddv x-mu*q.v x+nu*q.u x^gamma = 0) →
      |chi| ≤ X → (∀ x ∈ Icc 0 L, 0 < q.u x) →
      (∫ x in (0 : ℝ)..L, q.u x) = L*uStar →
      c2HolderNorm L theta q.u q.du q.ddu ≤ C ∧ c2HolderNorm L theta q.v q.dv q.ddv ≤ C := by
  obtain ⟨theta,ht,C,hC,hall⟩ := minimal_uniform_physical_C2_holder hL hm hm1 hbeta
    hmu hnu hgamma hgamma1 (X := X) (uStar := uStar)
  refine ⟨theta,ht,4*C,by positivity,?_⟩
  intro chi q hv hN0 hNL heq hchi hpos hmass
  exact norm_bound_of_criterion hL (hall chi q hv hN0 hNL heq hchi hpos hmass)

end
end ChemotaxisBifurcation.ClassicalHolderNorm
