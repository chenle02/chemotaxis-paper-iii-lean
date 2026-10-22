module
public import ChemotaxisBifurcation.PhysicalPolynomial
public import ChemotaxisBifurcation.Semidiscrete
public import ChemotaxisBifurcation.CoefficientLimits

@[expose] public section

/-!
# Root counts along a fixed positive mode

A positive mode's eigenvalue is injective as a function of positive length.
Every finite family of distinct zero lengths therefore injects into the real
roots of the numerator polynomial. The nonzero-polynomial hypothesis is
explicit; the zero polynomial's empty formal roots multiset is not used to
claim a finite real zero set.
-/

namespace ChemotaxisBifurcation.ModeRootCounts

open Polynomial PhysicalPolynomial

noncomputable section

theorem eigenvalue_injOn_positive (n : ℕ) (hn : 0 < n) :
    Set.InjOn (fun L : ℝ => Semidiscrete.continuumLam L n) (Set.Ioi 0) := by
  intro L hL M hM heq
  have ha : 0 < (n : ℝ) * Real.pi := by positivity
  have hLpos : 0 < L := hL
  have hMpos : 0 < M := hM
  have hvL := div_pos ha hLpos
  have hvM := div_pos ha hMpos
  unfold Semidiscrete.continuumLam at heq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
  · have hc := (div_eq_div_iff hLpos.ne' hMpos.ne').mp h
    exact (mul_left_cancel₀ ha.ne' hc).symm
  · linarith

/-- Any finite family of distinct positive zero lengths has size bounded by
the numerator's degree. No finiteness of the full zero set is assumed. -/
theorem zero_lengths_card_le_degree (P : ℝ[X]) (hP : P ≠ 0)
    (n : ℕ) (hn : 0 < n) (S : Finset ℝ)
    (hpos : ∀ L ∈ S, 0 < L)
    (hzero : ∀ L ∈ S, P.eval (Semidiscrete.continuumLam L n) = 0) :
    S.card ≤ P.natDegree := by
  classical
  let f : ℝ → ℝ := fun L => Semidiscrete.continuumLam L n
  have hinj : Set.InjOn f (↑S : Set ℝ) := by
    intro L hL M hM heq
    exact eigenvalue_injOn_positive n hn (hpos L hL) (hpos M hM) heq
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  have hsub : S.image f ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hzero L hL
  calc
    S.card = (S.image f).card := hcard.symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le P.roots
    _ ≤ P.natDegree := Polynomial.card_roots' P

theorem paper_zero_lengths_card_le_five (p : PhysicalParams) (beta : ℝ)
    (hP : paperNumeratorPoly p beta ≠ 0) (n : ℕ) (hn : 0 < n)
    (S : Finset ℝ) (hpos : ∀ L ∈ S, 0 < L)
    (hzero : ∀ L ∈ S,
      (paperNumeratorPoly p beta).eval (Semidiscrete.continuumLam L n) = 0) :
    S.card ≤ 5 :=
  (zero_lengths_card_le_degree _ hP n hn S hpos hzero).trans
    (natDegree_paperNumeratorPoly_le p beta)

theorem paper_balanced_zero_lengths_card_le_four (p : PhysicalParams) (beta : ℝ)
    (hP : paperBalancedNumeratorPoly p beta ≠ 0) (n : ℕ) (hn : 0 < n)
    (S : Finset ℝ) (hpos : ∀ L ∈ S, 0 < L)
    (hzero : ∀ L ∈ S,
      (paperBalancedNumeratorPoly p beta).eval (Semidiscrete.continuumLam L n) = 0) :
    S.card ≤ 4 :=
  (zero_lengths_card_le_degree _ hP n hn S hpos hzero).trans
    (natDegree_paperBalancedNumeratorPoly_le p beta)

/-- The literal numerator and physical coefficient have the same positive sign. -/
theorem physical_coefficient_pos_iff (p : PhysicalParams) (x beta : ℝ)
    (hp : p.LogisticAdmissible) (hx : Real.sqrt (p.logisticSlope * p.mu) / 2 < x) :
    0 < logisticBetaCoefficient p x beta ↔ 0 < (paperNumeratorPoly p beta).eval x := by
  have hQ := paperDenominatorPoly_eval_pos p x beta hp hx
  rw [logisticBetaCoefficient_eq_paperRatio p x beta hp hx]
  constructor
  · intro h
    simpa using (lt_div_iff₀ hQ).mp h
  · intro h
    exact div_pos h hQ

theorem physical_coefficient_neg_iff (p : PhysicalParams) (x beta : ℝ)
    (hp : p.LogisticAdmissible) (hx : Real.sqrt (p.logisticSlope * p.mu) / 2 < x) :
    logisticBetaCoefficient p x beta < 0 ↔ (paperNumeratorPoly p beta).eval x < 0 := by
  have hQ := paperDenominatorPoly_eval_pos p x beta hp hx
  rw [logisticBetaCoefficient_eq_paperRatio p x beta hp hx]
  constructor
  · intro h
    simpa using (div_lt_iff₀ hQ).mp h
  · intro h
    exact div_neg_of_neg_of_pos h hQ

theorem physical_coefficient_zero_iff (p : PhysicalParams) (x beta : ℝ)
    (hp : p.LogisticAdmissible) (hx : Real.sqrt (p.logisticSlope * p.mu) / 2 < x) :
    logisticBetaCoefficient p x beta = 0 ↔ (paperNumeratorPoly p beta).eval x = 0 := by
  have hQ := paperDenominatorPoly_eval_pos p x beta hp hx
  rw [logisticBetaCoefficient_eq_paperRatio p x beta hp hx]
  constructor
  · intro h
    simpa using (div_eq_iff hQ.ne').mp h
  · intro h
    simp [h]

private theorem critical_admissible_range (p : PhysicalParams) (d : ModeData) (beta : ℝ)
    (hp : p.LogisticAdmissible) (hs : PhysicalModeGuards.StrictCriticalMode p d beta) :
    Real.sqrt (p.logisticSlope * p.mu) / 2 < d.eigenvalue := by
  exact ModeIntervals.physical_critical_fixed_lower p d beta
    (CoefficientLimits.balancingEigenvalue p)
    (PhysicalModeGuards.logistic_positive_parameters p hp) hs
    (CoefficientLimits.balancingEigenvalue_pos p hp)
    (CoefficientLimits.balancingEigenvalue_sq p hp)

/-- The actual physical coefficient has at most five distinct zero lengths
within one strict critical-mode interval, provided its numerator is nonzero. -/
theorem actual_zero_lengths_card_le_five (p : PhysicalParams) (beta : ℝ)
    (hp : p.LogisticAdmissible) (hP : paperNumeratorPoly p beta ≠ 0)
    (n : ℕ) (hn : 0 < n) (S : Finset ℝ)
    (hcritical : ∀ L ∈ S, PhysicalModeGuards.StrictCriticalMode p ⟨L, n⟩ beta)
    (hzero : ∀ L ∈ S, logisticBetaCoefficient p (Semidiscrete.continuumLam L n) beta = 0) :
    S.card ≤ 5 := by
  apply paper_zero_lengths_card_le_five p beta hP n hn S
    (fun L hL => (hcritical L hL).1)
  intro L hL
  have hx : Real.sqrt (p.logisticSlope * p.mu) / 2 < Semidiscrete.continuumLam L n :=
    critical_admissible_range p ⟨L, n⟩ beta hp (hcritical L hL)
  exact (physical_coefficient_zero_iff p _ beta hp hx).mp (hzero L hL)

/-- The balanced case inherits a four-zero bound from its actual cancellation,
with nonvanishing derived from the original numerator. -/
theorem actual_balanced_zero_lengths_card_le_four (p : PhysicalParams) (beta : ℝ)
    (hp : p.LogisticAdmissible) (hbalanced : p.logisticSlope = p.mu)
    (hP : paperNumeratorPoly p beta ≠ 0) (n : ℕ) (hn : 0 < n) (S : Finset ℝ)
    (hcritical : ∀ L ∈ S, PhysicalModeGuards.StrictCriticalMode p ⟨L, n⟩ beta)
    (hzero : ∀ L ∈ S, logisticBetaCoefficient p (Semidiscrete.continuumLam L n) beta = 0) :
    S.card ≤ 4 := by
  have hfac := (paperPolynomials_balanced_factor p beta hbalanced).1
  have hPb : paperBalancedNumeratorPoly p beta ≠ 0 := by
    intro h
    apply hP
    simpa [h] using hfac
  apply paper_balanced_zero_lengths_card_le_four p beta hPb n hn S
    (fun L hL => (hcritical L hL).1)
  intro L hL
  let x := Semidiscrete.continuumLam L n
  have hx : Real.sqrt (p.logisticSlope * p.mu) / 2 < x :=
    critical_admissible_range p ⟨L, n⟩ beta hp (hcritical L hL)
  have hz : (paperNumeratorPoly p beta).eval x = 0 :=
    (physical_coefficient_zero_iff p x beta hp hx).mp (hzero L hL)
  have heval := congrArg (fun Q : ℝ[X] => Q.eval x) hfac
  rw [Polynomial.eval_mul] at heval
  have hlin :
      (PolynomialDegree.RationalData.pPoly (RationalCoefficient.physicalRationalData p beta)).eval x =
        p.mu + x := by
    simp [PolynomialDegree.RationalData.pPoly, RationalCoefficient.physicalRationalData]
  rw [heval, hlin] at hz
  have hmode := PhysicalModeGuards.logistic_positive_parameters p hp
  have hxpos : 0 < x := Thresholds.continuumLam_pos L n (hcritical L hL).1 hn
  exact (mul_eq_zero.mp hz).resolve_left (add_pos hmode.mu_pos hxpos).ne'

end

end ChemotaxisBifurcation.ModeRootCounts
