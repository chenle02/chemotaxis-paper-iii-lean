module
public import ChemotaxisBifurcation.SignalSpikeSubsequence
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Dense polynomial tests and full conjugate Lp testing

Pinned Weierstrass approximation and dense continuous functions in Lp turn
uniformly bounded polynomial-tested pairings into every conjugate-Lp test.
No reflexive-space extraction or Lp dual representation is assumed.
-/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal
namespace ChemotaxisBifurcation.SignalWeakTesting
noncomputable section

/-- Uniformly bounded Lp pairings that converge on a dense test set converge
on every conjugate-Lq test. -/
theorem all_Lp_tests_of_dense_tests
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (f : ℕ → Lp ℝ p μ) (fc : Lp ℝ p μ) (A : ℝ)
    (hbound : ∀ n, ‖f n‖ ≤ A) (S : Set (Lp ℝ q μ)) (hS : Dense S)
    (htest : ∀ g ∈ S,
      Tendsto (fun n => ∫ x, f n x * g x ∂μ) atTop (𝓝 (∫ x, fc x * g x ∂μ))) :
    ∀ g : Lp ℝ q μ,
      Tendsto (fun n => ∫ x, f n x * g x ∂μ) atTop (𝓝 (∫ x, fc x * g x ∂μ)) := by
  let P := (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q
  let T := fun n => P (f n)
  let Tc := P fc
  have hK : ∀ n, ‖T n‖ ≤ ‖P‖ * A := by
    intro n
    exact (P.le_opNorm (f n)).trans (mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg P))
  have hequi : Equicontinuous (fun n g => T n g) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => (‖P‖ * A) * t)
      (by simpa only [mul_zero, id_eq] using
        tendsto_const_nhds.mul (tendsto_id (α := ℝ) (x := (𝓝 0))))
    intro x y n
    exact ((T n).dist_le_opNorm x y).trans (mul_le_mul_of_nonneg_right (hK n) dist_nonneg)
  have hc : IsClosed {g : Lp ℝ q μ | Tendsto (fun n => T n g) atTop (𝓝 (Tc g))} :=
    hequi.isClosed_setOfPred_tendsto Tc.continuous
  have hs : S ⊆ {g : Lp ℝ q μ | Tendsto (fun n => T n g) atTop (𝓝 (Tc g))} := by
    intro g hg
    simpa only [Set.mem_ofPred_eq, T, Tc, P, ContinuousLinearMap.lpPairing_eq_integral,
      ContinuousLinearMap.mul_apply'] using htest g hg
  intro g
  have ht := (closure_minimal hs hc) (hS g)
  simpa only [T, Tc, P, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply', Set.mem_ofPred_eq] using ht

/-- Bounded-continuous tested convergence plus uniform actual Lp norm control
implies every conjugate-Lq integral test. -/
theorem all_Lp_tests_of_boundedContinuous_tests
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hq : q ≠ ∞) (f : ℕ → Lp ℝ p μ) (fc : Lp ℝ p μ) (A : ℝ)
    (hbound : ∀ n, ‖f n‖ ≤ A)
    (htest : ∀ g : X →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f n x * g x ∂μ) atTop (𝓝 (∫ x, fc x * g x ∂μ))) :
    ∀ g : Lp ℝ q μ,
      Tendsto (fun n => ∫ x, f n x * g x ∂μ) atTop (𝓝 (∫ x, fc x * g x ∂μ)) := by
  apply all_Lp_tests_of_dense_tests μ p q f fc A hbound
    (range (BoundedContinuousFunction.toLp q μ ℝ : (X →ᵇ ℝ) →L[ℝ] Lp ℝ q μ))
    (BoundedContinuousFunction.toLp_denseRange ℝ μ ℝ hq)
  rintro g ⟨g, rfl⟩
  have heq : ∀ F : Lp ℝ p μ,
      (∫ x, F x * (BoundedContinuousFunction.toLp q μ ℝ g) x ∂μ) = ∫ x, F x * g x ∂μ := by
    intro F
    apply integral_congr_ae
    filter_upwards [BoundedContinuousFunction.coeFn_toLp q μ ℝ g] with x hx
    rw [hx]
  simpa only [heq] using htest g

/-- Polynomial tests are dense in conjugate Lq on the compact interval.
This is a full Lp-test conclusion, not only weak-measure convergence. -/
theorem all_Lp_tests_of_polynomial_tests {L : ℝ}
    (μ : Measure (Icc (0 : ℝ) L)) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hq : q ≠ ∞) (f : ℕ → Lp ℝ p μ) (fc : Lp ℝ p μ) (A : ℝ)
    (hbound : ∀ n, ‖f n‖ ≤ A)
    (htest : ∀ P : Polynomial ℝ,
      Tendsto (fun n => ∫ x, f n x * P.eval (x : ℝ) ∂μ) atTop
        (𝓝 (∫ x, fc x * P.eval (x : ℝ) ∂μ))) :
    ∀ g : Lp ℝ q μ,
      Tendsto (fun n => ∫ x, f n x * g x ∂μ) atTop (𝓝 (∫ x, fc x * g x ∂μ)) := by
  let e := ContinuousMap.toLp q μ ℝ (E := ℝ)
  let poly := Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) L)
  have hdpoly : DenseRange poly := by
    rw [denseRange_iff_closure_range]
    rw [show range poly = (polynomialFunctions (Icc (0 : ℝ) L) : Set C(Icc (0 : ℝ) L, ℝ)) by
      exact (polynomialFunctions_coe (Icc (0 : ℝ) L)).symm]
    change ((polynomialFunctions (Icc (0 : ℝ) L)).topologicalClosure : Set C(Icc (0 : ℝ) L, ℝ)) = univ
    rw [polynomialFunctions_closure_eq_top]
    rfl
  have hdense := (ContinuousMap.toLp_denseRange ℝ μ ℝ hq).comp hdpoly e.continuous
  apply all_Lp_tests_of_dense_tests μ p q f fc A hbound (range (e ∘ poly)) hdense
  rintro g ⟨P, rfl⟩
  have heq : ∀ F : Lp ℝ p μ,
      (∫ x, F x * (e (poly P)) x ∂μ) = ∫ x, F x * P.eval (x : ℝ) ∂μ := by
    intro F
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := q) μ (poly P)] with x hx
    rw [hx]
    rfl
  simpa only [Function.comp_apply, heq] using htest P
end
end ChemotaxisBifurcation.SignalWeakTesting
