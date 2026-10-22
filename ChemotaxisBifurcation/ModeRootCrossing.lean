module
public import ChemotaxisBifurcation.OddRootCrossing
public import ChemotaxisBifurcation.ModeRealization

@[expose] public section

/-!
# Root crossings along actual mode intervals

The Neumann eigenvalue decreases strictly with positive domain length. Local
polynomial sign changes therefore give local coefficient changes inside an
admissible strict-mode interval, with reversed eigenvalue orientation.
-/
namespace ChemotaxisBifurcation.ModeRootCrossing

open Filter ModeIntervals PhysicalModeGuards OddRootCrossing PhysicalPolynomial
open scoped Topology
noncomputable section

theorem continuumLam_strictAntiOn_positive (n : ℕ) (hn : 0 < n) :
    StrictAntiOn (fun L : ℝ => Semidiscrete.continuumLam L n) (Set.Ioi 0) := by
  intro L hL M hM hLM
  have ha : 0 < (n : ℝ) * Real.pi := by positivity
  change (((n : ℝ) * Real.pi) / M) ^ 2 < (((n : ℝ) * Real.pi) / L) ^ 2
  exact (sq_lt_sq₀ (div_pos ha hM).le (div_pos ha hL).le).mpr
    (div_lt_div_of_pos_left ha hL hLM)

theorem continuumLam_continuousAt_positive (n : ℕ) (L : ℝ) (hL : 0 < L) :
    ContinuousAt (fun z : ℝ => Semidiscrete.continuumLam z n) L := by
  exact (continuousAt_const.div continuousAt_id hL.ne').pow 2

/-- An odd-multiplicity root inside an actual mode interval produces a domain
length sign switch; every nearby length used remains in that same mode. -/
theorem physical_mode_local_sign_change_of_odd_rootMultiplicity
    (p : PhysicalParams) (d : ModeData) (beta : ℝ)
    (hp : p.LogisticAdmissible) (hs : StrictCriticalMode p d beta)
    (hP : paperNumeratorPoly p beta ≠ 0)
    (hodd : Odd ((paperNumeratorPoly p beta).rootMultiplicity d.eigenvalue)) :
    ∃ U : Set ℝ, U ∈ 𝓝 d.L ∧
      (∀ L ∈ U, StrictCriticalMode p ⟨L, d.n0⟩ beta) ∧
      ∀ L ∈ U, ∀ M ∈ U, L < d.L → d.L < M →
        logisticBetaCoefficient p (Semidiscrete.continuumLam L d.n0) beta *
          logisticBetaCoefficient p (Semidiscrete.continuumLam M d.n0) beta < 0 := by
  let r := CoefficientLimits.balancingEigenvalue p
  have hmode := logistic_positive_parameters p hp
  have hr : 0 < r := CoefficientLimits.balancingEigenvalue_pos p hp
  have hrsq : r ^ 2 = p.logisticSlope * p.mu :=
    CoefficientLimits.balancingEigenvalue_sq p hp
  have hinterval := (physical_critical_length_iff p d beta r
    hmode hs.1 hs.2.1 hr hrsq).mp hs
  rcases physical_coefficient_local_sign_change_of_odd_rootMultiplicity
    p beta d.eigenvalue hp hP hodd with ⟨V, hV, hcross⟩
  have hpre : {L : ℝ | Semidiscrete.continuumLam L d.n0 ∈ V} ∈ 𝓝 d.L :=
    (continuumLam_continuousAt_positive d.n0 d.L hs.1).eventually hV
  let U := {L : ℝ | Semidiscrete.continuumLam L d.n0 ∈ V} ∩
    Set.Ioo (criticalLength r (d.n0 - 1)) (criticalLength r d.n0)
  have hU : U ∈ 𝓝 d.L := inter_mem hpre (isOpen_Ioo.mem_nhds hinterval)
  have hpos : ∀ L ∈ U, 0 < L := by
    intro L hL
    exact lt_of_le_of_lt (criticalLength_nonneg r (d.n0 - 1)) hL.2.1
  have hstrict : ∀ L ∈ U, StrictCriticalMode p ⟨L, d.n0⟩ beta := by
    intro L hL
    exact (physical_critical_length_iff p ⟨L, d.n0⟩ beta r
      hmode (hpos L hL) hs.2.1 hr hrsq).mpr hL.2
  refine ⟨U, hU, hstrict, ?_⟩
  intro L hL M hM hLd hdM
  have hanti := continuumLam_strictAntiOn_positive d.n0 hs.2.1
  have hleft : Semidiscrete.continuumLam M d.n0 < d.eigenvalue :=
    hanti hs.1 (hpos M hM) hdM
  have hright : d.eigenvalue < Semidiscrete.continuumLam L d.n0 :=
    hanti (hpos L hL) hs.1 hLd
  have hMrange := physical_critical_fixed_lower p ⟨M, d.n0⟩ beta r
    hmode (hstrict M hM) hr hrsq
  have hLrange := physical_critical_fixed_lower p ⟨L, d.n0⟩ beta r
    hmode (hstrict L hL) hr hrsq
  have hc := hcross _ hM.1 _ hL.1 hMrange hLrange hleft hright
  simpa [mul_comm] using hc

/-- Even multiplicity preserves the local coefficient sign throughout a
punctured neighborhood inside the same strict-mode interval. -/
theorem physical_mode_local_same_sign_of_even_rootMultiplicity
    (p : PhysicalParams) (d : ModeData) (beta : ℝ)
    (hp : p.LogisticAdmissible) (hs : StrictCriticalMode p d beta)
    (hP : paperNumeratorPoly p beta ≠ 0)
    (heven : Even ((paperNumeratorPoly p beta).rootMultiplicity d.eigenvalue)) :
    ∃ U : Set ℝ, U ∈ 𝓝 d.L ∧
      (∀ L ∈ U, StrictCriticalMode p ⟨L, d.n0⟩ beta) ∧
      ∀ L ∈ U, ∀ M ∈ U, L ≠ d.L → M ≠ d.L →
        0 < logisticBetaCoefficient p (Semidiscrete.continuumLam L d.n0) beta *
          logisticBetaCoefficient p (Semidiscrete.continuumLam M d.n0) beta := by
  let r := CoefficientLimits.balancingEigenvalue p
  have hmode := logistic_positive_parameters p hp
  have hr : 0 < r := CoefficientLimits.balancingEigenvalue_pos p hp
  have hrsq : r ^ 2 = p.logisticSlope * p.mu :=
    CoefficientLimits.balancingEigenvalue_sq p hp
  have hinterval := (physical_critical_length_iff p d beta r
    hmode hs.1 hs.2.1 hr hrsq).mp hs
  rcases physical_coefficient_local_same_sign_of_even_rootMultiplicity
    p beta d.eigenvalue hp hP heven with ⟨V, hV, hsame⟩
  have hpre : {L : ℝ | Semidiscrete.continuumLam L d.n0 ∈ V} ∈ 𝓝 d.L :=
    (continuumLam_continuousAt_positive d.n0 d.L hs.1).eventually hV
  let U := {L : ℝ | Semidiscrete.continuumLam L d.n0 ∈ V} ∩
    Set.Ioo (criticalLength r (d.n0 - 1)) (criticalLength r d.n0)
  have hU : U ∈ 𝓝 d.L := inter_mem hpre (isOpen_Ioo.mem_nhds hinterval)
  have hpos : ∀ L ∈ U, 0 < L := by
    intro L hL
    exact lt_of_le_of_lt (criticalLength_nonneg r (d.n0 - 1)) hL.2.1
  have hstrict : ∀ L ∈ U, StrictCriticalMode p ⟨L, d.n0⟩ beta := by
    intro L hL
    exact (physical_critical_length_iff p ⟨L, d.n0⟩ beta r
      hmode (hpos L hL) hs.2.1 hr hrsq).mpr hL.2
  refine ⟨U, hU, hstrict, ?_⟩
  intro L hL M hM hLd hMd
  have hinj := ModeRootCounts.eigenvalue_injOn_positive d.n0 hs.2.1
  have hleft : Semidiscrete.continuumLam L d.n0 ≠ d.eigenvalue := by
    intro he
    exact hLd (hinj (hpos L hL) hs.1 he)
  have hright : Semidiscrete.continuumLam M d.n0 ≠ d.eigenvalue := by
    intro he
    exact hMd (hinj (hpos M hM) hs.1 he)
  have hLrange := physical_critical_fixed_lower p ⟨L, d.n0⟩ beta r
    hmode (hstrict L hL) hr hrsq
  have hMrange := physical_critical_fixed_lower p ⟨M, d.n0⟩ beta r
    hmode (hstrict M hM) hr hrsq
  exact hsame _ hL.1 _ hM.1 hLrange hMrange hleft hright

/-- The exceptional zero numerator means the coefficient vanishes throughout
its admissible range, not that it has an empty set of real zeros. -/
theorem physical_coefficient_zero_of_zero_numerator
    (p : PhysicalParams) (x beta : ℝ) (hp : p.LogisticAdmissible)
    (hx : Real.sqrt (p.logisticSlope * p.mu) / 2 < x)
    (hP : paperNumeratorPoly p beta = 0) :
    logisticBetaCoefficient p x beta = 0 := by
  apply (ModeRootCounts.physical_coefficient_zero_iff p x beta hp hx).mpr
  simp [hP]

end
end ChemotaxisBifurcation.ModeRootCrossing
