module
public import ChemotaxisBifurcation.ClassicalSpikeSubsequence

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.ClassicalSpikeInterface
open Set MeasureTheory Filter Topology
noncomputable section

/-- Mathlib-vocabulary interface for the actual stationary-system limit lemma.
All flux/derivative witnesses are ordinary classical solution data; no mass,
first-integral, extraction, weak density or limiting equation is assumed. -/
theorem classical_all_test_subsequence
    (L a b alpha gamma mu nu m beta r R : ℝ) (chi : ℕ → ℝ)
    (u du ddu v dv ddv dJ : ℕ → ℝ → ℝ)
    (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) (halpha : 0 < alpha)
    (hg : 0 < gamma) (hmu : 0 < mu) (hnu : 0 < nu)
    (hm : 0 < m) (hbeta : 0 ≤ beta) (hr : 1 < r) (hgr : gamma < r) (hR : 0 ≤ R)
    (hchi : Tendsto chi atTop atTop)
    (huc : ∀ n, ContinuousOn (u n) (Icc 0 L))
    (hduc : ∀ n, ContinuousOn (du n) (Icc 0 L))
    (hvc : ∀ n, ContinuousOn (v n) (Icc 0 L))
    (hdvc : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hddvc : ∀ n, ContinuousOn (ddv n) (Icc 0 L))
    (hup : ∀ n x, x ∈ Icc 0 L → 0 < u n x)
    (hvp : ∀ n x, x ∈ Icc 0 L → 0 < v n x)
    (hdu : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (u n) (du n x) x)
    (hddu : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (du n) (ddu n x) x)
    (hdv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x)
    (hddv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (hdJ : ∀ n x, x ∈ Ioo 0 L →
      HasDerivAt (fun y => chi n*(u n y^m/(1+v n y)^beta)*dv n y) (dJ n x) x)
    (hpop : ∀ n x, x ∈ Ioo 0 L → ddu n x-dJ n x+a*u n x-b*u n x^(1+alpha)=0)
    (hsig : ∀ n x, x ∈ Ioo 0 L → ddv n x-mu*v n x+nu*u n x^gamma=0)
    (hu0 : ∀ n, du n 0=0) (huL : ∀ n, du n L=0)
    (hv0 : ∀ n, dv n 0=0) (hvL : ∀ n, dv n L=0)
    (hbound : ∀ n, ∫ x in (0 : ℝ)..L, u n x^r ≤ R) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ c : ℝ, 0 ≤ c ∧
      TendstoUniformlyOn (fun n => v (phi n)) (fun _ => nu/mu*c) atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => dv (phi n)) (fun _ => 0) atTop (Icc 0 L) ∧
      (∀ x y, 0 ≤ x → x ≤ y → y ≤ L →
        Tendsto (fun n => ∫ z in x..y, u (phi n) z^gamma) atTop (𝓝 (c*(y-x)))) ∧
      ∀ g : Lp ℝ (ENNReal.ofReal ((r/gamma)/(r/gamma-1))) ((Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume)),
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, u (phi n) x^gamma*g x
          ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume)) atTop
          (𝓝 (∫ x : Icc (0 : ℝ) L, c*g x ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume))) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, v (phi n) x*g x
          ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume)) atTop
          (𝓝 (∫ x : Icc (0 : ℝ) L, (nu/mu*c)*g x ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume))) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, dv (phi n) x*g x
          ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume)) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, ddv (phi n) x*g x
          ∂(Measure.comap (Subtype.val : Icc (0 : ℝ) L → ℝ) volume)) atTop (𝓝 0) := by
  let p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta := fun n => {
    u := u n
    v := v n
    du := du n
    ddu := ddu n
    dv := dv n
    dJ := dJ n
    continuous_u := huc n
    continuous_du := hduc n
    continuous_flux := by
      exact ((continuousOn_const.mul (((huc n).rpow_const fun x hx => Or.inl (hup n x hx).ne').div
        ((continuousOn_const.add (hvc n)).rpow_const fun x hx => Or.inl (show (1 : ℝ)+v n x ≠ 0 by linarith [hvp n x hx]))
        (fun x hx => (Real.rpow_pos_of_pos (show (0 : ℝ)<1+v n x by linarith [hvp n x hx]) beta).ne'))).mul (hdvc n))
    derivative_u := hdu n
    derivative_du := hddu n
    derivative_v := hdv n
    derivative_flux := hdJ n
    stationary := hpop n
    neumann_u_left := hu0 n
    neumann_u_right := huL n
    neumann_v_left := hv0 n
    neumann_v_right := hvL n }
  let s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma := fun n => {
    ddv := ddv n
    continuous_v := hvc n
    nonnegative_v := fun x hx => (hvp n x hx).le
    continuous_dv := hdvc n
    derivative_dv := hddv n
    stationary := hsig n }
  exact ClassicalSpikeSubsequence.exists_constant_signal_and_weak_tests p s
    hL ha hb halpha hg hmu hnu hm hbeta hr hgr hR hchi hup hvp hddvc hbound

end
end ChemotaxisBifurcation.ClassicalSpikeInterface
