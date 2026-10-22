module
public import ChemotaxisBifurcation.SignalWeakSobolev

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace ChemotaxisBifurcation.SignalWeakSubsequence
noncomputable section
open SignalWeakSource

/-- Complete existential constant-signal subsequence deduction for the
classical data: uniform C1 convergence, every interval source test, and every
conjugate-Lq test for the source and all three signal components. No extraction
or weak-source premise is assumed. Population first-integral and moment inputs
remain explicit upstream classical-equation deductions. -/
theorem exists_constant_C1_and_all_weak_tests_subsequence
    {L gamma m r beta kappa mu nu M Fb R : ℝ}
    {chi : ℕ → ℝ} {u du v dv ddv F : ℕ → ℝ → ℝ}
    (hL : 0 < L) (hγ : 0 < gamma) (hr : 1 < r) (hγr : gamma < r)
    (hm : 0 < m) (hkappa : 0 < kappa) (hmu : 0 < mu) (hnu : 0 < nu) (hR0 : 0 ≤ R)
    (hchi : Tendsto chi atTop atTop)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ x ∈ Icc 0 L, 0 ≤ u n x)
    (hdu : ∀ n, ∀ x ∈ Ioo 0 L, HasDerivAt (u n) (du n x) x)
    (hdu_cont : ∀ n, ContinuousOn (du n) (Icc 0 L))
    (hv : ∀ n, ContinuousOn (v n) (Icc 0 L)) (hvpos : ∀ n, ∀ x ∈ Icc 0 L, 0 < v n x)
    (hdv : ∀ n, ContinuousOn (dv n) (Icc 0 L))
    (hddv : ∀ n, ContinuousOn (ddv n) (Icc 0 L))
    (hderiv : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (v n) (dv n x) x)
    (hderiv2 : ∀ n x, x ∈ Ioo 0 L → HasDerivAt (dv n) (ddv n x) x)
    (hsignal : ∀ n x, x ∈ Ioo 0 L → ddv n x - mu * v n x + nu * u n x ^ gamma = 0)
    (hbc0 : ∀ n, dv n 0 = 0) (hbcL : ∀ n, dv n L = 0)
    (hF : ∀ n, ContinuousOn (F n) (Icc 0 L))
    (hflux : ∀ n, ∀ x ∈ Icc 0 L,
      du n x = chi n * (u n x ^ m / (1 + v n x) ^ beta * dv n x) - F n x)
    (hFb : ∀ n, ∀ x ∈ Icc 0 L, |F n x| ≤ Fb)
    (hkappa_le : ∀ n, ∀ x ∈ Icc 0 L, kappa ≤ 1 / (1 + v n x) ^ beta)
    (hmass : ∀ n, ∫ x in (0 : ℝ)..L, u n x ≤ M)
    (hR : ∀ n, ∫ x in (0 : ℝ)..L, u n x ^ r ≤ R) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ c : ℝ, 0 ≤ c ∧
      TendstoUniformlyOn (fun n => v (phi n)) (fun _ => nu / mu * c) atTop (Icc 0 L) ∧
      TendstoUniformlyOn (fun n => dv (phi n)) (fun _ => 0) atTop (Icc 0 L) ∧
      (∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
        Tendsto (fun n => ∫ x in p..q, u (phi n) x ^ gamma) atTop (𝓝 (c * (q - p)))) ∧
      ∀ g : Lp ℝ (ENNReal.ofReal ((r / gamma) / (r / gamma - 1))) (intervalVolume L),
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, u (phi n) x ^ gamma * g x ∂intervalVolume L) atTop
          (𝓝 (∫ x : Icc (0 : ℝ) L, c * g x ∂intervalVolume L)) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, v (phi n) x * g x ∂intervalVolume L) atTop
          (𝓝 (∫ x : Icc (0 : ℝ) L, (nu / mu * c) * g x ∂intervalVolume L)) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, dv (phi n) x * g x ∂intervalVolume L) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫ x : Icc (0 : ℝ) L, ddv (phi n) x * g x ∂intervalVolume L) atTop (𝓝 0) := by
  obtain ⟨phi, hphi, c, hc, hvlim, hdvlim, hinterval⟩ :=
    SignalSpikeSubsequence.exists_constant_C1_and_interval_source_subsequence
      hL hγ hr hγr hm hkappa hmu hnu hR0 hchi hu hu0 hdu hdu_cont hv hvpos hdv hddv
      hderiv hderiv2 hsignal hbc0 hbcL hF hflux hFb hkappa_le hmass hR
  refine ⟨phi, hphi, c, hc, hvlim, hdvlim, hinterval, ?_⟩
  exact SignalWeakSobolev.all_components_test_tendsto L mu nu gamma r R c
    (fun n => u (phi n)) (fun n => v (phi n)) (fun n => dv (phi n)) (fun n => ddv (phi n))
    hL hmu hnu hγ hr hγr hR0 (fun n => hu (phi n)) (fun n => hu0 (phi n))
    (fun n => hv (phi n)) (fun n => hvpos (phi n)) (fun n => hdv (phi n)) (fun n => hddv (phi n))
    (fun n => hderiv (phi n)) (fun n => hderiv2 (phi n)) (fun n => hsignal (phi n))
    (fun n => hbc0 (phi n)) (fun n => hbcL (phi n)) (fun n => hR (phi n)) hvlim hdvlim
end
end ChemotaxisBifurcation.SignalWeakSubsequence
