module
public import ChemotaxisBifurcation.SignalPowerMoment
public import ChemotaxisBifurcation.SignalDirectLimit

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
namespace ChemotaxisBifurcation.SignalSpikeSubsequence
noncomputable section

/-- Actual constant C1 signal subsequence and interval-tested population-source
convergence from the classical first integral and signal equations. There is
no extraction, weak-source-density or limiting-equation hypothesis. The
stronger weak Lq and weak W2q convergence claims remain separate. -/
theorem exists_constant_C1_and_interval_source_subsequence
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
      ∀ p q, 0 ≤ p → p ≤ q → q ≤ L →
        Tendsto (fun n => ∫ x in p..q, u (phi n) x ^ gamma) atTop (𝓝 (c * (q - p))) := by
  obtain ⟨V, DV, phi, hphi, hV, hDV, hvlim, hdvlim, hDV0, hDVL, hV0, hderivlim⟩ :=
    SignalPowerMoment.exists_C1_subsequence_of_power_moment L mu nu gamma r R u v dv ddv
      hL hmu hnu.le hγ hr hγr hR0 hu hu0 hv hvpos hdv hddv hderiv hderiv2 hsignal hbc0 hbcL hR
  obtain ⟨c, hc, hVc, hDVc, hsource⟩ := SignalDirectLimit.constant_limit_without_weak_source
    hL hγ hγr hm hkappa hmu hnu (hchi.comp hphi.tendsto_atTop)
    (fun n => hu (phi n)) (fun n => hu0 (phi n)) (fun n => hdu (phi n))
    (fun n => hdu_cont (phi n)) (fun n => hv (phi n))
    (fun n x hx => (hvpos (phi n) x hx).le) (fun n => hdv (phi n)) (fun n => hF (phi n))
    (fun n => hflux (phi n)) (fun n => hFb (phi n)) (fun n => hkappa_le (phi n))
    (fun n => hmass (phi n)) (fun n => hR (phi n)) hV hderivlim hDV hV0 hdvlim hvlim
    (fun n => hderiv2 (phi n)) (fun n => hsignal (phi n)) hDV0 hDVL
  exact ⟨phi, hphi, c, hc, hvlim.congr_right (fun x hx => hVc x hx),
    hdvlim.congr_right (fun x hx => hDVc x hx), hsource⟩
end
end ChemotaxisBifurcation.SignalSpikeSubsequence
