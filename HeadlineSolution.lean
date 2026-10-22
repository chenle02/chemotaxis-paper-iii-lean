module
public import ChemotaxisBifurcation.BranchCurves
public import ChemotaxisBifurcation.EndpointConcentration
public import ChemotaxisBifurcation.GlobalBranch
public import ChemotaxisBifurcation.IntervalMoments
public import ChemotaxisBifurcation.MinimalFlux
public import ChemotaxisBifurcation.MixedRemainder
public import ChemotaxisBifurcation.NoDiracMass
public import ChemotaxisBifurcation.NormalizedAsymptotic
public import ChemotaxisBifurcation.SpikeLimit
public import ChemotaxisBifurcation.SpikeLimitBlowup
public import ChemotaxisBifurcation.StationaryMassBounds
public import ChemotaxisBifurcation.TrigIntegrals

@[expose] public section

/-!
# Headline comparator Solution

Proves each statement of `HeadlineChallenge.lean` from the project theorem of the same name.
-/

set_option autoImplicit false

namespace ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.TrigIntegrals

/-- Closed form of the integral over [0, L] of three cosine series with l1 coefficients times
cos(k pi x / L). (arXiv:2610.20976v1, Lemma 2.1.) -/
theorem cos_cos_cos_cos_lp (L : ℝ) (hL : 0 < L)
    (u v w : lp (fun _ : ℕ => ℝ) 1) (k : ℕ) :
    ∫ x in (0 : ℝ)..L,
        (∑' i : ℕ, u i * Real.cos ((i : ℝ) * Real.pi * x / L)) *
          (∑' j : ℕ, v j * Real.cos ((j : ℝ) * Real.pi * x / L)) *
          (∑' l : ℕ, w l * Real.cos ((l : ℝ) * Real.pi * x / L)) *
          Real.cos ((k : ℝ) * Real.pi * x / L) =
      L / 8 *
        ((∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) + t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 + t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = k},
            u t.1.1 * v t.1.2.1 * w t.1.2.2) +
          (∑' t : {t : ℕ × ℕ × ℕ // (t.1 : ℤ) - t.2.1 - t.2.2 = -(k : ℤ)},
            u t.1.1 * v t.1.2.1 * w t.1.2.2)) +
        L / 8 * (if k = 0 then u 0 * v 0 * w 0 else 0) := by
  exact _root_.ChemotaxisBifurcation.TrigIntegrals.cos_cos_cos_cos_lp L hL u v w k

end ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.TrigIntegrals

namespace ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.MixedRemainder

open Filter Topology

/-- For every small eta on the bifurcating side the reduced scalar equation has a root of each
sign within O(|eta|) of sqrt(alpha eta / beta), where the field has derivative of sign -beta.
(arXiv:2610.20976v1, Theorem 1.1, Step 5.) -/
theorem center_ODE_final_branch_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (s ^ 2 * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (|s| * e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) :
    ∀ᶠ eta in 𝓝 (0 : ℝ), 0 < eta * beta →
      ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → ∃ s, 0 < sgn * s ∧
        alpha * eta * s - beta * s ^ 3 + R eta s = 0 ∧
        abs (|s| - Real.sqrt (alpha * eta / beta)) ≤
          (2 * alpha * (C * (2 * (|beta| + 2 * C) / alpha + 1)) *
              (3 * |beta| / (2 * alpha) + 1) / |beta| ^ 2) * |eta| ∧
        deriv (fun s => alpha * eta * s - beta * s ^ 3 + R eta s) s * beta < 0 := by
  exact _root_.ChemotaxisBifurcation.MixedRemainder.center_ODE_final_branch_eventually alpha beta
      C r R Rs halpha hbeta hC hr hr1 hRval hRder hRs

end ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.MixedRemainder

namespace ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.NormalizedAsymptotic

open Filter Asymptotics

/-- The normalized cubic coefficient P(lambda)/Q(lambda) equals (7/12 - beta/4) lambda + O(1) as
lambda tends to infinity. (arXiv:2610.20976v1, Eq. (3.7).) -/
theorem coefficient_sub_linear_isBigO (beta : ℝ) :
    (fun lambda : ℝ =>
        ((224 - 96 * beta) * lambda ^ 4
          + (192 - 152 * beta) * lambda ^ 3
          + (8 - 104 * beta - 16 * beta ^ 2) * lambda ^ 2
          + (96 - 28 * beta - 8 * beta ^ 2) * lambda
          + 56 + 11 * beta - beta ^ 2) /
          (96 * (1 + lambda) * (4 * lambda ^ 2 - 1)) - (7 / 12 - beta / 4) * lambda)
      =O[atTop] (fun _ => (1 : ℝ)) := by
  exact _root_.ChemotaxisBifurcation.NormalizedAsymptotic.coefficient_sub_linear_isBigO beta

end ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.NormalizedAsymptotic

namespace ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.IntervalMoments

open MeasureTheory Set

/-- A continuous, positive, nonconstant density on [0, L] with the logistic mass identity
a int u = b int u^(1+alpha) has 0 < min u < u* < max u, int u < L u* and
int u^(1+alpha) < L u*^(1+alpha), where u* = (a/b)^(1/alpha).
(arXiv:2610.20976v1, Lemma 4.1(1).) -/
theorem logistic_interval_bounds
    (a b alpha L : ℝ) (u : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ContinuousOn u (Icc 0 L)) (hpos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hnonconst : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u x ≠ u y)
    (hmass : a * ∫ x in (0 : ℝ)..L, u x = b * ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha)) :
    (∃ x₀ ∈ Icc 0 L, IsMinOn u (Icc 0 L) x₀ ∧ 0 < u x₀ ∧
        u x₀ < (a / b) ^ (1 / alpha)) ∧
      (∃ x₁ ∈ Icc 0 L, IsMaxOn u (Icc 0 L) x₁ ∧ (a / b) ^ (1 / alpha) < u x₁) ∧
      ∫ x in (0 : ℝ)..L, u x < L * (a / b) ^ (1 / alpha) ∧
      ∫ x in (0 : ℝ)..L, u x ^ (1 + alpha) < L * ((a / b) ^ (1 / alpha)) ^ (1 + alpha) := by
  exact _root_.ChemotaxisBifurcation.IntervalMoments.logistic_interval_bounds a b alpha L u ha hb
    halpha hL hcont hpos hnonconst hmass

end ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.IntervalMoments

namespace ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.MinimalFlux

open Set

/-- In the minimal model, the stationary equation with zero boundary flux gives u_x = chi0 u^m
(1+v)^(-beta) v_x on [0, L]. (arXiv:2610.20976v1, Eq. (4.14) in the proof of
Lemma 4.2(2), p. 29.) -/
theorem minimal_flux_identity (L chi0 m beta : ℝ) (u v du ddu dv dJ : ℝ → ℝ)
    (hdu_cont : ContinuousOn du (Icc 0 L))
    (hddu : ∀ x ∈ Ioo 0 L, HasDerivAt du (ddu x) x)
    (hJ_cont : ContinuousOn (fun x => chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x)
      (Icc 0 L))
    (hJ : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun x => chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x) (dJ x) x)
    (hstationary : ∀ x ∈ Ioo 0 L, ddu x - dJ x = 0)
    (hbc_u : du 0 = 0) (hbc_v : dv 0 = 0) :
    ∀ x ∈ Icc 0 L, du x = chi0 * (u x ^ m / (1 + v x) ^ beta) * dv x := by
  exact _root_.ChemotaxisBifurcation.MinimalFlux.minimal_flux_identity L chi0 m beta u v du ddu dv
      dJ hdu_cont hddu hJ_cont hJ hstationary hbc_u hbc_v

/-- For m = 1 the flux identity gives u(x) = u(x0) exp(int from x0 to x of chi0 v_x
(1+v)^(-beta)). (arXiv:2610.20976v1: the representation in the proof of Lemma 4.1(2), with F = 0 and
m = 1, which the proof of Lemma 4.2(2) applies to the minimal model.) -/
theorem minimal_exp_representation (L chi0 beta : ℝ) (u v du dv : ℝ → ℝ)
    (hu_cont : ContinuousOn u (Icc 0 L)) (hu_pos : ∀ x ∈ Icc 0 L, 0 < u x)
    (hdu : ∀ x ∈ Ioo 0 L, HasDerivAt u (du x) x)
    (hflux : ∀ x ∈ Ioo 0 L, du x = chi0 * (u x / (1 + v x) ^ beta) * dv x)
    (hg_cont : ContinuousOn (fun y => chi0 * dv y / (1 + v y) ^ beta) (Icc 0 L)) :
    ∀ x₀ ∈ Icc 0 L, ∀ x ∈ Icc 0 L,
      u x = u x₀ * Real.exp (∫ y in x₀..x, chi0 * dv y / (1 + v y) ^ beta) := by
  exact _root_.ChemotaxisBifurcation.MinimalFlux.minimal_exp_representation L chi0 beta u v du dv
    hu_cont hu_pos hdu hflux hg_cont

end ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.MinimalFlux

namespace ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.NoDiracMass

open MeasureTheory Set Filter
open scoped Topology

/-- For non-constant positive densities with the logistic mass identity, the mass in a window of
radius delta tends to 0 as delta tends to 0+, uniformly in the density and the center.
(arXiv:2610.20976v1, Remark 1.3(2).) -/
theorem window_mass_tendstoUniformly
    (a b alpha L : ℝ) {ι : Type*} (u : ι → ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hL : 0 < L)
    (hcont : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hpos : ∀ n, ∀ x ∈ Icc 0 L, 0 < u n x)
    (hnonconst : ∀ n, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, u n x ≠ u n y)
    (hmass : ∀ n,
      a * ∫ x in (0 : ℝ)..L, u n x = b * ∫ x in (0 : ℝ)..L, u n x ^ (1 + alpha)) :
    TendstoUniformly
      (fun δ (nx : ι × ℝ) => ∫ x in Ioo (nx.2 - δ) (nx.2 + δ) ∩ Ioo 0 L, u nx.1 x)
      (fun _ => 0) (𝓝[>] 0) := by
  exact _root_.ChemotaxisBifurcation.NoDiracMass.window_mass_tendstoUniformly a b alpha L u ha hb
      halpha hL hcont hpos hnonconst hmass

end ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.NoDiracMass

namespace ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.EndpointConcentration

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

/-- Finite measures of fixed mass whose mass outside every neighbourhood of an endpoint vanishes
converge weakly to that mass times the Dirac measure at the endpoint. (arXiv:2610.20976v1,
Theorem 1.3(3).) -/
theorem tendsto_mass_smul_dirac_of_vanishing_tails
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    (endpoint : X) (mass : ℝ≥0) (hmass_pos : 0 < mass)
    (μ : ℕ → FiniteMeasure X)
    (hmass : ∀ n, (μ n).mass = mass)
    (htail : ∀ U : Set X, IsOpen U → endpoint ∈ U →
      Tendsto (fun n ↦ μ n Uᶜ) atTop (𝓝 0)) :
    Tendsto μ atTop
      (𝓝 (mass • (diracProba endpoint).toFiniteMeasure)) := by
  exact
    _root_.ChemotaxisBifurcation.EndpointConcentration.tendsto_mass_smul_dirac_of_vanishing_tails
    endpoint mass hmass_pos μ hmass htail

end ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.EndpointConcentration

namespace ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.GlobalBranch

open Set Filter Topology MeasureTheory intervalIntegral

/-- Monotone solutions of the form c + s_j cos(n pi x / L) + o(s_j) can only occur for the first
mode n = 1. (arXiv:2610.20976v1, Section 4.3, proof of Theorem 1.3(3).) -/
theorem mode_eq_one_of_monotone_limit {L c : ℝ} (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n)
    (u r : ℕ → ℝ → ℝ) (s ε : ℕ → ℝ)
    (hu : ∀ j x, u j x = c + s j * Real.cos ((n : ℝ) * Real.pi / L * x) + r j x)
    (hs : ∀ j, s j ≠ 0)
    (hr : ∀ j, ∀ x ∈ Icc 0 L, |r j x| ≤ ε j * |s j|)
    (hε : Tendsto ε atTop (𝓝 0))
    (hmono : ∀ j, MonotoneOn (u j) (Icc 0 L) ∨ AntitoneOn (u j) (Icc 0 L)) :
    n = 1 := by
  exact @_root_.ChemotaxisBifurcation.GlobalBranch.mode_eq_one_of_monotone_limit L c hL n hn u r s ε hu hs hr hε hmono

end ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.GlobalBranch

namespace ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.SpikeLimit

open Set Filter Topology MeasureTheory
open scoped Interval

/-- A nonnegative C1 limit V with V_x(x) = int_0^x (mu V - nu W), V_x(L) = 0 and W V_x = 0 a.e. is
constant, and W equals a constant c >= 0 a.e. (arXiv:2610.20976v1, Lemma 5.1.) -/
theorem limit_eq_const {L mu nu : ℝ} {V dV W : ℝ → ℝ} (hL : 0 < L) (hmu : 0 < mu)
    (hnu : 0 < nu) (hV : ContinuousOn V (Icc 0 L))
    (hdV : ∀ x ∈ Ioo 0 L, HasDerivAt V (dV x) x) (hdV_cont : ContinuousOn dV (Icc 0 L))
    (hV0 : ∀ x ∈ Icc 0 L, 0 ≤ V x) (hW : IntervalIntegrable W volume 0 L)
    (heq : ∀ x ∈ Icc 0 L, dV x = ∫ y in (0 : ℝ)..x, (mu * V y - nu * W y))
    (hbcL : dV L = 0) (hWdV : ∀ᵐ x, x ∈ Ioo 0 L → W x * dV x = 0) :
    ∃ c, 0 ≤ c ∧ (∀ x ∈ Icc 0 L, V x = nu / mu * c) ∧ ∀ᵐ x, x ∈ Icc 0 L → W x = c := by
  exact @_root_.ChemotaxisBifurcation.SpikeLimit.limit_eq_const L mu nu V dV W hL hmu hnu hV hdV hdV_cont hV0 hW heq hbcL hWdV

/-- Continuous u_n >= 0 with (1+alpha)-moments bounded by L (u*)^(1+alpha) and int u_n^gamma -> c L
give 0 <= c <= (u*)^gamma. (arXiv:2610.20976v1, Theorem 1.4.) -/
theorem spike_limit_constant_le {L uStar alpha gamma c : ℝ} {u : ℕ → ℝ → ℝ} (hL : 0 < L)
    (halpha : 0 < alpha) (huStar : 0 ≤ uStar) (hγ : 0 < gamma) (hγα : gamma ≤ 1 + alpha)
    (hu : ∀ n, ContinuousOn (u n) (Icc 0 L)) (hu0 : ∀ n, ∀ y ∈ Icc 0 L, 0 ≤ u n y)
    (hmoment : ∀ n, ∫ y in (0 : ℝ)..L, u n y ^ (1 + alpha) ≤ L * uStar ^ (1 + alpha))
    (hweak : Tendsto (fun n => ∫ y in (0 : ℝ)..L, u n y ^ gamma) atTop (𝓝 (c * L))) :
    0 ≤ c ∧ c ≤ uStar ^ gamma := by
  exact @_root_.ChemotaxisBifurcation.SpikeLimit.spike_limit_constant_le L uStar alpha gamma c u hL halpha huStar hγ hγα hu hu0 hmoment hweak

end ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.SpikeLimit

namespace ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.BranchCurves

open Filter Topology

/-- Local uniqueness of the two branches: on a fixed window |s| ≤ ρ, for each small η on the
bifurcating side there is exactly one root of each sign. (arXiv:2610.20976v1: existence of the
roots is Step 5 of the proof of Theorem 1.1, TeX line 1969. Their uniqueness is used, but not
argued, in the proofs of Theorem 1.3(1), TeX line 2866, and Theorem 1.3(3), TeX line 3024; see
finding v1-proof-gap-local-uniqueness.) -/
theorem branchRoot_existsUnique_eventually (alpha beta C r : ℝ) (R Rs : ℝ → ℝ → ℝ)
    (halpha : 0 < alpha) (hbeta : beta ≠ 0) (hC : 0 ≤ C)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRval : ∀ e s, |e| ≤ r → |s| ≤ r →
      |R e s| ≤ C * (|s| * e ^ 2 + |s| ^ 3 * |e| + s ^ 4))
    (hRder : ∀ e s, |e| ≤ r → |s| ≤ r → HasDerivAt (R e) (Rs e s) s)
    (hRs : ∀ e s, |e| ≤ r → |s| ≤ r →
      |Rs e s| ≤ C * (e ^ 2 + s ^ 2 * |e| + |s| ^ 3)) :
    ∃ ρ > 0, ∀ᶠ eta in 𝓝 (0 : ℝ), 0 < eta * beta → ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
      ∃! s, 0 < sgn * s ∧ |s| ≤ ρ ∧ alpha * eta * s - beta * s ^ 3 + R eta s = 0 := by
  exact _root_.ChemotaxisBifurcation.BranchCurves.branchRoot_existsUnique_eventually alpha beta
    C r R Rs halpha hbeta hC hr hr1 hRval hRder hRs

end ChemotaxisBifurcationHeadline.ChemotaxisBifurcation.BranchCurves
