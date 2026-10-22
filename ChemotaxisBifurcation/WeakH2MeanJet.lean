module
public import ChemotaxisBifurcation.CurvedSignalResponse
@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.WeakH2MeanJet
open Set Filter Topology Asymptotics WeakH2PhaseSpace WeakH2AmbientClosure WeakH2CosineMode
noncomputable section

/-- Fixed mass of an actual phase family forces its quadratic constant coefficient
 to vanish. No mass condition on the cubic phase term is required. -/
theorem quadratic_constant_zero {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (jet : QuadraticJetData) (H3 : Space L hL) (J : ℝ → Space L hL)
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), populationMass hL (J t) = 0)
    (he : (fun t => J t - (t • mode hL n +
      t^2 • (jet.a0 • const hL 1 + jet.a2 • mode hL (2*n)) + t^3 • H3))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3)) : jet.a0 = 0 := by
  let massCLM : Space L hL →L[ℝ] ℝ :=
    { toFun := populationMass hL
      map_add' := populationMass_add hL
      map_smul' := populationMass_smul hL
      cont := continuous_populationMass hL }
  have hc : populationMass hL (const hL 1) = L := by
    have h := const_mem_fixedMeanSet hL 1
    change populationMass hL (const hL 1) = L*1 at h
    simpa using h
  have hh := (massCLM.isBigO_comp _ (𝓝 (0 : ℝ))).trans_isLittleO he
  have hmass : (fun t => -(t^2*(jet.a0*L)+t^3*populationMass hL H3))
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^3) := by
    apply hh.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hm] with t ht
    simp [massCLM,populationMass_sub,populationMass_add,populationMass_smul,
      ht,hc,mass_mode hL n hn,mass_mode hL (2*n) (by omega)]
  have h32 : (fun t : ℝ => t^3) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) :=
    isLittleO_pow_pow (by norm_num : 2 < 3)
  have hz : (fun t : ℝ => t^2*(jet.a0*L)) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t^2) := by
    convert (hmass.of_neg_left.trans_isBigO h32.isBigO).sub (h32.const_mul_left (populationMass hL H3)) using 1
    funext t
    ring
  have hz' := hz.mono (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hlim := (isLittleO_iff_tendsto (fun t ht => by simp [ht])).mp hz'
  have heq : (fun t : ℝ => (t^2*(jet.a0*L))/t^2) =ᶠ[𝓝[≠] (0 : ℝ)] (fun _ => jet.a0*L) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    field_simp
  have hv : jet.a0*L = 0 := tendsto_nhds_unique tendsto_const_nhds (hlim.congr' heq)
  exact (mul_eq_zero.mp hv).resolve_right (ne_of_gt hL)
end
end ChemotaxisBifurcation.WeakH2MeanJet
