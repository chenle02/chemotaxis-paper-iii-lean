module
public import ChemotaxisBifurcation.SinePotentialBound

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.MonotoneSineBound
open Real Set MonotoneLocusGeneral
noncomputable section

def potential (chi mu nu gamma beta m : ℝ) (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  chi*nu*gamma*u x^(m+gamma-1)/(1+v x)^beta-mu

theorem neg_coeff_eq_potential {chi mu nu gamma beta m : ℝ} {u v : ℝ → ℝ} {x : ℝ}
    (hu : 0 < u x) :
    -coeff chi mu nu gamma beta m u v x = potential chi mu nu gamma beta m u v x := by
  have hp : u x^(m+gamma-1) = u x^m*u x^(gamma-1) := by
    rw [show m+gamma-1 = m+(gamma-1) by ring,Real.rpow_add hu]
  dsimp [coeff,potential]
  rw [hp]
  ring

/-- Actual stationary first-order equations and monotonicity yield the
sine-test obstruction on every interior subinterval. -/
theorem not_potential_ge {chi mu nu gamma beta m L a b : ℝ} {u v y : ℝ → ℝ}
    (s : StationarySolution chi mu nu gamma beta m L u v y)
    (hchi : 0 < chi) (hanti : AntitoneOn u (Icc 0 L)) (hnc : ¬IsConstOn u L)
    (ha : 0 < a) (hab : a < b) (hb : b < L) :
    ¬ (∀ x ∈ Icc a b, (Real.pi/(b-a))^2 ≤ potential chi mu nu gamma beta m u v x) := by
  have hsub : Icc a b ⊆ Icc 0 L := fun x hx => ⟨ha.le.trans hx.1,hx.2.trans hb.le⟩
  have hint : Icc a b ⊆ Ioo 0 L := fun x hx => ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩
  let w := fun x => -y x
  let dw := fun x => -(mu*v x-nu*u x^gamma)
  apply SinePotentialBound.not_potential_ge hab
    (w := w) (dw := dw) (c := potential chi mu nu gamma beta m u v)
  · intro x hx
    exact ((s.deriv_y x (hsub hx)).neg).mono hsub
  · intro x hx
    have h := ((s.deriv_z x (hsub hx)).neg).mono hsub
    convert h using 1
    rw [← neg_coeff_eq_potential (s.u_pos x (hsub hx))]
    dsimp [w]
    ring
  · intro x hx
    exact neg_pos.mpr (s.sig_neg_of_antitoneOn hchi hanti hnc x (hint hx))

/-- The sine test gives an actual quantitative interior population bound.
The signal upper bound is an ordinary input here, discharged by the physical
minimal-PDE wrapper. No potential/sine-test estimate is assumed. -/
theorem interior_power_bound {chi mu nu gamma beta m L delta V : ℝ} {u v y : ℝ → ℝ}
    (s : StationarySolution chi mu nu gamma beta m L u v y)
    (hchi : 0 < chi) (hmu : 0 ≤ mu) (hnu : 0 < nu) (hgamma : 0 < gamma) (hm : 1 ≤ m)
    (hbeta : 0 ≤ beta) (hanti : AntitoneOn u (Icc 0 L)) (hnc : ¬IsConstOn u L)
    (hdelta : delta ∈ Ioo 0 L) (hV : ∀ x ∈ Icc 0 L, v x ≤ V) :
    chi*nu*gamma*u delta^(m+gamma-1) ≤
      (mu+(Real.pi/(delta-delta/2))^2)*(1+V)^beta := by
  have hI : Icc (delta/2) delta ⊆ Icc 0 L := by
    intro x hx; constructor <;> linarith [hx.1,hx.2,hdelta.1,hdelta.2]
  have hp : 0 ≤ m+gamma-1 := by linarith
  have hcoef : 0 ≤ chi*nu*gamma := by positivity
  by_contra hnot
  have hstrict := lt_of_not_ge hnot
  apply not_potential_ge s hchi hanti hnc (by linarith [hdelta.1] : 0 < delta/2)
    (by linarith [hdelta.1] : delta/2 < delta) hdelta.2
  intro x hx
  have hux : u delta ≤ u x := hanti (hI hx) (Ioo_subset_Icc_self hdelta) hx.2
  have hpow : u delta^(m+gamma-1) ≤ u x^(m+gamma-1) :=
    Real.rpow_le_rpow (s.u_pos delta (Ioo_subset_Icc_self hdelta)).le hux hp
  have hden : (1+v x)^beta ≤ (1+V)^beta := Real.rpow_le_rpow
    (s.v_pos x (hI hx)).le (by linarith [hV x (hI hx)]) hbeta
  have hd : 0 < (1+v x)^beta := Real.rpow_pos_of_pos (s.v_pos x (hI hx)) _
  have hnum := mul_le_mul_of_nonneg_left hpow hcoef
  have hpositive : 0 ≤ mu+(Real.pi/(delta-delta/2))^2 := add_nonneg hmu (sq_nonneg _)
  have hh : (mu+(Real.pi/(delta-delta/2))^2)*(1+v x)^beta < chi*nu*gamma*u x^(m+gamma-1) :=
    (mul_le_mul_of_nonneg_left hden hpositive).trans_lt (hstrict.trans_le hnum)
  dsimp [potential]
  have hdiv := (lt_div_iff₀ hd).mpr hh
  linarith

theorem not_potential_ge_increasing {chi mu nu gamma beta m L a b : ℝ} {u v y : ℝ → ℝ}
    (s : StationarySolution chi mu nu gamma beta m L u v y)
    (hchi : 0 < chi) (hmono : MonotoneOn u (Icc 0 L)) (hnc : ¬IsConstOn u L)
    (ha : 0 < a) (hab : a < b) (hb : b < L) :
    ¬ (∀ x ∈ Icc a b, (Real.pi/(b-a))^2 ≤ potential chi mu nu gamma beta m u v x) := by
  have hsub : Icc a b ⊆ Icc 0 L := fun x hx => ⟨ha.le.trans hx.1,hx.2.trans hb.le⟩
  have hint : Icc a b ⊆ Ioo 0 L := fun x hx => ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩
  let w := fun x => y x
  let dw := fun x => mu*v x-nu*u x^gamma
  apply SinePotentialBound.not_potential_ge hab
    (w := w) (dw := dw) (c := potential chi mu nu gamma beta m u v)
  · intro x hx
    exact (s.deriv_y x (hsub hx)).mono hsub
  · intro x hx
    have h := (s.deriv_z x (hsub hx)).mono hsub
    convert h using 1
    rw [← neg_coeff_eq_potential (s.u_pos x (hsub hx))]
    dsimp [w]
    ring
  · intro x hx
    exact s.sig_pos_of_monotoneOn hchi hmono hnc x (hint hx)

theorem interior_power_bound_right {chi mu nu gamma beta m L delta V : ℝ} {u v y : ℝ → ℝ}
    (s : StationarySolution chi mu nu gamma beta m L u v y)
    (hchi : 0 < chi) (hmu : 0 ≤ mu) (hnu : 0 < nu) (hgamma : 0 < gamma) (hm : 1 ≤ m)
    (hbeta : 0 ≤ beta) (hmono : MonotoneOn u (Icc 0 L)) (hnc : ¬IsConstOn u L)
    (hdelta : delta ∈ Ioo 0 L) (hV : ∀ x ∈ Icc 0 L, v x ≤ V) :
    chi*nu*gamma*u delta^(m+gamma-1) ≤
      (mu+(Real.pi/((delta+L)/2-delta))^2)*(1+V)^beta := by
  have hI : Icc delta ((delta+L)/2) ⊆ Icc 0 L := by
    intro x hx; constructor <;> linarith [hx.1,hx.2,hdelta.1,hdelta.2]
  have hp : 0 ≤ m+gamma-1 := by linarith
  have hcoef : 0 ≤ chi*nu*gamma := by positivity
  by_contra hnot
  have hstrict := lt_of_not_ge hnot
  apply not_potential_ge_increasing s hchi hmono hnc hdelta.1
    (by linarith [hdelta.2] : delta < (delta+L)/2) (by linarith [hdelta.2] : (delta+L)/2 < L)
  intro x hx
  have hux : u delta ≤ u x := hmono (Ioo_subset_Icc_self hdelta) (hI hx) hx.1
  have hpow : u delta^(m+gamma-1) ≤ u x^(m+gamma-1) :=
    Real.rpow_le_rpow (s.u_pos delta (Ioo_subset_Icc_self hdelta)).le hux hp
  have hden : (1+v x)^beta ≤ (1+V)^beta := Real.rpow_le_rpow
    (s.v_pos x (hI hx)).le (by linarith [hV x (hI hx)]) hbeta
  have hd : 0 < (1+v x)^beta := Real.rpow_pos_of_pos (s.v_pos x (hI hx)) _
  have hnum := mul_le_mul_of_nonneg_left hpow hcoef
  have hpositive : 0 ≤ mu+(Real.pi/((delta+L)/2-delta))^2 := add_nonneg hmu (sq_nonneg _)
  have hh : (mu+(Real.pi/((delta+L)/2-delta))^2)*(1+v x)^beta < chi*nu*gamma*u x^(m+gamma-1) :=
    (mul_le_mul_of_nonneg_left hden hpositive).trans_lt (hstrict.trans_le hnum)
  dsimp [potential]
  have hdiv := (lt_div_iff₀ hd).mpr hh
  linarith

end
end ChemotaxisBifurcation.MonotoneSineBound
