module
public import ChemotaxisBifurcation.ClassicalODECompactness
public import ChemotaxisBifurcation.ClassicalLogisticEstimates
public import ChemotaxisBifurcation.PhysicalStrongPositivity
public import ChemotaxisBifurcation.SignedEllipticEnergy

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.StationaryODEState
open Real Set MeasureTheory Filter Topology
noncomputable section

/-- Parameter, population/value derivative, signal/value derivative. -/
abbrev State := ℝ × ((ℝ × ℝ) × (ℝ × ℝ))

def point (chi u du v dv : ℝ) : State := (chi,((u,du),(v,dv)))

/-- Continuous extension outside the physical half-space v>=0. -/
def offset (z : State) : ℝ := max 1 (1+z.2.2.1)

def signalRHS (mu nu gamma : ℝ) (z : State) : ℝ :=
  mu*z.2.2.1-nu*z.2.1.1^gamma

def drift (m beta : ℝ) (z : State) : ℝ :=
  z.1*m*z.2.1.1^(m-1)*z.2.2.2/(offset z)^beta

def zero (a b alpha m beta mu nu gamma : ℝ) (z : State) : ℝ :=
  a-b*z.2.1.1^alpha-z.1*z.2.1.1^(m-1)*
    (signalRHS mu nu gamma z/(offset z)^beta-beta*z.2.2.2^2/(offset z)^(beta+1))

/-- Actual stationary system on the nonnegative physical half-space. The
parameter derivative is zero, so extraction includes the sensitivity itself. -/
def field (a b alpha m beta mu nu gamma : ℝ) (z : State) : State :=
  (0,((z.2.1.2,-zero a b alpha m beta mu nu gamma z*z.2.1.1+drift m beta z*z.2.1.2),
    (z.2.2.2,signalRHS mu nu gamma z)))

theorem continuous_field (a b alpha m beta mu nu gamma : ℝ)
    (halpha : 0 ≤ alpha) (hm : 1 ≤ m) (hgamma : 0 ≤ gamma) :
    Continuous (field a b alpha m beta mu nu gamma) := by
  have hchi : Continuous (fun z : State => z.1) := by fun_prop
  have hu : Continuous (fun z : State => z.2.1.1) := by fun_prop
  have hdu : Continuous (fun z : State => z.2.1.2) := by fun_prop
  have hv : Continuous (fun z : State => z.2.2.1) := by fun_prop
  have hdv : Continuous (fun z : State => z.2.2.2) := by fun_prop
  have hw : Continuous offset := continuous_const.max (continuous_const.add hv)
  have hwpos (z : State) : 0 < offset z := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hwb : Continuous (fun z => (offset z)^beta) :=
    hw.rpow_const (fun z => Or.inl (hwpos z).ne')
  have hwb1 : Continuous (fun z => (offset z)^(beta+1)) :=
    hw.rpow_const (fun z => Or.inl (hwpos z).ne')
  have hn (q : ℝ) (z : State) : (offset z)^q ≠ 0 := (Real.rpow_pos_of_pos (hwpos z) q).ne'
  have hum : Continuous (fun z : State => z.2.1.1^(m-1)) :=
    hu.rpow_const (fun _ => Or.inr (by linarith))
  have hua : Continuous (fun z : State => z.2.1.1^alpha) :=
    hu.rpow_const (fun _ => Or.inr halpha)
  have hug : Continuous (fun z : State => z.2.1.1^gamma) :=
    hu.rpow_const (fun _ => Or.inr hgamma)
  have hs : Continuous (signalRHS mu nu gamma) :=
    (continuous_const.mul hv).sub (continuous_const.mul hug)
  have hd : Continuous (drift m beta) :=
    (((hchi.mul continuous_const).mul hum).mul hdv).div hwb (hn beta)
  have hz : Continuous (zero a b alpha m beta mu nu gamma) :=
    (continuous_const.sub (continuous_const.mul hua)).sub
      ((hchi.mul hum).mul ((hs.div hwb (hn beta)).sub
        ((continuous_const.mul (hdv.pow 2)).div hwb1 (hn (beta+1)))))
  exact continuous_const.prodMk ((hdu.prodMk ((hz.neg.mul hu).add (hd.mul hdu))).prodMk
    (hdv.prodMk hs))

/-- The given literal classical stationary system is a trajectory of the
continuous augmented field; no expanded ODE is supplied as an assumption. -/
theorem classical_derivative {L a b alpha chi m beta mu nu gamma : ℝ}
    (p : StationaryMassIdentity.ClassicalProfile L a b alpha chi m beta)
    (s : ClassicalLogisticEstimates.SignalData p mu nu gamma)
    (hm : 1 ≤ m) (halpha : 0 ≤ alpha)
    (hu : ∀ x ∈ Icc 0 L, 0 ≤ p.u x) {x : ℝ} (hx : x ∈ Ioo 0 L) :
    HasDerivAt (fun y => point chi (p.u y) (p.du y) (p.v y) (p.dv y))
      (field a b alpha m beta mu nu gamma (point chi (p.u x) (p.du x) (p.v x) (p.dv x))) x := by
  have hx' := Ioo_subset_Icc_self hx
  have hbase : ∀ y ∈ Icc 0 L, 0 < 1+p.v y := by
    intro y hy; linarith [s.nonnegative_v y hy]
  have hflux := (PhysicalStrongPositivity.flux_hasDerivWithinAt (chi := chi) (beta := beta) hm hbase hx'
    (p.derivative_u x hx).hasDerivWithinAt (p.derivative_v x hx).hasDerivWithinAt
    (s.derivative_dv x hx).hasDerivWithinAt).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hJ := (p.derivative_flux x hx).unique hflux
  have hstat := p.stationary x hx
  rw [hJ] at hstat
  have hpop := PhysicalStrongPositivity.stationary_linear_identity hm halpha (hu x hx') hstat
  have hsig : s.ddv x = mu*p.v x-nu*p.u x^gamma := by linarith [s.stationary x hx]
  have hw : 1 ≤ 1+p.v x := by linarith [s.nonnegative_v x hx']
  have hvalue : field a b alpha m beta mu nu gamma (point chi (p.u x) (p.du x) (p.v x) (p.dv x)) =
      point 0 (p.du x) (p.ddu x) (p.dv x) (s.ddv x) := by
    dsimp [field,zero,drift,signalRHS,offset,point]
    rw [max_eq_right hw]
    rw [hsig] at hpop
    ext <;> first | rfl | exact hpop.symm | exact hsig.symm
  rw [hvalue]
  exact (hasDerivAt_const x chi).prodMk
    (((p.derivative_u x hx).prodMk (p.derivative_du x hx)).prodMk
      ((p.derivative_v x hx).prodMk (s.derivative_dv x hx)))

/-- A parameter-only uniform bound for the actual augmented stationary
profiles, from the full logistic Gronwall and signed signal estimates. -/
theorem uniform_state_bound {L a b alpha m beta mu nu gamma X : ℝ}
    (chi : ℕ → ℝ) (p : ∀ n, StationaryMassIdentity.ClassicalProfile L a b alpha (chi n) m beta)
    (s : ∀ n, ClassicalLogisticEstimates.SignalData (p n) mu nu gamma)
    (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hm : 1 ≤ m) (hm1 : m ≤ alpha+2) (hbeta : 0 ≤ beta)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1+alpha)
    (hchi : ∀ n, |chi n| ≤ X)
    (hpos : ∀ n x, x ∈ Icc 0 L → 0 < (p n).u x)
    (hnonconst : ∀ n, ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, (p n).u x ≠ (p n).u y) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n x, x ∈ Icc 0 L →
      ‖point (chi n) ((p n).u x) ((p n).du x) ((p n).v x) ((p n).dv x)‖ ≤ B := by
  let U := ClassicalLogisticEstimates.gronwallC1Envelope L a b alpha gamma nu X m
  have hU : 0 ≤ U := by
    dsimp [U,ClassicalLogisticEstimates.gronwallC1Envelope,SpikeEstimates.gronwallPopulationBound]
    positivity
  let V := (1/mu+2*L^2+2*L)*(nu*U^gamma)
  refine ⟨max (max X U) (max V 0),le_trans (le_max_right _ _) (le_max_right _ _),?_⟩
  intro n x hx
  have huc := ClassicalLogisticEstimates.c1_gronwall_bound (p n) (s n) hL ha hb halpha
    hgamma hgamma1 hm hm1 hbeta hmu.le hnu (hchi n) (hpos n) (hnonconst n)
  let F := fun y => nu*(p n).u y^gamma
  have hFc : ContinuousOn F (Icc 0 L) :=
    continuousOn_const.mul ((p n).continuous_u.rpow_const (fun _ _ => Or.inr hgamma.le))
  let q : SignedEllipticEnergy.Profile L mu F := {
    V := (p n).v
    dV := (p n).dv
    continuous_V := (s n).continuous_v
    continuous_dV := (s n).continuous_dv
    derivative_V := (p n).derivative_v
    equation := by
      intro y hy
      convert (s n).derivative_dv y hy using 1
      dsimp [F]
      linarith [(s n).stationary y hy]
    neumann_left := (p n).neumann_v_left
    neumann_right := (p n).neumann_v_right }
  have hFb : ∀ y ∈ Icc 0 L, |F y| ≤ nu*U^gamma := by
    intro y hy
    have huly : (p n).u y ≤ U := (le_abs_self _).trans (huc y hy).1
    dsimp [F]
    rw [abs_mul,abs_of_nonneg hnu,abs_of_nonneg (Real.rpow_nonneg (hpos n y hy).le _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hpos n y hy).le huly hgamma.le) hnu
  have hvc : |(p n).v x|+|(p n).dv x| ≤ V :=
    q.c1_bound hL hmu hFc (by positivity) hFb x hx
  change max |chi n| (max (max |(p n).u x| |(p n).du x|)
    (max |(p n).v x| |(p n).dv x|)) ≤ max (max X U) (max V 0)
  apply max_le
  · exact (hchi n).trans ((le_max_left _ _).trans (le_max_left _ _))
  apply max_le
  · exact (max_le (huc x hx).1 (huc x hx).2).trans ((le_max_right _ _).trans (le_max_left _ _))
  apply max_le
  · have hh : |(p n).v x| ≤ V := by linarith [abs_nonneg ((p n).dv x)]
    exact hh.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hh : |(p n).dv x| ≤ V := by linarith [abs_nonneg ((p n).v x)]
    exact hh.trans ((le_max_left _ _).trans (le_max_right _ _))

end
end ChemotaxisBifurcation.StationaryODEState
