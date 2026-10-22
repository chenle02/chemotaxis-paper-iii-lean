module
public import ChemotaxisBifurcation.PrimitiveDerivatives

@[expose] public section

/-!
# Mobility mixed-partial witnesses

These are the actual positive-base derivatives of
`u^m (1+v)^(-beta)` underlying Equation 2.7--2.8.  Function-valued PDE
remainders remain outside this finite scalar module.
-/

namespace ChemotaxisBifurcation

open Filter
open scoped Topology

/-- Mobility as a function of population with the signal offset fixed. -/
noncomputable def mobilityInU (m beta w u : ℝ) : ℝ :=
  u ^ m * w ^ (-beta)

/-- Mobility as a function of signal offset with the population fixed. -/
noncomputable def mobilityInW (m beta u w : ℝ) : ℝ :=
  w ^ (-beta) * u ^ m

def mobilityInU_hasDerivAt
    (m beta w u : ℝ) (hu : 0 < u) :=
  (mobility_hasDerivAt m u hu).mul
    (hasDerivAt_const u (w ^ (-beta)))

theorem mobilityInU_derivative_value (m beta w u : ℝ) :
    m * u ^ (m - 1) * w ^ (-beta) + u ^ m * 0 =
      m * u ^ (m - 1) * w ^ (-beta) := by ring

/-- Derivative of the first population derivative; its value is twice the
factorial-normalized coefficient `B_uu`. -/
def mobilityInU_second_hasDerivAt
    (m beta w u : ℝ) (hu : 0 < u) :=
  (hasDerivAt_const u (m * w ^ (-beta))).mul
    (rpow_hasDerivAt (m - 1) u hu)

theorem mobilityInU_second_derivative_value (m beta w u : ℝ) :
    0 * u ^ (m - 1) +
        (m * w ^ (-beta)) * ((m - 1) * u ^ (m - 1 - 1)) =
      m * (m - 1) * u ^ (m - 2) * w ^ (-beta) := by ring

def mobilityInW_hasDerivAt
    (m beta u w : ℝ) (hw : 0 < w) :=
  (sensitivity_hasDerivAt beta w hw).mul
    (hasDerivAt_const w (u ^ m))

theorem mobilityInW_derivative_value (m beta u w : ℝ) :
    (-beta * w ^ (-beta - 1)) * u ^ m + w ^ (-beta) * 0 =
      -beta * u ^ m * w ^ (-beta - 1) := by ring

/-- Mixed derivative `∂_w ∂_u` of the mobility. -/
def mobility_mixed_hasDerivAt
    (m beta u w : ℝ) (hw : 0 < w) :=
  (sensitivity_hasDerivAt beta w hw).mul
    (hasDerivAt_const w (m * u ^ (m - 1)))

theorem mobility_mixed_derivative_value (m beta u w : ℝ) :
    (-beta * w ^ (-beta - 1)) * (m * u ^ (m - 1)) +
        w ^ (-beta) * 0 =
      -m * beta * u ^ (m - 1) * w ^ (-beta - 1) := by ring

/-- Derivative of the first signal derivative; its value is twice the
factorial-normalized coefficient `B_vv`. -/
def mobilityInW_second_hasDerivAt
    (m beta u w : ℝ) (hw : 0 < w) :=
  (rpow_hasDerivAt (-beta - 1) w hw).mul
    (hasDerivAt_const w (-beta * u ^ m))

theorem mobilityInW_second_derivative_value (m beta u w : ℝ) :
    ((-beta - 1) * w ^ (-beta - 1 - 1)) * (-beta * u ^ m) +
        w ^ (-beta - 1) * 0 =
      beta * (beta + 1) * u ^ m * w ^ (-beta - 2) := by ring

/-- Normalized first population derivative, stated using the named mobility. -/
theorem mobilityInU_hasDerivAt_normalized
    (m beta w u : ℝ) (hu : 0 < u) :
    HasDerivAt (mobilityInU m beta w)
      (m * u ^ (m - 1) * w ^ (-beta)) u := by
  change HasDerivAt
    ((fun y : ℝ => y ^ m) * fun _ : ℝ => w ^ (-beta))
      (m * u ^ (m - 1) * w ^ (-beta)) u
  have h := mobilityInU_hasDerivAt m beta w u hu
  rw [mobilityInU_derivative_value] at h
  exact h

/-- Normalized first signal-offset derivative, stated using the named mobility. -/
theorem mobilityInW_hasDerivAt_normalized
    (m beta u w : ℝ) (hw : 0 < w) :
    HasDerivAt (mobilityInW m beta u)
      (-beta * u ^ m * w ^ (-beta - 1)) w := by
  change HasDerivAt
    ((fun y : ℝ => y ^ (-beta)) * fun _ : ℝ => u ^ m)
      (-beta * u ^ m * w ^ (-beta - 1)) w
  have h := mobilityInW_hasDerivAt m beta u w hw
  rw [mobilityInW_derivative_value] at h
  exact h

/-- The entered second population derivative is the derivative of the actual
first derivative on a positive neighborhood. -/
theorem mobilityInU_deriv_hasDerivAt
    (m beta w u : ℝ) (hu : 0 < u) :
    HasDerivAt (deriv (mobilityInU m beta w))
      (m * (m - 1) * u ^ (m - 2) * w ^ (-beta)) u := by
  have hbase := mobilityInU_second_hasDerivAt m beta w u hu
  rw [mobilityInU_second_derivative_value] at hbase
  have hpos : ∀ᶠ y in 𝓝 u, 0 < y := isOpen_Ioi.mem_nhds hu
  have hev :
      (fun y : ℝ => m * w ^ (-beta) * y ^ (m - 1)) =ᶠ[𝓝 u]
        deriv (mobilityInU m beta w) := by
    filter_upwards [hpos] with y hy
    rw [(mobilityInU_hasDerivAt_normalized m beta w y hy).deriv]
    ring
  exact hbase.congr_of_eventuallyEq hev.symm

/-- The mixed coefficient differentiates the actual population derivative
with respect to the signal offset. -/
theorem mobility_mixed_deriv_hasDerivAt
    (m beta u w : ℝ) (hu : 0 < u) (hw : 0 < w) :
    HasDerivAt (fun z : ℝ => deriv (mobilityInU m beta z) u)
      (-m * beta * u ^ (m - 1) * w ^ (-beta - 1)) w := by
  have hbase := mobility_mixed_hasDerivAt m beta u w hw
  rw [mobility_mixed_derivative_value] at hbase
  have hev :
      (fun z : ℝ => z ^ (-beta) * (m * u ^ (m - 1))) =ᶠ[𝓝 w]
        (fun z : ℝ => deriv (mobilityInU m beta z) u) := by
    filter_upwards [] with z
    rw [(mobilityInU_hasDerivAt_normalized m beta z u hu).deriv]
    ring
  exact hbase.congr_of_eventuallyEq hev.symm

/-- The entered second signal derivative is the derivative of the actual
first derivative on a positive neighborhood. -/
theorem mobilityInW_deriv_hasDerivAt
    (m beta u w : ℝ) (hw : 0 < w) :
    HasDerivAt (deriv (mobilityInW m beta u))
      (beta * (beta + 1) * u ^ m * w ^ (-beta - 2)) w := by
  have hbase := mobilityInW_second_hasDerivAt m beta u w hw
  rw [mobilityInW_second_derivative_value] at hbase
  have hpos : ∀ᶠ y in 𝓝 w, 0 < y := isOpen_Ioi.mem_nhds hw
  have hev :
      (fun y : ℝ => (-beta * u ^ m) * y ^ (-beta - 1)) =ᶠ[𝓝 w]
        deriv (mobilityInW m beta u) := by
    filter_upwards [hpos] with y hy
    rw [(mobilityInW_hasDerivAt_normalized m beta u y hy).deriv]
  have hev' :
      deriv (mobilityInW m beta u) =ᶠ[𝓝 w]
        (fun y : ℝ => y ^ (-beta - 1) * (-beta * u ^ m)) := by
    filter_upwards [hev] with y hy
    rw [← hy]
    ring
  exact hbase.congr_of_eventuallyEq hev'

/-- Translation from the signal offset `w` to the manuscript variable
`v`, where `w = 1 + v`; the inner derivative is one. -/
theorem mobilityInV_hasDerivAt
    (m beta u v : ℝ) (hw : 0 < 1 + v) :
    HasDerivAt (fun z : ℝ => mobilityInW m beta u (1 + z))
      (-beta * u ^ m * (1 + v) ^ (-beta - 1)) v := by
  have hinner : HasDerivAt (fun z : ℝ => 1 + z) 1 v := by
    simpa using (hasDerivAt_id v).const_add 1
  simpa [Function.comp_def] using
    (mobilityInW_hasDerivAt_normalized m beta u (1 + v) hw).comp v hinner

end ChemotaxisBifurcation
