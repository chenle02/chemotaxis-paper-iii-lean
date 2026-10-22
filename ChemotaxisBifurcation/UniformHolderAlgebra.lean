module
public import ChemotaxisBifurcation.ClassicalODECompactness
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
namespace ChemotaxisBifurcation.UniformHolderAlgebra
open Real Set
noncomputable section
variable {ι : Type*}

/-- A common bounded Hölder modulus for an actual family on a fixed interval. -/
structure Control (L : ℝ) (f : ι → ℝ → ℝ) where
  exponent : ℝ
  exponent_pos : 0 < exponent
  exponent_le_one : exponent ≤ 1
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounded : ∀ n x, x ∈ Icc 0 L → |f n x| ≤ bound
  modulus : ∀ n x, x ∈ Icc 0 L → ∀ y, y ∈ Icc 0 L →
    |f n y-f n x| ≤ constant*|y-x|^exponent

 theorem power_weaken {d L r t : ℝ} (hd : 0 ≤ d) (hD : d ≤ L)
    (ht : 0 < t) (htr : t ≤ r) (hr : r ≤ 1) :
    d^r ≤ max 1 L*d^t := by
  by_cases h1 : d ≤ 1
  · have hp := Real.rpow_le_rpow_of_exponent_ge' hd h1 ht.le htr
    exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg hd _) (le_max_left _ _))
  · have hp := Real.rpow_le_self_of_one_le (le_of_not_ge h1) hr
    have ht1 : 1 ≤ d^t := Real.one_le_rpow (le_of_not_ge h1) ht.le
    exact hp.trans (hD.trans ((le_max_right _ _).trans
      (le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) ht1)))

namespace Control
variable {L : ℝ} {f g : ι → ℝ → ℝ}

def weaken (h : Control L f) (t : ℝ) (ht : 0 < t) (htr : t ≤ h.exponent) : Control L f where
  exponent := t
  exponent_pos := ht
  exponent_le_one := htr.trans h.exponent_le_one
  constant := h.constant*max 1 L
  constant_nonneg := mul_nonneg h.constant_nonneg (le_trans zero_le_one (le_max_left _ _))
  bound := h.bound
  bound_nonneg := h.bound_nonneg
  bounded := h.bounded
  modulus := by
    intro n x hx y hy
    have hd : |y-x| ≤ L := by rw [abs_le]; constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
    exact (h.modulus n x hx y hy).trans (by
      nlinarith [mul_le_mul_of_nonneg_left
        (power_weaken (abs_nonneg _) hd ht htr h.exponent_le_one) h.constant_nonneg])

def const (L c : ℝ) : Control (ι := ι) L (fun _ _ => c) where
  exponent := 1
  exponent_pos := zero_lt_one
  exponent_le_one := le_rfl
  constant := 0
  constant_nonneg := le_rfl
  bound := |c|
  bound_nonneg := abs_nonneg _
  bounded := fun _ _ _ => le_rfl
  modulus := by intros; simp

def add (h : Control L f) (k : Control L g) : Control L (fun n x => f n x+g n x) := by
  let r := min h.exponent k.exponent
  let h' := h.weaken r (lt_min h.exponent_pos k.exponent_pos) (min_le_left _ _)
  let k' := k.weaken r (lt_min h.exponent_pos k.exponent_pos) (min_le_right _ _)
  refine ⟨r,lt_min h.exponent_pos k.exponent_pos,(min_le_left _ _).trans h.exponent_le_one,
    h'.constant+k'.constant,add_nonneg h'.constant_nonneg k'.constant_nonneg,
    h.bound+k.bound,add_nonneg h.bound_nonneg k.bound_nonneg,?_,?_⟩
  · intro n x hx
    exact (abs_add_le _ _).trans (add_le_add (h.bounded n x hx) (k.bounded n x hx))
  · intro n x hx y hy
    have hh := h'.modulus n x hx y hy
    have hk := k'.modulus n x hx y hy
    calc |f n y+g n y-(f n x+g n x)| = |(f n y-f n x)+(g n y-g n x)| := by congr 1; ring
      _ ≤ |f n y-f n x|+|g n y-g n x| := abs_add_le _ _
      _ ≤ (h'.constant+k'.constant)*|y-x|^r := by change |f n y-f n x| ≤ h'.constant*|y-x|^r at hh; change |g n y-g n x| ≤ k'.constant*|y-x|^r at hk; nlinarith

def mul (h : Control L f) (k : Control L g) : Control L (fun n x => f n x*g n x) := by
  let r := min h.exponent k.exponent
  let h' := h.weaken r (lt_min h.exponent_pos k.exponent_pos) (min_le_left _ _)
  let k' := k.weaken r (lt_min h.exponent_pos k.exponent_pos) (min_le_right _ _)
  refine ⟨r,lt_min h.exponent_pos k.exponent_pos,(min_le_left _ _).trans h.exponent_le_one,
    h.bound*k'.constant+k.bound*h'.constant,
    add_nonneg (mul_nonneg h.bound_nonneg k'.constant_nonneg) (mul_nonneg k.bound_nonneg h'.constant_nonneg),
    h.bound*k.bound,mul_nonneg h.bound_nonneg k.bound_nonneg,?_,?_⟩
  · intro n x hx
    rw [abs_mul]
    exact mul_le_mul (h.bounded n x hx) (k.bounded n x hx) (abs_nonneg _) h.bound_nonneg
  · intro n x hx y hy
    have hh := h'.modulus n x hx y hy
    have hk := k'.modulus n x hx y hy
    have ha := mul_le_mul (h.bounded n y hy) hk (abs_nonneg _) h.bound_nonneg
    have hb := mul_le_mul (k.bounded n x hx) hh (abs_nonneg _) k.bound_nonneg
    calc |f n y*g n y-f n x*g n x| = |f n y*(g n y-g n x)+g n x*(f n y-f n x)| := by congr 1; ring
      _ ≤ |f n y*(g n y-g n x)|+|g n x*(f n y-f n x)| := abs_add_le _ _
      _ ≤ (h.bound*k'.constant+k.bound*h'.constant)*|y-x|^r := by
        rw [abs_mul,abs_mul]; change |f n y| * |g n y-g n x| ≤ h.bound*(k'.constant*|y-x|^r) at ha; change |g n x| * |f n y-f n x| ≤ k.bound*(h'.constant*|y-x|^r) at hb; nlinarith

/-- Concavity of the nonnegative real power gives its actual scalar Hölder modulus. -/
theorem rpow_difference {p x y : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |y^p-x^p| ≤ |y-x|^p := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this hy hx (le_of_not_ge hxy)
  rw [abs_of_nonneg (sub_nonneg.mpr hxy),abs_of_nonneg
    (sub_nonneg.mpr (Real.rpow_le_rpow hx hxy hp.le))]
  have h := Real.rpow_add_le_add_rpow hx (sub_nonneg.mpr hxy) hp.le hp1
  rw [add_sub_cancel] at h
  linarith

/-- Controls depend only on the actual representatives on the interval. -/
def congr (h : Control L f) (heq : ∀ n x, x ∈ Icc 0 L → f n x = g n x) : Control L g where
  exponent := h.exponent
  exponent_pos := h.exponent_pos
  exponent_le_one := h.exponent_le_one
  constant := h.constant
  constant_nonneg := h.constant_nonneg
  bound := h.bound
  bound_nonneg := h.bound_nonneg
  bounded := by intro n x hx; rw [← heq n x hx]; exact h.bounded n x hx
  modulus := by intro n x hx y hy; rw [← heq n x hx,← heq n y hy]; exact h.modulus n x hx y hy

/-- A uniformly bounded common Lipschitz family supplies a Hölder control. -/
def of_lipschitz (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ n x, x ∈ Icc 0 L → |f n x| ≤ B)
    (hc : ∀ n x, x ∈ Icc 0 L → ∀ y, y ∈ Icc 0 L → |f n y-f n x| ≤ C*|y-x|) :
    Control L f := ⟨1,zero_lt_one,le_rfl,C,hC,B,hB,hb,by simpa only [Real.rpow_one] using hc⟩

/-- Composition with an actually Lipschitz scalar function preserves the exponent. -/
def comp_lipschitz (h : Control L f) (F : ℝ → ℝ) (S : Set ℝ)
    (hmap : ∀ n x, x ∈ Icc 0 L → f n x ∈ S)
    (D M : ℝ) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hb : ∀ x ∈ S, |F x| ≤ D)
    (hl : ∀ x ∈ S, ∀ y ∈ S, |F y-F x| ≤ M*|y-x|) :
    Control L (fun n x => F (f n x)) where
  exponent := h.exponent
  exponent_pos := h.exponent_pos
  exponent_le_one := h.exponent_le_one
  constant := M*h.constant
  constant_nonneg := mul_nonneg hM h.constant_nonneg
  bound := D
  bound_nonneg := hD
  bounded := fun n x hx => hb _ (hmap n x hx)
  modulus := by
    intro n x hx y hy
    exact (hl _ (hmap n x hx) _ (hmap n y hy)).trans (by
      nlinarith [mul_le_mul_of_nonneg_left (h.modulus n x hx y hy) hM])

/-- Compact derivative control of an actual real power away from zero,
or at zero when the exponent is at least one. -/
theorem scalar_rpow_lipschitz (p A B : ℝ) (_hA : 0 ≤ A)
    (hp : A > 0 ∨ 1 ≤ p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc A B, ∀ y ∈ Icc A B,
      |y^p-x^p| ≤ M*|y-x| := by
  have hc : ContinuousOn (fun x : ℝ => p*x^(p-1)) (Icc A B) :=
    continuousOn_const.mul (continuousOn_id.rpow_const (fun x hx => by
      rcases hp with ha | hp
      · exact Or.inl (ne_of_gt (ha.trans_le hx.1))
      · exact Or.inr (by linarith)))
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro x hx y hy
  have hd : ∀ t ∈ Icc A B, HasDerivWithinAt (fun z : ℝ => z^p) (p*t^(p-1)) (Icc A B) t := by
    intro t ht
    have hh := (hasDerivWithinAt_id t (Icc A B)).rpow_const (p := p) (by
      rcases hp with ha | hp
      · exact Or.inl (ne_of_gt (ha.trans_le ht.1))
      · exact Or.inr hp)
    simpa only [one_mul, id_eq] using hh
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (fun t ht => (hM t ht).trans (le_max_left _ _)) (convex_Icc _ _) hx hy

/-- Actual nonnegative powers preserve a common bounded Hölder modulus.
The sublinear case uses the proved concave-power difference inequality. -/
theorem exists_rpow (h : Control L f) (p : ℝ) (hp : 0 ≤ p)
    (hf : ∀ n x, x ∈ Icc 0 L → 0 ≤ f n x) : Nonempty (Control L (fun n x => f n x^p)) := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · subst p
    simpa only [Real.rpow_zero] using (⟨const L 1⟩ : Nonempty (Control (ι := ι) L (fun _ _ => (1 : ℝ))))
  by_cases hp1 : p ≤ 1
  · refine ⟨⟨h.exponent*p,mul_pos h.exponent_pos hp0,
      (mul_le_mul h.exponent_le_one hp1 hp0.le zero_le_one).trans_eq (one_mul 1),
      h.constant^p,Real.rpow_nonneg h.constant_nonneg _,h.bound^p,
      Real.rpow_nonneg h.bound_nonneg _,?_,?_⟩⟩
    · intro n x hx
      rw [abs_of_nonneg (Real.rpow_nonneg (hf n x hx) _)]
      exact Real.rpow_le_rpow (hf n x hx) ((le_abs_self _).trans (h.bounded n x hx)) hp
    · intro n x hx y hy
      calc |f n y^p-f n x^p| ≤ |f n y-f n x|^p := rpow_difference hp0 hp1 (hf n x hx) (hf n y hy)
        _ ≤ (h.constant*|y-x|^h.exponent)^p := Real.rpow_le_rpow (abs_nonneg _) (h.modulus n x hx y hy) hp
        _ = h.constant^p*|y-x|^(h.exponent*p) := by
          rw [Real.mul_rpow h.constant_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
            Real.rpow_mul (abs_nonneg _)]
  · obtain ⟨M,hM,hml⟩ := scalar_rpow_lipschitz p 0 h.bound le_rfl (Or.inr (le_of_not_ge hp1))
    exact ⟨h.comp_lipschitz (fun t => t^p) (Icc 0 h.bound)
      (fun n x hx => ⟨hf n x hx,(le_abs_self _).trans (h.bounded n x hx)⟩)
      (h.bound^p) M (Real.rpow_nonneg h.bound_nonneg _) hM
      (fun t ht => by rw [abs_of_nonneg (Real.rpow_nonneg ht.1 _)]; exact Real.rpow_le_rpow ht.1 ht.2 hp) hml⟩

/-- Arbitrary powers of a uniformly positive base have an actual common
Hölder modulus, with their scalar derivative bound derived on a compact interval. -/
theorem exists_rpow_positive (h : Control L f) (p A : ℝ) (hA : 0 < A)
    (hf : ∀ n x, x ∈ Icc 0 L → A ≤ f n x) : Nonempty (Control L (fun n x => f n x^p)) := by
  obtain ⟨M,hM,hml⟩ := scalar_rpow_lipschitz p A h.bound hA.le (Or.inl hA)
  have hc : ContinuousOn (fun t : ℝ => t^p) (Icc A h.bound) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (hA.trans_le ht.1)))
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨h.comp_lipschitz (fun t => t^p) (Icc A h.bound)
    (fun n x hx => ⟨hf n x hx,(le_abs_self _).trans (h.bounded n x hx)⟩)
    (max D 0) M (le_max_right _ _) hM
    (fun t ht => (hD t ht).trans (le_max_left _ _)) hml⟩

noncomputable def rpow (h : Control L f) (p : ℝ) (hp : 0 ≤ p)
    (hf : ∀ n x, x ∈ Icc 0 L → 0 ≤ f n x) : Control L (fun n x => f n x^p) :=
  Classical.choice (exists_rpow h p hp hf)

noncomputable def rpow_positive (h : Control L f) (p A : ℝ) (hA : 0 < A)
    (hf : ∀ n x, x ∈ Icc 0 L → A ≤ f n x) : Control L (fun n x => f n x^p) :=
  Classical.choice (exists_rpow_positive h p A hA hf)

end Control
end
end ChemotaxisBifurcation.UniformHolderAlgebra
