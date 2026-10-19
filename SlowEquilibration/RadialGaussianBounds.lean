-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual one-dimensional Gaussian integrals for the radial Laplace step.
The bounds retain their exact square-root dimensional normalization. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.RadialGaussianBounds
open Set MeasureTheory Filter
open scoped Topology ENNReal
set_option maxHeartbeats 300000

/-- The literal Gaussian envelope, including its radial center. -/
def gaussian (a m x : ℝ) : ℝ := Real.exp (-a*(x-m)^2)

theorem gaussian_integrable {a : ℝ} (ha : 0<a) (m : ℝ) :
    Integrable (gaussian a m) :=
  (integrable_exp_neg_mul_sq ha).comp_sub_right m

theorem gaussian_integral (a m : ℝ) :
    (∫ x : ℝ,gaussian a m x)=Real.sqrt (Real.pi/a) := by
  unfold gaussian
  exact (integral_sub_right_eq_self (fun x : ℝ => Real.exp (-a*x^2)) m).trans
    (integral_gaussian a)

/-- A Gaussian tail has its full square-root prefactor and a quadratic
exponential loss, without an asymptotic error term. -/
theorem gaussian_tail_le {a : ℝ} (ha : 0<a) (m t : ℝ) (ht : 0≤t) :
    (∫ x in {x : ℝ | t≤|x-m|},gaussian a m x)≤
      Real.sqrt (Real.pi/(a/2))*Real.exp (-(a/2)*t^2) := by
  have hs : MeasurableSet {x : ℝ | t≤|x-m|} := measurableSet_le measurable_const (by fun_prop)
  have hg := (gaussian_integrable (half_pos ha) m).const_mul
    (Real.exp (-(a/2)*t^2))
  have hp (x : ℝ) (hx : x∈{x : ℝ | t≤|x-m|}) :
      gaussian a m x≤Real.exp (-(a/2)*t^2)*gaussian (a/2) m x := by
    unfold gaussian
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh : t^2≤(x-m)^2 := by
      have hb := pow_le_pow_left₀ ht hx 2
      simpa only [sq_abs] using hb
    nlinarith
  calc
    _≤∫ x in {x : ℝ | t≤|x-m|},Real.exp (-(a/2)*t^2)*gaussian (a/2) m x :=
      setIntegral_mono_on ((gaussian_integrable ha m).restrict) (hg.restrict) hs hp
    _≤∫ x : ℝ,Real.exp (-(a/2)*t^2)*gaussian (a/2) m x :=
      setIntegral_le_integral hg (ae_of_all _ (fun _ => by unfold gaussian;positivity))
    _=_ := by rw [integral_const_mul,gaussian_integral];ring

/-- A pointwise first-moment envelope useful after exact Gaussian energy
reweighting. It holds uniformly in the radial center. -/
theorem gaussian_moment_envelope {a : ℝ} (ha : 0<a) (m x : ℝ) :
    |x-m| * gaussian a m x≤gaussian (a/2) m x/Real.sqrt a := by
  have hs : 0<Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq := Real.sq_sqrt ha.le
  have hu : Real.sqrt a*|x-m|≤Real.exp ((a/2)*(x-m)^2) := by
    have hsmall : Real.sqrt a*|x-m|≤1+(a/2)*(x-m)^2 := by
      nlinarith [sq_nonneg (Real.sqrt a*|x-m|-1),sq_abs (x-m)]
    exact hsmall.trans (by simpa only [add_comm] using Real.add_one_le_exp ((a/2)*(x-m)^2))
  apply (le_div_iff₀ hs).mpr
  unfold gaussian
  calc
    _=(Real.sqrt a*|x-m|)*Real.exp (-a*(x-m)^2) := by ring
    _≤Real.exp ((a/2)*(x-m)^2)*Real.exp (-a*(x-m)^2) :=
      mul_le_mul_of_nonneg_right hu (Real.exp_pos _).le
    _=_ := by rw [←Real.exp_add];congr 1;ring

theorem gaussian_moment_integrable {a : ℝ} (ha : 0<a) (m : ℝ) :
    Integrable (fun x : ℝ => |x-m| * gaussian a m x) := by
  apply ((gaussian_integrable (half_pos ha) m).div_const (Real.sqrt a)).mono'
  · exact (by unfold gaussian;fun_prop : Continuous (fun x : ℝ => |x-m| * gaussian a m x)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (show 0≤gaussian a m x by unfold gaussian;positivity))]
    exact gaussian_moment_envelope ha m x

theorem gaussian_first_moment_le {a : ℝ} (ha : 0<a) (m : ℝ) :
    (∫ x : ℝ,|x-m| * gaussian a m x)≤Real.sqrt (Real.pi/(a/2))/Real.sqrt a := by
  calc
    _≤∫ x : ℝ,gaussian (a/2) m x/Real.sqrt a := integral_mono
      (gaussian_moment_integrable ha m)
      ((gaussian_integrable (half_pos ha) m).div_const (Real.sqrt a))
      (gaussian_moment_envelope ha m)
    _=_ := by rw [integral_div,gaussian_integral]

/-- Every actual nonnegative integrable radial density under a Gaussian
pointwise envelope inherits the correct normalization upper bound. -/
theorem density_integral_upper {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hf : IntegrableOn f U) {A a m : ℝ} (hA : 0≤A) (ha : 0<a)
    (henv : ∀ x∈U,f x≤A*gaussian a m x) :
    (∫ x in U,f x)≤A*Real.sqrt (Real.pi/a) := by
  have hg := (gaussian_integrable ha m).const_mul A
  calc
    _≤∫ x in U,A*gaussian a m x := setIntegral_mono_on hf (hg.restrict) hU henv
    _≤∫ x : ℝ,A*gaussian a m x := setIntegral_le_integral hg
      (ae_of_all _ (fun _ => mul_nonneg hA (Real.exp_pos _).le))
    _=_ := by rw [integral_const_mul,gaussian_integral]

/-- The normalization lower bound is a genuine interval integral. No
normalization or Gaussian probability estimate is supplied as an input. -/
theorem density_integral_lower {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hf : IntegrableOn f U) (hf0 : ∀ x∈U,0≤f x)
    {A m w : ℝ} (hw : 0≤w) (hInside : Icc (m-w) (m+w)⊆U)
    (hl : ∀ x∈Icc (m-w) (m+w),A≤f x) :
    2*w*A≤∫ x in U,f x := by
  have hI : m-w≤m+w := by linarith
  have hConst : (∫ _ : ℝ in Icc (m-w) (m+w),A)=2*w*A := by
    rw [setIntegral_const,Real.volume_real_Icc_of_le hI,smul_eq_mul]
    ring
  rw [←hConst]
  apply (setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Icc];exact ENNReal.ofReal_ne_top))
    (hf.mono_set hInside) measurableSet_Icc hl).trans
  exact setIntegral_mono_set hf (ae_restrict_of_forall_mem hU hf0)
    (Eventually.of_forall fun _ hx => hInside hx)
end SlowEquilibration.RadialGaussianBounds
