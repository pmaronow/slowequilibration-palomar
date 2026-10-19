-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemicirclePotential
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# The scalar strong-field critical-point exponent

The potential in this module is the actual semicircle-density logarithmic
integral. The strong-field ratio is `t = a / b > 1`; the normalized radial
variable is `u = k / sqrt b`. No critical-point count formula is assumed here.
-/

namespace SlowEquilibration.StrongFieldComplexity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory

/-- The radial part of the BCNS exponent in dimensionless variables. -/
def radial (t u : ℝ) : ℝ :=
  (1 - Real.log t) / 2 + SemicirclePotential.potential u - u ^ 2 / (2 * (t + 1))

/-- Positive endpoint of the strong-field radial critical-point exponent. -/
def endpoint (t : ℝ) : ℝ := (t + 1) / Real.sqrt t

lemma endpoint_pos {t : ℝ} (ht : 1 < t) : 0 < endpoint t := by
  unfold endpoint
  positivity

lemma endpoint_sq {t : ℝ} (ht : 1 < t) : (endpoint t) ^ 2 = (t + 1) ^ 2 / t := by
  rw [endpoint, div_pow, Real.sq_sqrt (by linarith : 0 ≤ t)]

lemma endpoint_gt_two {t : ℝ} (ht : 1 < t) : 2 < endpoint t := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ t)
  have hr := Real.sqrt_nonneg t
  rw [endpoint, lt_div_iff₀ (Real.sqrt_pos.mpr (by linarith : 0 < t))]
  nlinarith [sq_pos_of_pos (by linarith : 0 < t - 1)]

lemma sqrt_endpoint {t : ℝ} (ht : 1 < t) :
    Real.sqrt ((endpoint t)^2 - 4) = (t - 1) / Real.sqrt t := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs := Real.sq_sqrt ht0.le
  have he := endpoint_gt_two ht
  apply (Real.sqrt_eq_iff_eq_sq (by nlinarith : 0 ≤ (endpoint t)^2 - 4)
    (by positivity : 0 ≤ (t - 1) / Real.sqrt t)).mpr
  rw [endpoint, div_pow, div_pow]
  field_simp
  nlinarith

theorem radial_endpoint {t : ℝ} (ht : 1 < t) : radial t (endpoint t) = 0 := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs := Real.sq_sqrt ht0.le
  have hlogarg : (endpoint t + Real.sqrt ((endpoint t)^2 - 4))/2 = Real.sqrt t := by
    rw [sqrt_endpoint ht, endpoint]
    field_simp
    nlinarith
  rw [radial, SemicirclePotential.potential_explicit (endpoint_gt_two ht), hlogarg,
    Real.log_sqrt ht0.le, sqrt_endpoint ht, endpoint]
  field_simp
  nlinarith

theorem radial_hasDerivAt {t u : ℝ} (hu : 2 < u) :
    HasDerivAt (radial t)
      ((u - Real.sqrt (u^2 - 4))/2 - u/(t+1)) u := by
  have hd := (hasDerivAt_const u ((1 - Real.log t)/2)).add
    (SemicirclePotential.potential_hasDerivAt_explicit hu)
  have hp := ((hasDerivAt_id u).pow 2).div_const (2*(t+1))
  have hp' : HasDerivAt (fun v : ℝ => v^2/(2*(t+1))) (u/(t+1)) u := by
    convert hp using 1
    · rfl
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one,
        mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  convert hd.sub hp' using 1
  · rfl
  · simp only [zero_add]

lemma radial_deriv_pos {t u : ℝ} (ht : 1 < t) (hu : 2 < u)
    (hue : u < endpoint t) : 0 < deriv (radial t) u := by
  rw [(radial_hasDerivAt hu).deriv]
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t+1 := by linarith
  have hroot := Real.sqrt_nonneg (u^2-4)
  have hsq := Real.sq_sqrt (by nlinarith : 0 ≤ u^2-4)
  have he := endpoint_pos ht
  have huSq : u^2 < (endpoint t)^2 := by nlinarith
  rw [endpoint_sq ht] at huSq
  have hprod := (lt_div_iff₀ ht0).mp huSq
  have hnum : (t+1)*Real.sqrt (u^2-4) < u*(t-1) := by
    have hn0 : 0 < u*(t-1) := mul_pos (by linarith) (by linarith)
    have hl0 : 0 ≤ (t+1)*Real.sqrt (u^2-4) := mul_nonneg ht1.le hroot
    nlinarith [sq_nonneg ((t+1)*Real.sqrt (u^2-4)+u*(t-1))]
  apply (sub_pos).mpr
  apply (div_lt_iff₀ ht1).mpr
  nlinarith

lemma radial_deriv_neg {t u : ℝ} (ht : 1 < t) (hue : endpoint t < u) :
    deriv (radial t) u < 0 := by
  have hu : 2 < u := (endpoint_gt_two ht).trans hue
  rw [(radial_hasDerivAt hu).deriv]
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t+1 := by linarith
  have hroot := Real.sqrt_nonneg (u^2-4)
  have hsq := Real.sq_sqrt (by nlinarith : 0 ≤ u^2-4)
  have he := endpoint_pos ht
  have huSq : (endpoint t)^2 < u^2 := by nlinarith
  rw [endpoint_sq ht] at huSq
  have hprod := (div_lt_iff₀ ht0).mp huSq
  have hnum : u*(t-1) < (t+1)*Real.sqrt (u^2-4) := by
    have hn0 : 0 < u*(t-1) := mul_pos (by linarith) (by linarith)
    have hl0 : 0 ≤ (t+1)*Real.sqrt (u^2-4) := mul_nonneg ht1.le hroot
    nlinarith [sq_nonneg ((t+1)*Real.sqrt (u^2-4)+u*(t-1))]
  apply (sub_neg).mpr
  apply (lt_div_iff₀ ht1).mpr
  nlinarith

theorem radial_strictMonoOn {t : ℝ} (ht : 1 < t) :
    StrictMonoOn (radial t) (Ioc 2 (endpoint t)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
  · intro u hu
    exact (radial_hasDerivAt hu.1).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u ∈ Ioo 2 (endpoint t) := by simpa only [interior_Ioc] using hu
    exact radial_deriv_pos ht hu'.1 hu'.2

theorem radial_strictAntiOn {t : ℝ} (ht : 1 < t) :
    StrictAntiOn (radial t) (Ici (endpoint t)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro u hu
    exact (radial_hasDerivAt ((endpoint_gt_two ht).trans_le hu)).continuousAt.continuousWithinAt
  · intro u hu
    have hue : endpoint t < u := by simpa only [interior_Ici, mem_Ioi] using hu
    exact radial_deriv_neg ht hue

/-- The literal outside-edge potential gives a strict radial gap except at
the true strong-field endpoint. -/
theorem radial_lt_zero_of_ne_endpoint {t u : ℝ} (ht : 1 < t) (hu : 2 < u)
    (hne : u ≠ endpoint t) : radial t u < 0 := by
  rcases lt_or_gt_of_ne hne with hl | hg
  · have h := radial_strictMonoOn ht ⟨hu, hl.le⟩
      ⟨endpoint_gt_two ht, le_rfl⟩ hl
    rwa [radial_endpoint ht] at h
  · have h := radial_strictAntiOn ht (show endpoint t ∈ Ici (endpoint t) from le_rfl)
      (show u ∈ Ici (endpoint t) from hg.le) hg
    rwa [radial_endpoint ht] at h

theorem radial_nonpos {t u : ℝ} (ht : 1 < t) (hu : 2 < u) : radial t u ≤ 0 := by
  by_cases he : u = endpoint t
  · rw [he, radial_endpoint ht]
  · exact (radial_lt_zero_of_ne_endpoint ht hu he).le

theorem radial_eq_zero_iff {t u : ℝ} (ht : 1 < t) (hu : 2 < u) :
    radial t u = 0 ↔ u = endpoint t := by
  constructor
  · intro hz
    by_contra he
    have hn := radial_lt_zero_of_ne_endpoint ht hu he
    linarith
  · intro he
    rw [he, radial_endpoint ht]

/-- The exact logarithmic inequality giving a strict strong-field margin
in the inner spectral interval. -/
theorem log_ratio_gt {t : ℝ} (ht : 1 < t) :
    2*(t-1)/(t+1) < Real.log t := by
  let x := (t-1)/(t+1)
  have ht1 : 0 < t+1 := by linarith
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    dsimp [x]
    apply (div_lt_iff₀ ht1).mpr
    linarith
  have harg : (1+x)/(1-x) = t := by
    dsimp [x]
    field_simp
    ring
  have h := Real.sum_range_le_log_div hx0.le hx1 2
  rw [harg] at h
  norm_num [Finset.sum_range_succ] at h
  have hx3 : 0 < x^3 := pow_pos hx0 3
  have hstrict : 2*x < Real.log t := by linarith
  convert hstrict using 1
  dsimp [x]
  ring

/-- The inner quadratic branch of the semicircle formula gives a strict
negative exponent everywhere in the spectral interval. This is a scalar
calculation, kept separate from the literal inner-integral identity. -/
theorem innerQuadraticRadial_lt_zero {t u : ℝ} (ht : 1 < t) (hu : |u| ≤ 2) :
    (1-Real.log t)/2 + (u^2/4-1/2) - u^2/(2*(t+1)) < 0 := by
  have ht1 : 0 < t+1 := by linarith
  have hlog := (div_lt_iff₀ ht1).mp (log_ratio_gt ht)
  have hu2 : u^2 ≤ 4 := by
    have h := abs_le.mp hu
    nlinarith [sq_nonneg (u-2), sq_nonneg (u+2)]
  have hprod : u^2*(t-1) ≤ 4*(t-1) :=
    mul_le_mul_of_nonneg_right hu2 (by linarith)
  have heq : (1-Real.log t)/2 + (u^2/4-1/2) - u^2/(2*(t+1)) =
      (-2*(t+1)*Real.log t+u^2*(t-1))/(4*(t+1)) := by
    field_simp
    ring
  rw [heq]
  apply div_neg_of_neg_of_pos _ (by positivity : 0 < 4*(t+1))
  nlinarith

/-- Literal BCNS exponent, including the conditional height variance.
`variance` denotes the source's `J²`, rather than its square root. -/
def exponent (a b variance h k : ℝ) : ℝ :=
  1/2 + Real.log (b/a)/2 + SemicirclePotential.potential (k/Real.sqrt b) -
    k^2/(2*(a+b)) - (h-a*k/(a+b))^2/(2*variance)

def radialEndpoint (a b : ℝ) : ℝ := (a+b)/Real.sqrt a

lemma ratio_gt_one {a b : ℝ} (hb : 0 < b) (hab : b < a) : 1 < a/b := by
  apply (lt_div_iff₀ hb).mpr
  simpa using hab

lemma radial_physical {a b k : ℝ} (hb : 0 < b) (hab : b < a) :
    radial (a/b) (k/Real.sqrt b) =
      1/2 + Real.log (b/a)/2 + SemicirclePotential.potential (k/Real.sqrt b) -
        k^2/(2*(a+b)) := by
  have ha : 0 < a := hb.trans hab
  have hs : (Real.sqrt b)^2 = b := Real.sq_sqrt hb.le
  have hlog : Real.log (a/b) = -Real.log (b/a) := by
    rw [show a/b = (b/a)⁻¹ by field_simp, Real.log_inv]
  unfold radial
  rw [hlog]
  field_simp
  nlinarith

lemma radialEndpoint_normalized {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    radialEndpoint a b / Real.sqrt b = endpoint (a/b) := by
  have ha : 0 < a := hb.trans hab
  have hs : (Real.sqrt b)^2 = b := Real.sq_sqrt hb.le
  rw [endpoint, Real.sqrt_div ha.le]
  unfold radialEndpoint
  field_simp
  nlinarith

lemma endpoint_height {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    a*radialEndpoint a b/(a+b) = Real.sqrt a := by
  have ha : 0 < a := hb.trans hab
  have hs : (Real.sqrt a)^2 = a := Real.sq_sqrt ha.le
  unfold radialEndpoint
  field_simp
  nlinarith

/-- Actual strong-field exponent bound in the positive outside-edge region. -/
theorem exponent_nonpos_pos_outside {a b variance h k : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    (hk : 2*Real.sqrt b < k) : exponent a b variance h k ≤ 0 := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hu : 2 < k/Real.sqrt b := (lt_div_iff₀ hs).mpr hk
  have hg := radial_nonpos (ratio_gt_one hb hab) hu
  rw [radial_physical hb hab] at hg
  have ht : 0 ≤ (h-a*k/(a+b))^2/(2*variance) := by positivity
  unfold exponent
  linarith

/-- The true positive endpoint is the only zero outside the spectral edge;
the conditional-height term also forces the physical height `sqrt a`. -/
theorem exponent_eq_zero_iff_pos_outside {a b variance h k : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    (hk : 2*Real.sqrt b < k) :
    exponent a b variance h k = 0 ↔
      k = radialEndpoint a b ∧ h = Real.sqrt a := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hu : 2 < k/Real.sqrt b := (lt_div_iff₀ hs).mpr hk
  have ht := ratio_gt_one hb hab
  have hg := radial_nonpos ht hu
  have htail : 0 ≤ (h-a*k/(a+b))^2/(2*variance) := by positivity
  have heq : exponent a b variance h k =
      radial (a/b) (k/Real.sqrt b) - (h-a*k/(a+b))^2/(2*variance) := by
    rw [radial_physical hb hab]
    rfl
  constructor
  · intro hz
    rw [heq] at hz
    have hg0 : radial (a/b) (k/Real.sqrt b) = 0 := by linarith
    have hk0 := (radial_eq_zero_iff ht hu).mp hg0
    rw [← radialEndpoint_normalized hb hab] at hk0
    have hke : k = radialEndpoint a b := (div_left_inj' hs.ne').mp hk0
    have hzero : (h-a*k/(a+b))^2 = 0 := by
      have htail0 : (h-a*k/(a+b))^2/(2*variance) = 0 := by linarith
      exact (div_eq_zero_iff).mp htail0 |>.resolve_right (by positivity)
    have hm : h = a*k/(a+b) := by nlinarith [sq_nonneg (h-a*k/(a+b))]
    refine ⟨hke, ?_⟩
    rw [hke, endpoint_height hb hab] at hm
    exact hm
  · rintro ⟨rfl, rfl⟩
    rw [heq, endpoint_height hb hab, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_div, sub_zero, radialEndpoint_normalized hb hab, radial_endpoint ht]

theorem exponent_continuousOn_pos_outside (a b variance : ℝ) (hb : 0 < b) :
    ContinuousOn (fun z : ℝ × ℝ => exponent a b variance z.1 z.2)
      {z | 2*Real.sqrt b < z.2} := by
  intro z hz
  have hu : 2 < z.2/Real.sqrt b :=
    (lt_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr hz
  have hp : ContinuousAt (fun w : ℝ × ℝ => SemicirclePotential.potential (w.2/Real.sqrt b)) z :=
    (SemicirclePotential.potential_hasDerivAt_explicit hu).continuousAt.comp
      (f := fun w : ℝ × ℝ => w.2/Real.sqrt b)
      (continuous_snd.div_const (Real.sqrt b)).continuousAt
  have hc : ContinuousAt (fun z : ℝ × ℝ => exponent a b variance z.1 z.2) z := by
    unfold exponent
    fun_prop
  exact hc.continuousWithinAt

/-- A strict uniform compact gap follows from the actual exponent and its
unique endpoint. No uniform exponent bound is an input. -/
theorem exists_uniform_exponent_gap_pos_outside {a b variance : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hregion : ∀ z ∈ K, 2*Real.sqrt b < z.2)
    (hheight : ∀ z ∈ K, z.1 ≠ Real.sqrt a) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K, exponent a b variance z.1 z.2 ≤ -η := by
  by_cases hne : K.Nonempty
  · have hcont := (exponent_continuousOn_pos_outside a b variance hb).mono hregion
    obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne hcont
    have hle := exponent_nonpos_pos_outside (h := z.1) hb hab hvariance (hregion z hz)
    have hstrict : exponent a b variance z.1 z.2 < 0 := by
      apply lt_of_le_of_ne hle
      intro heq
      have he := (exponent_eq_zero_iff_pos_outside hb hab hvariance (hregion z hz)).mp heq
      exact hheight z hz he.2
    refine ⟨-exponent a b variance z.1 z.2/2, by linarith, ?_⟩
    intro w hw
    have hm : exponent a b variance w.1 w.2 ≤ exponent a b variance z.1 z.2 := hmax hw
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact (hne ⟨z, hz⟩).elim

end
end SlowEquilibration.StrongFieldComplexity
