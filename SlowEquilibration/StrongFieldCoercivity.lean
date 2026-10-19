-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.StrongFieldWholeLine

@[expose] public section

/-!
# Actual quadratic tail control for the strong-field exponent

The literal semicircle log integral is bounded using its genuine support and
integrability. A pair of elementary Young inequalities then controls both
the radial variable and the conditional height. No tail bound is assumed.
-/

namespace SlowEquilibration.StrongFieldComplexity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory

theorem potential_le_abs_add_two (u : ℝ) :
    SemicirclePotential.potential u ≤ |u|+2 := by
  have hsupport : ∀ᵐ t ∂SemicirclePotential.law, t ∈ Icc (-2 : ℝ) 2 := by
    rw [ae_iff]
    exact SemicirclePotential.law_supported
  have hpoint : ∀ᵐ t ∂SemicirclePotential.law, Real.log |u-t| ≤ |u|+2 := by
    filter_upwards [hsupport] with t ht
    calc
      Real.log |u-t| ≤ |u-t| := Real.log_le_self (abs_nonneg _)
      _ ≤ |u|+|t| := abs_sub _ _
      _ ≤ |u|+2 := by
        exact add_le_add le_rfl (abs_le.mpr ht)
  have h := integral_mono_ae (SemicircleWholeLine.log_abs_integrable u)
    (integrable_const (|u|+2)) hpoint
  simpa [SemicirclePotential.potential] using h

lemma linear_radial_young {A b k : ℝ} (hA : 0 < A) (hb : 0 < b) :
    |k|/Real.sqrt b ≤ k^2/(4*A)+A/b := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  have hlinear : |k|/Real.sqrt b = |k| * Real.sqrt b/b := by
    apply (div_eq_div_iff hs.ne' hb.ne').mpr
    calc
      |k| * b = |k| * (Real.sqrt b)^2 := by rw [hs2]
      _ = (|k| * Real.sqrt b)*Real.sqrt b := by ring
  have heq : k^2/(4*A)+A/b-|k|/Real.sqrt b =
      (|k| * Real.sqrt b-2*A)^2/(4*A*b) := by
    rw [hlinear, sub_sq, mul_pow, hs2, sq_abs]
    field_simp
    ring
  have hnonneg : 0 ≤ (|k| * Real.sqrt b-2*A)^2/(4*A*b) := by positivity
  rw [← heq] at hnonneg
  linarith

/-- Explicit positive lower coefficient for the two-dimensional precision
quadratic form. -/
def precisionCoefficient (A variance α : ℝ) : ℝ :=
  min (1/(4*A*(1+2*α^2))) (1/(4*variance))

theorem precisionCoefficient_pos {A variance α : ℝ} (hA : 0 < A)
    (hvariance : 0 < variance) : 0 < precisionCoefficient A variance α := by
  unfold precisionCoefficient
  apply lt_min <;> positivity

theorem quadratic_penalty_ge {A variance α h k : ℝ} (hA : 0 < A)
    (hvariance : 0 < variance) :
    precisionCoefficient A variance α*(h^2+k^2) ≤
      k^2/(4*A)+(h-α*k)^2/(2*variance) := by
  let c := precisionCoefficient A variance α
  have hc : 0 < c := precisionCoefficient_pos hA hvariance
  have hm1 : c ≤ 1/(4*A*(1+2*α^2)) := min_le_left _ _
  have hm2 : c ≤ 1/(4*variance) := min_le_right _ _
  have hcm1 : c*(1+2*α^2) ≤ 1/(4*A) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*A)).mpr
    have h := (le_div_iff₀ (by positivity : 0 < 4*A*(1+2*α^2))).mp hm1
    nlinarith
  have hcm2 : 2*c ≤ 1/(2*variance) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*variance)).mpr
    have h := (le_div_iff₀ (by positivity : 0 < 4*variance)).mp hm2
    nlinarith
  have hh : h^2+k^2 ≤ (1+2*α^2)*k^2+2*(h-α*k)^2 := by
    nlinarith [sq_nonneg (h-2*α*k)]
  have hkbound := mul_le_mul_of_nonneg_right hcm1 (sq_nonneg k)
  have hhbound := mul_le_mul_of_nonneg_right hcm2 (sq_nonneg (h-α*k))
  have hboth := mul_le_mul_of_nonneg_left hh hc.le
  change c*(h^2+k^2) ≤ _
  calc
    c*(h^2+k^2) ≤ c*((1+2*α^2)*k^2+2*(h-α*k)^2) := hboth
    _ = c*(1+2*α^2)*k^2+2*c*(h-α*k)^2 := by ring
    _ ≤ k^2/(4*A)+(h-α*k)^2/(2*variance) := by
      convert add_le_add hkbound hhbound using 1
      ring

/-- Explicit finite tail constant; absolute value ensures positivity. -/
def coercivityConstant (a b : ℝ) : ℝ :=
  |5/2+Real.log (b/a)/2+(a+b)/b|+1

theorem coercivityConstant_pos (a b : ℝ) : 0 < coercivityConstant a b := by
  unfold coercivityConstant
  positivity

/-- Genuine global quadratic coercivity for the actual BCNS exponent,
valid at every height and radial variable, including both spectral edges. -/
theorem exponent_le_quadratic_coercivity {a b variance : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance) (h k : ℝ) :
    exponent a b variance h k ≤ coercivityConstant a b -
      precisionCoefficient (a+b) variance (a/(a+b))*(h^2+k^2) := by
  have hA : 0 < a+b := by linarith
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hp := potential_le_abs_add_two (k/Real.sqrt b)
  rw [abs_div, abs_of_pos hs] at hp
  have hy := linear_radial_young (k := k) hA hb
  have hq := quadratic_penalty_ge (α := a/(a+b)) (h := h) (k := k) hA hvariance
  have hcoef : k^2/(2*(a+b)) = k^2/(4*(a+b))+k^2/(4*(a+b)) := by
    field_simp
    ring
  have hmean : a/(a+b)*k = a*k/(a+b) := by ring
  rw [hmean] at hq
  have hC : 5/2+Real.log (b/a)/2+(a+b)/b ≤ coercivityConstant a b := by
    unfold coercivityConstant
    linarith [le_abs_self (5/2+Real.log (b/a)/2+(a+b)/b)]
  unfold exponent
  rw [hcoef]
  linarith

end
end SlowEquilibration.StrongFieldComplexity
