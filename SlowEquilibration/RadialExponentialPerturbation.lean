-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Bounded radial exponential reweighting is controlled by the true
radial first moment of the original density. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.RadialExponentialPerturbation
open Set MeasureTheory
set_option maxHeartbeats 300000

theorem exp_sub_one_abs_le (s : ℝ) :
    |Real.exp s-1| ≤ Real.exp |s| * |s| := by
  have hf : ∀ u∈Icc (-|s|) |s|,DifferentiableAt ℝ Real.exp u :=
    fun _ _ => Real.differentiable_exp.differentiableAt
  have hb : ∀ u∈Icc (-|s|) |s|,‖deriv Real.exp u‖ ≤ Real.exp |s| := by
    intro u hu
    rw [Real.deriv_exp,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hu.2
  have hzero : (0 : ℝ)∈Icc (-|s|) |s| := ⟨neg_nonpos.mpr (abs_nonneg s),abs_nonneg s⟩
  have hs : s∈Icc (-|s|) |s| := abs_le.mp (le_refl |s|)
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le hf hb (convex_Icc _ _) hzero hs
  simpa only [Real.exp_zero,Real.norm_eq_abs,sub_zero] using hh

theorem bounded_radial_exp_sub_one {m M q k : ℝ} (hk : |k-m| ≤ M) :
    |Real.exp (q*(k-m))-1| ≤ (Real.exp (|q| * M)*|q|)*|k-m| := by
  have hb : |q*(k-m)| ≤ |q| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hk (abs_nonneg q)
  have hh := (exp_sub_one_abs_le (q*(k-m))).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb) (abs_nonneg _))
  exact hh.trans_eq (by rw [abs_mul];ring)

theorem radial_moment_integrable {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hi : IntegrableOn f U) (h0 : ∀ k∈U,0 ≤ f k) {m M : ℝ}
    (hRadius : ∀ k∈U,|k-m| ≤ M) : IntegrableOn (fun k => |k-m| * f k) U := by
  apply (hi.const_mul M).mono'
  · exact (by fun_prop : Continuous (fun k : ℝ => |k-m|)).aestronglyMeasurable.mul hi.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hU] with k hk
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (h0 k hk))]
    exact mul_le_mul_of_nonneg_right (hRadius k hk) (h0 k hk)

theorem radial_exp_integrable {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hi : IntegrableOn f U) (h0 : ∀ k∈U,0 ≤ f k) {m M : ℝ}
    (hRadius : ∀ k∈U,|k-m| ≤ M) (q : ℝ) :
    IntegrableOn (fun k => f k*Real.exp (q*(k-m))) U := by
  apply (hi.mul_const (Real.exp (|q| * M))).mono'
  · exact hi.aestronglyMeasurable.mul
      (by fun_prop : Continuous (fun k : ℝ => Real.exp (q*(k-m)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hU] with k hk
    rw [Real.norm_of_nonneg (mul_nonneg (h0 k hk) (Real.exp_pos _).le)]
    have he : q*(k-m) ≤ |q| * M :=
      (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hRadius k hk) (abs_nonneg q))
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (h0 k hk)

theorem radial_exp_integral_error {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hi : IntegrableOn f U) (h0 : ∀ k∈U,0 ≤ f k) {m M : ℝ}
    (hRadius : ∀ k∈U,|k-m| ≤ M) (q : ℝ) :
    |(∫ k in U,f k*Real.exp (q*(k-m)))-(∫ k in U,f k)| ≤
      (Real.exp (|q| * M)*|q|)*(∫ k in U,|k-m| * f k) := by
  have he := radial_exp_integrable hU hi h0 hRadius q
  have hm := radial_moment_integrable hU hi h0 hRadius
  rw [←integral_sub he hi]
  calc
    _ ≤ ∫ k in U,‖f k*Real.exp (q*(k-m))-f k‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ k in U,(Real.exp (|q| * M)*|q|)*(|k-m| * f k) := by
      apply integral_mono_ae (he.sub hi).norm (hm.const_mul (Real.exp (|q| * M)*|q|))
      filter_upwards [ae_restrict_mem hU] with k hk
      change |f k*Real.exp (q*(k-m))-f k| ≤ _
      have hfactor : f k*Real.exp (q*(k-m))-f k=f k*(Real.exp (q*(k-m))-1) := by ring
      rw [hfactor,abs_mul,abs_of_nonneg (h0 k hk)]
      exact (mul_le_mul_of_nonneg_left (bounded_radial_exp_sub_one (q := q) (hRadius k hk))
        (h0 k hk)).trans_eq (by ring)
    _=_ := integral_const_mul _ _

theorem radial_exp_normalized_error {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hi : IntegrableOn f U) (h0 : ∀ k∈U,0 ≤ f k) {m M : ℝ}
    (hRadius : ∀ k∈U,|k-m| ≤ M) (q : ℝ) (hMass : 0 < ∫ k in U,f k) :
    |(∫ k in U,f k*Real.exp (q*(k-m)))/(∫ k in U,f k)-1| ≤
      (Real.exp (|q| * M)*|q|)*((∫ k in U,|k-m| * f k)/(∫ k in U,f k)) := by
  have he : (∫ k in U,f k*Real.exp (q*(k-m)))/(∫ k in U,f k)-1=
      ((∫ k in U,f k*Real.exp (q*(k-m)))-(∫ k in U,f k))/(∫ k in U,f k) := by
    field_simp
  rw [he,abs_div,abs_of_pos hMass,←mul_div_assoc]
  exact div_le_div_of_nonneg_right (radial_exp_integral_error hU hi h0 hRadius q) hMass.le

end SlowEquilibration.RadialExponentialPerturbation
