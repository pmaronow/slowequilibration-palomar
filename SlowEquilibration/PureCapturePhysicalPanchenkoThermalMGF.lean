-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPanchenkoQuenchedEnergy
public import Mathlib.Analysis.Convex.Integral

/-! A fixed-temperature thermal deviation bound from two exponential moments.
The two moments are later identified with the physical log-partition second
difference. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoThermalMGF

open MeasureTheory Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem centered_absolute_integral_le_log_mgfs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f P)
    (δ : ℝ)
    (hplus : Integrable (fun x => Real.exp (δ * f x)) P)
    (hminus : Integrable (fun x => Real.exp (-δ * f x)) P)
    (hzero : (∫ x, f x ∂P) = 0) :
    δ * (∫ x, |f x| ∂P) ≤
      Real.log 2 +
        Real.log (∫ x, Real.exp (δ * f x) ∂P) +
        Real.log (∫ x, Real.exp (-δ * f x) ∂P) := by
  let A := ∫ x, Real.exp (δ * f x) ∂P
  let B := ∫ x, Real.exp (-δ * f x) ∂P
  have hA : 0 < A := integral_exp_pos hplus
  have hB : 0 < B := integral_exp_pos hminus
  have hplusOne : 1 ≤ A := by
    have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
      isClosed_univ (ae_of_all P fun _ => mem_univ _)
      (hfi.const_mul δ) hplus
    simpa only [integral_const_mul, hzero, mul_zero, Real.exp_zero] using h
  have hminusOne : 1 ≤ B := by
    have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
      isClosed_univ (ae_of_all P fun _ => mem_univ _)
      (hfi.const_mul (-δ)) hminus
    simpa only [integral_const_mul, hzero, mul_zero, Real.exp_zero] using h
  have hExpAbs : Integrable (fun x => Real.exp (δ * |f x|)) P := by
    apply (hplus.add hminus).mono'
      ((hf.abs.const_mul δ).exp).aestronglyMeasurable
    exact .of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      rcases le_total 0 (f x) with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_nonpos hx]
        have heq : δ * -(f x) = -δ * f x := by ring
        rw [heq]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (ae_of_all P fun _ => mem_univ _)
    ((hfi.norm).const_mul δ) hExpAbs
  have hExpIntegral : Real.exp (δ * (∫ x, |f x| ∂P)) ≤ A + B := by
    simpa only [Real.norm_eq_abs, Pi.add_apply, integral_const_mul,
      integral_add hplus hminus] using
      hj.trans (integral_mono hExpAbs (hplus.add hminus) (fun x => by
        rcases le_total 0 (f x) with hx | hx
        · rw [Real.norm_eq_abs, abs_of_nonneg hx]
          change Real.exp (δ * f x) ≤ Real.exp (δ * f x) + Real.exp (-δ * f x)
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [Real.norm_eq_abs, abs_of_nonpos hx]
          have heq : δ * -(f x) = -δ * f x := by ring
          rw [heq]
          change Real.exp (-δ * f x) ≤ Real.exp (δ * f x) + Real.exp (-δ * f x)
          exact le_add_of_nonneg_left (Real.exp_pos _).le))
  have hAB : A + B ≤ 2 * (A * B) := by nlinarith [mul_nonneg (sub_nonneg.mpr hplusOne) (sub_nonneg.mpr hminusOne)]
  have hlog := Real.log_le_log (Real.exp_pos _) (hExpIntegral.trans hAB)
  rw [Real.log_exp, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_ne_zero hA.ne' hB.ne'),
      Real.log_mul hA.ne' hB.ne'] at hlog
  simpa only [A, B, add_assoc] using hlog

end SlowEquilibration.PureCapturePhysicalPanchenkoThermalMGF
