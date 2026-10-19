-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Probability.Moments.SubGaussian

/-! A quantitative square-moment consequence of a genuine sub-Gaussian MGF.
The estimate uses both exponential moments at a specified positive scale. -/
@[expose] public section
namespace SlowEquilibration.SubGaussianSecondMoment
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma square_le_exponentials {t : ℝ} (ht : 0 < t) (x : ℝ) :
    x^2 ≤ (2/t^2)*(Real.exp (t*x)+Real.exp (-t*x)) := by
  have hp := Real.pow_div_factorial_le_exp |t*x| (abs_nonneg _) 2
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_ofNat,
    Nat.cast_one,mul_one] at hp
  have he : Real.exp |t*x| ≤ Real.exp (t*x)+Real.exp (-t*x) := by
    rcases le_total 0 (t*x) with h | h
    · rw [abs_of_nonneg h]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_nonpos h]
      have h0:=Real.exp_nonneg (t*x)
      simpa only [neg_mul] using (show Real.exp (-(t*x)) ≤ Real.exp (t*x)+Real.exp (-(t*x)) by linarith)
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hsq : t^2*x^2 ≤ 2*(Real.exp (t*x)+Real.exp (-t*x)) := by
    simp only [sq_abs,mul_pow] at hp
    linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ht2).mpr
  convert hsq using 1 <;> ring

/-- An explicit quantitative bound obtained from the actual two-sided MGF.
No square-moment estimate is supplied as an assumption. -/
theorem square_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x=>X x^2) μ ∧
      (∫ x,X x^2 ∂μ) ≤ 4*Real.exp ((c:ℝ)*t^2/2)/t^2 := by
  have hi := (hX.integrable_exp_mul t).add (hX.integrable_exp_mul (-t))
  have he (x : Ω) : X x^2 ≤ (2/t^2)*
      (Real.exp (t*X x)+Real.exp (-t*X x)) := square_le_exponentials ht (X x)
  have hs : Integrable (fun x=>X x^2) μ :=
    (hi.const_mul (2/t^2)).mono' (hX.aestronglyMeasurable.pow 2)
      (ae_of_all _ (fun x=>by simpa only [Real.norm_of_nonneg (sq_nonneg _), Pi.add_apply] using he x))
  refine ⟨hs,?_⟩
  calc
    _ ≤ ∫ x,(2/t^2)*(Real.exp (t*X x)+Real.exp (-t*X x)) ∂μ :=
      integral_mono hs (hi.const_mul _) he
    _ = (2/t^2)*(mgf X μ t+mgf X μ (-t)) := by
      rw [integral_const_mul]
      congr 1
      exact integral_add (hX.integrable_exp_mul t) (hX.integrable_exp_mul (-t))
    _ ≤ (2/t^2)*(Real.exp ((c:ℝ)*t^2/2)+Real.exp ((c:ℝ)*(-t)^2/2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hX.mgf_le t) (hX.mgf_le (-t))) (by positivity)
    _ = _ := by rw [neg_sq];ring

end
end SlowEquilibration.SubGaussianSecondMoment
