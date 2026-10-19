-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Real moments from an ordinary integer moment on a probability space. -/
@[expose] public section
namespace SlowEquilibration.NonnegativeRealMoment
noncomputable section
open MeasureTheory ProbabilityTheory

lemma rpow_le_one_add_pow {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q)
    (r : ℕ) (hqr : q ≤ (r:ℝ)) : x^q ≤ 1+x^r := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx hx1 hq).trans (le_add_of_nonneg_right (pow_nonneg hx _))
  · have h:=Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hqr
    rw [Real.rpow_natCast] at h
    exact h.trans (le_add_of_nonneg_left (by norm_num))

/-- No integrability convention is hidden: the real power is dominated by
an integrable ordinary integer power. -/
theorem real_moment_of_integer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {q : ℝ} (hq : 0 ≤ q) (r : ℕ) (hqr : q ≤ (r:ℝ))
    (hI : Integrable (fun x=>f x^r) μ) :
    Integrable (fun x=>f x^q) μ ∧
      (∫ x,f x^q ∂μ) ≤ 1+(∫ x,f x^r ∂μ) := by
  have hdom : Integrable (fun x=>1+f x^r) μ := (integrable_const 1).add hI
  have hp (x) : f x^q ≤ 1+f x^r:=rpow_le_one_add_pow (hf0 x) hq r hqr
  have hi : Integrable (fun x=>f x^q) μ := hdom.mono' (hf.pow_const q).aestronglyMeasurable
    (ae_of_all _ (fun x=>by rw [Real.norm_of_nonneg (Real.rpow_nonneg (hf0 x) q)];exact hp x))
  refine ⟨hi,(integral_mono hi hdom hp).trans_eq ?_⟩
  rw [integral_add (integrable_const 1) hI,integral_const,probReal_univ,one_smul]

end
end SlowEquilibration.NonnegativeRealMoment
