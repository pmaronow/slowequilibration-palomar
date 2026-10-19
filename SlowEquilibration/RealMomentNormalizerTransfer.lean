-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NonnegativeRealMoment

/-! Ordinary real-moment transfer between positive deterministic physical
normalizers, retaining original-space integrability and an explicit ratio. -/
@[expose] public section
namespace SlowEquilibration.NonnegativeRealMoment
noncomputable section
open MeasureTheory ProbabilityTheory

/-- A lower comparison of physical means transfers an already proved
ordinary q moment; no independence or replacement law is used. -/
theorem real_moment_normalizer_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ x,0 ≤ f x)
    {a b L q K : ℝ} (ha : 0 < a) (hb : 0 < b) (hL : 0 ≤ L) (hq : 0 ≤ q)
    (hratio : a/b ≤ L) (hI : Integrable (fun x=>(f x/a)^q) μ)
    (hMoment : (∫ x,(f x/a)^q ∂μ) ≤ K) :
    Integrable (fun x=>(f x/b)^q) μ ∧
      (∫ x,(f x/b)^q ∂μ) ≤ L^q*K := by
  have hp (x) : (f x/b)^q ≤ L^q*(f x/a)^q := by
    have hEq : f x/b=(a/b)*(f x/a) := by field_simp
    rw [hEq,Real.mul_rpow (div_nonneg ha.le hb.le) (div_nonneg (hf0 x) ha.le)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (div_nonneg ha.le hb.le) hratio hq)
      (Real.rpow_nonneg (div_nonneg (hf0 x) ha.le) q)
  have hdom:=hI.const_mul (L^q)
  have hi : Integrable (fun x=>(f x/b)^q) μ :=
    hdom.mono' ((hf.div_const b).pow_const q).aestronglyMeasurable
      (ae_of_all _ (fun x=>by rw [Real.norm_of_nonneg (Real.rpow_nonneg (div_nonneg (hf0 x) hb.le) q)];exact hp x))
  refine ⟨hi,(integral_mono hi hdom hp).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hMoment (Real.rpow_nonneg hL q)

end
end SlowEquilibration.NonnegativeRealMoment
