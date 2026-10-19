-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.BoundedQuadraticConvergence

/-! True quadratic expectation stability under a bounded pointwise
perturbation, on an arbitrary probability space. -/
@[expose] public section
namespace SlowEquilibration.BoundedQuadraticConvergence
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma integral_square_perturbation_bound {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (F G : E → ℝ)
    (hF : Integrable (fun x=>F x^2) μ) (hG : Integrable (fun x=>G x^2) μ)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ x,|F x-G x| ≤ K) :
    (∫ x,F x^2 ∂μ) ≤ 2*(∫ x,G x^2 ∂μ)+2*K^2 := by
  have hpoint (x:E) : F x^2 ≤ 2*G x^2+2*K^2 := by
    have hs : (F x-G x)^2 ≤ K^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (hbound x)
    nlinarith [sq_nonneg (F x-2*G x)]
  have hh:=integral_mono_ae hF ((hG.const_mul 2).add (integrable_const (2*K^2))) (ae_of_all _ hpoint)
  change (∫ x,F x^2 ∂μ) ≤ ∫ x,2*G x^2+2*K^2 ∂μ at hh
  rw [integral_add (hG.const_mul 2) (integrable_const _),integral_const_mul,
    integral_const,probReal_univ,one_smul] at hh
  exact hh

end
end SlowEquilibration.BoundedQuadraticConvergence
