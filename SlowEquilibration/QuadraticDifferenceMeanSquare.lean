-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.QuadraticPerturbation

/-! Genuine ordinary L² difference decomposition with integrability. -/
@[expose] public section
namespace SlowEquilibration.BoundedQuadraticConvergence
noncomputable section
open Function MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma integral_square_difference_bound {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (F G : E → ℝ) (hF : Measurable F)
    (hG : Integrable (fun x=>G x^2) μ) (hD : Integrable (fun x=>(F x-G x)^2) μ) :
    Integrable (fun x=>F x^2) μ ∧
      (∫ x,F x^2 ∂μ) ≤ 2*(∫ x,G x^2 ∂μ)+2*(∫ x,(F x-G x)^2 ∂μ) := by
  let R:=fun x=>2*G x^2+2*(F x-G x)^2
  have hR : Integrable R μ:=(hG.const_mul 2).add (hD.const_mul 2)
  have hp (x:E) : F x^2 ≤ R x := by dsimp only [R];nlinarith [sq_nonneg (F x-2*G x)]
  have hFI : Integrable (fun x=>F x^2) μ:=hR.mono' (hF.pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun x=>by rw [Real.norm_of_nonneg (sq_nonneg _)];exact hp x))
  refine ⟨hFI,?_⟩
  have hh:=integral_mono_ae hFI hR (ae_of_all _ hp)
  have heq : (∫ x,R x ∂μ)=(∫ x,2*G x^2 ∂μ)+(∫ x,2*(F x-G x)^2 ∂μ) := by
    convert integral_add (hG.const_mul 2) (hD.const_mul 2) using 1
  rw [heq,integral_const_mul,integral_const_mul] at hh
  exact hh

end
end SlowEquilibration.BoundedQuadraticConvergence

