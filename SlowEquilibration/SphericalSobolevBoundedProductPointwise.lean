-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalSobolevBoundedProduct

/-! Literal almost-everywhere products and gradients in the actual completed
spherical Sobolev graph, derived from the proved product calculus. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance.KilledOperator
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem sphericalSobolevGraph_bounded_product_ae {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (u v : sphericalSobolevGraph hN β H hH) (CU CV : ℝ≥0)
    (hU : ∀ᵐ x ∂gibbsLaw N β H,‖u.val.fst x‖ ≤ CU)
    (hV : ∀ᵐ x ∂gibbsLaw N β H,‖v.val.fst x‖ ≤ CV) :
    ∃ w : sphericalSobolevGraph hN β H hH,
      (w.val.fst=ᵐ[gibbsLaw N β H] fun x => u.val.fst x*v.val.fst x) ∧
      ∀ ij : Fin N × Fin N,w.val.snd ij=ᵐ[gibbsLaw N β H]
        fun x => v.val.fst x*u.val.snd ij x+u.val.fst x*v.val.snd ij x := by
  obtain ⟨w,hw,hG⟩ := sphericalSobolevGraph_bounded_product hN β H hH u v CU CV hU hV
  refine ⟨w,?_,?_⟩
  · rw [hw]
    exact multiplication_ae _ _ _ _ _ _
  · intro ij
    rw [hG]
    filter_upwards [multiplication_ae (gibbsLaw N β H) v.val.fst (Lp.aestronglyMeasurable v.val.fst) CV hV (u.val.snd ij),
      multiplication_ae (gibbsLaw N β H) u.val.fst (Lp.aestronglyMeasurable u.val.fst) CU hU (v.val.snd ij),
      Lp.coeFn_add
        (multiplication (gibbsLaw N β H) v.val.fst (Lp.aestronglyMeasurable v.val.fst) CV hV (u.val.snd ij))
        (multiplication (gibbsLaw N β H) u.val.fst (Lp.aestronglyMeasurable u.val.fst) CU hU (v.val.snd ij))]
        with x h₁ h₂ hadd
    change (multiplication (gibbsLaw N β H) v.val.fst (Lp.aestronglyMeasurable v.val.fst) CV hV (u.val.snd ij)+
      multiplication (gibbsLaw N β H) u.val.fst (Lp.aestronglyMeasurable u.val.fst) CU hU (v.val.snd ij)) x=_
    simp only [hadd,Pi.add_apply,h₁,h₂]

end SlowEquilibration.SphericalForm
