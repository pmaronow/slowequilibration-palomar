-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalWeightedProductPairing

/-! The actual bounded square is in the completed graph, and its form
pairing is exactly twice the literal source gradient cross integral. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem sphericalSobolevGraph_square_cross_pairing (hN : 1≤N) (β : ℝ) (H : Vector N→ℝ)
    (hH : Continuous H) (u F : sphericalSobolevGraph hN β H hH) (CU : ℝ≥0)
    (hU : ∀ᵐ x ∂gibbsLaw N β H,‖u.val.fst x‖≤CU) :
    ∃ v : sphericalSobolevGraph hN β H hH,
      (v.val.fst=ᵐ[gibbsLaw N β H] fun x => (u.val.fst x)^2) ∧
      (∀ ij : Fin N×Fin N,v.val.snd ij=ᵐ[gibbsLaw N β H] fun x => 2*u.val.fst x*u.val.snd ij x) ∧
      sphericalCompletedDirichlet hN β H hH F v=2*sphericalWeightedGradientCross hN β H hH u F := by
  obtain ⟨v,hv,hgrad⟩ := sphericalSobolevGraph_bounded_product_ae hN β H hH u u CU CU hU hU
  have hvg : ∀ ij : Fin N×Fin N,v.val.snd ij=ᵐ[gibbsLaw N β H]
      fun x => 2*u.val.fst x*u.val.snd ij x := by
    intro ij
    exact (hgrad ij).mono (fun x hx => hx.trans (by ring))
  refine ⟨v,?_,hvg,?_⟩
  · exact hv.mono (fun x hx => hx.trans (by ring))
  · change inner ℝ F.val.snd v.val.snd=2*∑ ij : Fin N×Fin N,
      ∫ x,u.val.fst x*F.val.snd ij x*u.val.snd ij x ∂gibbsLaw N β H
    rw [PiLp.inner_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij _
    rw [L2.inner_def,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hvg ij] with x hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
    ring

end SlowEquilibration.SphericalForm
