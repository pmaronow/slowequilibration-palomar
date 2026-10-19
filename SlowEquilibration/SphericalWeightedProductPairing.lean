-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalSobolevBoundedProductPointwise

/-! Literal bounded Fh completed-form energy expansion. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance.KilledOperator
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def sphericalWeightedGradientSquare (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (u F : sphericalSobolevGraph hN β H hH) : ℝ :=
  ∑ ij : Fin N × Fin N,∫ x,F.val.fst x*(u.val.snd ij x)^2 ∂gibbsLaw N β H

def sphericalWeightedGradientCross (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (u F : sphericalSobolevGraph hN β H hH) : ℝ :=
  ∑ ij : Fin N × Fin N,∫ x,u.val.fst x*F.val.snd ij x*u.val.snd ij x ∂gibbsLaw N β H

/-- The actual Leibniz gradient expands the completed form into the
literal weighted gradient square and cross term. -/
theorem sphericalCompletedDirichlet_product_pairing (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (u F v : sphericalSobolevGraph hN β H hH) (CU CF : ℝ≥0)
    (hU : ∀ᵐ x ∂gibbsLaw N β H,‖u.val.fst x‖ ≤ CU)
    (hF : ∀ᵐ x ∂gibbsLaw N β H,‖F.val.fst x‖ ≤ CF)
    (hG : ∀ ij : Fin N × Fin N,v.val.snd ij=ᵐ[gibbsLaw N β H]
      fun x => u.val.fst x*F.val.snd ij x+F.val.fst x*u.val.snd ij x) :
    sphericalCompletedDirichlet hN β H hH u v=
      sphericalWeightedGradientSquare hN β H hH u F+sphericalWeightedGradientCross hN β H hH u F := by
  change inner ℝ u.val.snd v.val.snd=_
  rw [PiLp.inner_apply]
  unfold sphericalWeightedGradientSquare sphericalWeightedGradientCross
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  have hiB : Integrable (fun x => F.val.fst x*(u.val.snd ij x)^2) (gibbsLaw N β H) := by
    apply (L2.integrable_inner (𝕜:=ℝ) (u.val.snd ij)
      (multiplication (gibbsLaw N β H) F.val.fst (Lp.aestronglyMeasurable F.val.fst) CF hF (u.val.snd ij))).congr
    filter_upwards [multiplication_ae (gibbsLaw N β H) F.val.fst (Lp.aestronglyMeasurable F.val.fst) CF hF (u.val.snd ij)] with x hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
    ring
  have hiC : Integrable (fun x => u.val.fst x*F.val.snd ij x*u.val.snd ij x) (gibbsLaw N β H) := by
    apply (L2.integrable_inner (𝕜:=ℝ) (u.val.snd ij)
      (multiplication (gibbsLaw N β H) u.val.fst (Lp.aestronglyMeasurable u.val.fst) CU hU (F.val.snd ij))).congr
    filter_upwards [multiplication_ae (gibbsLaw N β H) u.val.fst (Lp.aestronglyMeasurable u.val.fst) CU hU (F.val.snd ij)] with x hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
  rw [L2.inner_def,← integral_add hiB hiC]
  apply integral_congr_ae
  filter_upwards [hG ij] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
  ring

theorem sphericalWeightedGradientSquare_nonnegative (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (u F : sphericalSobolevGraph hN β H hH)
    (hF : ∀ᵐ x ∂gibbsLaw N β H,0 ≤ F.val.fst x) :
    0 ≤ sphericalWeightedGradientSquare hN β H hH u F := by
  apply Finset.sum_nonneg
  intro ij _
  exact integral_nonneg_of_ae (hF.mono (fun x hx => mul_nonneg hx (sq_nonneg _)))

end SlowEquilibration.SphericalForm
