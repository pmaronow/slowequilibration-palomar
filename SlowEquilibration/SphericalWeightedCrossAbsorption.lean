-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalWeightedProductPairing
public import SlowEquilibration.SphericalResolventFisher

/-! The literal completed-gradient cross term is absorbed by the actual
weighted energy and inverse-function Fisher integral. -/
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

private theorem scalar_cross_absorption (F u a b : ℝ) (hF : 1 ≤ F) (hu : |u| ≤ 1) :
    |u*b*a| ≤ (F*a^2+b^2*F⁻¹)/2 := by
  have hpos : 0<F := by linarith
  have hne : F≠0 := ne_of_gt hpos
  have he : F*((F*a^2+b^2*F⁻¹)/2)=((F*a)^2+b^2)/2 := by
    field_simp [hne]
  have hab : |b*a| ≤ (F*a^2+b^2*F⁻¹)/2 := by
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ hpos).mp
      rw [mul_neg,he]
      nlinarith [sq_nonneg (F*a+b)]
    · apply (mul_le_mul_iff_right₀ hpos).mp
      rw [he]
      nlinarith [sq_nonneg (F*a-b)]
  apply le_trans _ hab
  rw [mul_assoc,abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) hu

theorem sphericalFisher_coordinate_integrable (hN : 1≤N) (β : ℝ) (H : Vector N→ℝ)
    (hH : Continuous H) (F : sphericalSobolevGraph hN β H hH)
    (hF : ∀ᵐ x ∂gibbsLaw N β H,1≤F.val.fst x) (ij : Fin N×Fin N) :
    Integrable (fun x => (F.val.snd ij x)^2*(F.val.fst x)⁻¹) (gibbsLaw N β H) := by
  apply (L2.integrable_inner (𝕜:=ℝ) (F.val.snd ij)
    (multiplication (gibbsLaw N β H) (fun x => (F.val.fst x)⁻¹)
      ((measurable_inv.comp_aemeasurable (Lp.aestronglyMeasurable F.val.fst).aemeasurable).aestronglyMeasurable)
      1 (lp_inv_norm_le_one F.val.fst hF) (F.val.snd ij))).congr
  filter_upwards [multiplication_ae (gibbsLaw N β H) (fun x => (F.val.fst x)⁻¹)
    ((measurable_inv.comp_aemeasurable (Lp.aestronglyMeasurable F.val.fst).aemeasurable).aestronglyMeasurable)
    1 (lp_inv_norm_le_one F.val.fst hF) (F.val.snd ij)] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
  ring

/-- This controls the actual cross integral itself, without a supplied
cross-term or energy inequality. -/
theorem sphericalWeightedGradientCross_absorption (hN : 1≤N) (β : ℝ) (H : Vector N→ℝ)
    (hH : Continuous H) (u F : sphericalSobolevGraph hN β H hH) (CF : ℝ≥0)
    (hu : ∀ᵐ x ∂gibbsLaw N β H,‖u.val.fst x‖≤(1 : ℝ≥0))
    (hF : ∀ᵐ x ∂gibbsLaw N β H,‖F.val.fst x‖≤CF)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β H,1≤F.val.fst x) :
    |sphericalWeightedGradientCross hN β H hH u F| ≤
      (sphericalWeightedGradientSquare hN β H hH u F+sphericalFisher hN β H hH F)/2 := by
  unfold sphericalWeightedGradientCross sphericalWeightedGradientSquare sphericalFisher
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro ij _
  have hiB : Integrable (fun x => F.val.fst x*(u.val.snd ij x)^2) (gibbsLaw N β H) := by
    apply (L2.integrable_inner (𝕜:=ℝ) (u.val.snd ij)
      (multiplication (gibbsLaw N β H) F.val.fst (Lp.aestronglyMeasurable F.val.fst) CF hF (u.val.snd ij))).congr
    filter_upwards [multiplication_ae (gibbsLaw N β H) F.val.fst
      (Lp.aestronglyMeasurable F.val.fst) CF hF (u.val.snd ij)] with x hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
    ring
  have hiC : Integrable (fun x => u.val.fst x*F.val.snd ij x*u.val.snd ij x) (gibbsLaw N β H) := by
    apply (L2.integrable_inner (𝕜:=ℝ) (u.val.snd ij)
      (multiplication (gibbsLaw N β H) u.val.fst (Lp.aestronglyMeasurable u.val.fst) 1 hu (F.val.snd ij))).congr
    filter_upwards [multiplication_ae (gibbsLaw N β H) u.val.fst
      (Lp.aestronglyMeasurable u.val.fst) 1 hu (F.val.snd ij)] with x hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
  have hiJ := sphericalFisher_coordinate_integrable hN β H hH F hFlo ij
  apply abs_integral_le_integral_abs.trans
  rw [← integral_add hiB hiJ,← integral_div]
  apply integral_mono_ae hiC.abs ((hiB.add hiJ).div_const 2)
  filter_upwards [hu,hFlo] with x hux hFx
  exact scalar_cross_absorption _ _ _ _ hFx (by simpa only [Real.norm_eq_abs,NNReal.coe_one] using hux)

end SlowEquilibration.SphericalForm
