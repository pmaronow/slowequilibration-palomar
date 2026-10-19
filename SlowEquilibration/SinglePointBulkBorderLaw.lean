-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SinglePointBorderRegression
public import SlowEquilibration.SphericalPosteriorCommonMarginal

/-! Actual single-point common bulk GOE law and independence from its
whole border row/corner under original mixed or proper-value tensor
posterior conditioning, at every target. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance GaussianObservationCoercivity SphericalConditionalMatrices
open NormalizedPairObservations CanonicalGOERealization GOEAsymptotics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

/-- Genuine common-bulk physical GOE marginal under an actual own-point
mixed tensor observer, with every observation target retained. -/
theorem single_common_matrix_mixed_hasLaw {N P m ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htan : ∀ i,inner ℝ (e i) x=0) (f : Fin ℓ → Vector N) (w : MixedObservationSpace ℓ) :
    HasLaw (hessianMatrix c x e) (goeLaw m N (secondCovariance c 1))
      (coefficientKernel (singleMixedObservation c x f) w) := by
  have hCross:=common_flat_hessian_mixed_cross_zero hN c hc hdeg x x e htan f
  have hFlat:=unaffected_actualObservation_hasLaw _ _ hCross w
  rw [flatHessianCLM_law hN c hc x hx e he htan] at hFlat
  have hPush:=(hasLaw_map (unflattenMatrix_measurable m).aemeasurable).fun_comp hFlat
  rw [Measure.map_map (unflattenMatrix_measurable m) (flatMatrix_measurable m)] at hPush
  have hEq : unflattenMatrix m ∘ flatMatrix m=id:=funext (unflattenMatrix_flatMatrix m)
  rw [hEq,Measure.map_id] at hPush
  apply hPush.congr
  exact ae_of_all _ (fun J=>(unflattenMatrix_actual_hessian c x e J).symm)

/-- The actual physical common bulk is independent of its entire true
border row and corner under the original mixed single-point posterior. -/
theorem single_common_bulk_border_mixed_independent {N P m ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (e : Fin m → Vector N) (htan : ∀ i,inner ℝ (e i) x=0)
    (hve : ∀ i,inner ℝ (e i) v=0) (f : Fin ℓ → Vector N) (w : MixedObservationSpace ℓ)
    (hA : Surjective (singleMixedObservation c x f)) :
    IndepFun (hessianMatrix c x e) (actualObservation (borderCLM c x e v))
      (coefficientKernel (singleMixedObservation c x f) w) := by
  have hBA:=common_flat_hessian_mixed_cross_zero hN c hc hdeg x x e htan f
  have hBC:=common_bulk_border_cross_zero hN c hc x x v e htan hve
  have hFlat:=coefficientKernel_independent_of_cross_zero (singleMixedObservation c x f) hA
    (flatHessianCLM c x e) (borderCLM c x e v) hBA hBC w
  have hPush:=hFlat.comp (unflattenMatrix_measurable m) measurable_id
  simpa only [Function.comp_def,unflattenMatrix_actual_hessian,id_eq] using hPush

/-- Genuine common-bulk physical GOE marginal under an actual own-point
proper value-only tensor observer, with every observation target retained. -/
theorem single_common_matrix_value_hasLaw {N P m ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htan : ∀ i,inner ℝ (e i) x=0) (f : Fin ℓ → Vector N) (w : ValueObservationSpace ℓ) :
    HasLaw (hessianMatrix c x e) (goeLaw m N (secondCovariance c 1))
      (coefficientKernel (singleValueObservation c x f) w) := by
  have hCross:=common_flat_hessian_value_cross_zero hN c hc hdeg x x e htan f
  have hFlat:=unaffected_actualObservation_hasLaw _ _ hCross w
  rw [flatHessianCLM_law hN c hc x hx e he htan] at hFlat
  have hPush:=(hasLaw_map (unflattenMatrix_measurable m).aemeasurable).fun_comp hFlat
  rw [Measure.map_map (unflattenMatrix_measurable m) (flatMatrix_measurable m)] at hPush
  have hEq : unflattenMatrix m ∘ flatMatrix m=id:=funext (unflattenMatrix_flatMatrix m)
  rw [hEq,Measure.map_id] at hPush
  apply hPush.congr
  exact ae_of_all _ (fun J=>(unflattenMatrix_actual_hessian c x e J).symm)

/-- The actual physical common bulk is independent of its entire true
border row and corner under the original proper value-only single-point posterior. -/
theorem single_common_bulk_border_value_independent {N P m ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (e : Fin m → Vector N) (htan : ∀ i,inner ℝ (e i) x=0)
    (hve : ∀ i,inner ℝ (e i) v=0) (f : Fin ℓ → Vector N) (w : ValueObservationSpace ℓ)
    (hA : Surjective (singleValueObservation c x f)) :
    IndepFun (hessianMatrix c x e) (actualObservation (borderCLM c x e v))
      (coefficientKernel (singleValueObservation c x f) w) := by
  have hBA:=common_flat_hessian_value_cross_zero hN c hc hdeg x x e htan f
  have hBC:=common_bulk_border_cross_zero hN c hc x x v e htan hve
  have hFlat:=coefficientKernel_independent_of_cross_zero (singleValueObservation c x f) hA
    (flatHessianCLM c x e) (borderCLM c x e v) hBA hBC w
  have hPush:=hFlat.comp (unflattenMatrix_measurable m) measurable_id
  simpa only [Function.comp_def,unflattenMatrix_actual_hessian,id_eq] using hPush

end
end SlowEquilibration.SphericalCommonHessianRegression
