-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorCommonMarginal

/-! Actual second-point common Hessian marginal GOE laws under every
specified mixed/proper-value full original coefficient posterior target. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity SphericalConditionalMatrices
open NormalizedPairObservations CanonicalGOERealization GOEAsymptotics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

/-- Genuine common Hessian GOE marginal under mixed conditioning at any
specified target. Its true law is derived from actual tensor covariance. -/
theorem posterior_common_matrix_right_mixed_hasLaw {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector N) (hy : ‖y‖^2=(N:ℝ)) (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (f g : Fin k → Vector N) (w : WithLp 2 (MixedObservationSpace k×MixedObservationSpace k)) :
    HasLaw (hessianMatrix c y e) (goeLaw m N (secondCovariance c 1))
      (coefficientKernel (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)) w) := by
  have hCross:=(single_pair_cross_zero (flatHessianCLM c y e)
    (singleMixedObservation c x f) (singleMixedObservation c y g)
    (common_flat_hessian_mixed_cross_zero hN c hc hdeg y x e htanx f)
    (common_flat_hessian_mixed_cross_zero hN c hc hdeg y y e htany g))
  have hFlat:=unaffected_actualObservation_hasLaw _ _ hCross w
  rw [flatHessianCLM_law hN c hc y hy e he htany] at hFlat
  have hPush:=(hasLaw_map (unflattenMatrix_measurable m).aemeasurable).fun_comp hFlat
  rw [Measure.map_map (unflattenMatrix_measurable m) (flatMatrix_measurable m)] at hPush
  have hEq : unflattenMatrix m ∘ flatMatrix m=id:=funext (unflattenMatrix_flatMatrix m)
  rw [hEq,Measure.map_id] at hPush
  apply hPush.congr
  exact ae_of_all _ (fun J=>(unflattenMatrix_actual_hessian c y e J).symm)

/-- Genuine common Hessian GOE marginal under value conditioning at any
specified target. Its true law is derived from actual tensor covariance. -/
theorem posterior_common_matrix_right_value_hasLaw {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector N) (hy : ‖y‖^2=(N:ℝ)) (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (f g : Fin k → Vector N) (w : WithLp 2 (ValueObservationSpace k×ValueObservationSpace k)) :
    HasLaw (hessianMatrix c y e) (goeLaw m N (secondCovariance c 1))
      (coefficientKernel (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)) w) := by
  have hCross:=(single_pair_cross_zero (flatHessianCLM c y e)
    (singleValueObservation c x f) (singleValueObservation c y g)
    (common_flat_hessian_value_cross_zero hN c hc hdeg y x e htanx f)
    (common_flat_hessian_value_cross_zero hN c hc hdeg y y e htany g))
  have hFlat:=unaffected_actualObservation_hasLaw _ _ hCross w
  rw [flatHessianCLM_law hN c hc y hy e he htany] at hFlat
  have hPush:=(hasLaw_map (unflattenMatrix_measurable m).aemeasurable).fun_comp hFlat
  rw [Measure.map_map (unflattenMatrix_measurable m) (flatMatrix_measurable m)] at hPush
  have hEq : unflattenMatrix m ∘ flatMatrix m=id:=funext (unflattenMatrix_flatMatrix m)
  rw [hEq,Measure.map_id] at hPush
  apply hPush.congr
  exact ae_of_all _ (fun J=>(unflattenMatrix_actual_hessian c y e J).symm)

end
end SlowEquilibration.SphericalCommonHessianRegression
