-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCommonHessianGOELaw

/-! Actual canonical correlated common-complement GOE laws under full
mixed and proper value-only tensor posteriors, at every observation target. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity GaussianRegressionCovariance NormalizedPairObservations
open SphericalConditionalMatrices SphericalHessianTraceCovariance SphericalTwoPointCovariance CanonicalGOERealization GOEAsymptotics
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

lemma common_flat_hessian_mixed_cross_zero {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector N) (e : Fin m → Vector N) (htany : ∀ i,inner ℝ (e i) y=0)
    (f : Fin k → Vector N) :
    (flatHessianCLM c x e).comp (singleMixedObservation c y f).adjoint=0 := by
  rw [flatHessianCLM,ContinuousLinearMap.comp_assoc,
    common_hessian_mixed_cross_zero hN c hc hdeg x y e htany f]
  simp

lemma common_flat_hessian_value_cross_zero {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector N) (e : Fin m → Vector N) (htany : ∀ i,inner ℝ (e i) y=0)
    (f : Fin k → Vector N) :
    (flatHessianCLM c x e).comp (singleValueObservation c y f).adjoint=0 := by
  rw [flatHessianCLM,ContinuousLinearMap.comp_assoc,
    common_hessian_value_cross_zero hN c hc hdeg x y e htany f]
  simp

/-- Full actual mixed posterior identification, derived from the tensor jet
covariance and the true canonical GOE realization, for every specified target. -/
theorem posterior_common_GOE_mixed_hasLaw {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hb : 0 < secondCovariance c 1) (hr : |overlap x y| ≤ 1)
    (f g : Fin k → Vector N) (w : WithLp 2 (MixedObservationSpace k×MixedObservationSpace k))
    (_hA : Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))) :
    HasLaw (actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)))
      ((stdGaussian (WithLp 2 (EuclideanSpace ℝ (CoefficientIndex m)×EuclideanSpace ℝ (CoefficientIndex m)))).map
        (correlatedPair (flatGOERealization m N (secondCovariance c 1))
          (hessianCorrelation c (overlap x y)) (hessianIndependentScale c (overlap x y))))
      (coefficientKernel (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)) w) := by
  have h:=unaffected_actualObservation_hasLaw
    (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))
    (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e))
    (paired_observations_cross_zero _ _ _ _
      (common_flat_hessian_mixed_cross_zero hN c hc hdeg x x e htanx f)
      (common_flat_hessian_mixed_cross_zero hN c hc hdeg x y e htany g)
      (common_flat_hessian_mixed_cross_zero hN c hc hdeg y x e htanx f)
      (common_flat_hessian_mixed_cross_zero hN c hc hdeg y y e htany g)) w
  rw [common_flat_hessian_pair_GOE_law hN c hc x y hx hy e he htanx htany hb hr] at h
  exact h

/-- Proper value-only posterior identification; no redundant radial
coordinate is added in a pure model. -/
theorem posterior_common_GOE_value_hasLaw {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hb : 0 < secondCovariance c 1) (hr : |overlap x y| ≤ 1)
    (f g : Fin k → Vector N) (w : WithLp 2 (ValueObservationSpace k×ValueObservationSpace k))
    (_hA : Surjective (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g))) :
    HasLaw (actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)))
      ((stdGaussian (WithLp 2 (EuclideanSpace ℝ (CoefficientIndex m)×EuclideanSpace ℝ (CoefficientIndex m)))).map
        (correlatedPair (flatGOERealization m N (secondCovariance c 1))
          (hessianCorrelation c (overlap x y)) (hessianIndependentScale c (overlap x y))))
      (coefficientKernel (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)) w) := by
  have h:=unaffected_actualObservation_hasLaw
    (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g))
    (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e))
    (paired_observations_cross_zero _ _ _ _
      (common_flat_hessian_value_cross_zero hN c hc hdeg x x e htanx f)
      (common_flat_hessian_value_cross_zero hN c hc hdeg x y e htany g)
      (common_flat_hessian_value_cross_zero hN c hc hdeg y x e htanx f)
      (common_flat_hessian_value_cross_zero hN c hc hdeg y y e htany g)) w
  rw [common_flat_hessian_pair_GOE_law hN c hc x y hx hy e he htanx htany hb hr] at h
  exact h

end
end SlowEquilibration.SphericalCommonHessianRegression
