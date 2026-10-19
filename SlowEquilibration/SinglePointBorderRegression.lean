-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianActualCornerMeanSquare
public import SlowEquilibration.GaussianUnaffectedRegression

/-! Exact actual single-point border regression. Tangent rows and corners
annihilate the point's value/radial/gradient observer, so their full laws
remain unchanged at every original tensor posterior target. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance SphericalConditionalMatrices
open NormalizedPairObservations PairHessianMean
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

lemma single_corner_mixed_cross_zero {N P ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (hvtan : inner ℝ v x=0) (f : Fin ℓ → Vector N) :
    (cornerCLM c x v).comp (singleMixedObservation c x f).adjoint=0 := by
  apply ContinuousLinearMap.ext
  intro w
  change cornerCLM c x v ((singleMixedObservation c x f).adjoint w)=0
  exact own_mixed_hessian_zero hN c hc hdeg x v v hvtan hvtan f w

lemma single_common_row_mixed_cross_zero {N P m ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (htan : ∀ i,inner ℝ (e i) x=0) (f : Fin ℓ → Vector N) :
    (commonRowCLM c x e v).comp (singleMixedObservation c x f).adjoint=0 := by
  apply ContinuousLinearMap.ext
  intro w
  apply PiLp.ext
  intro i
  change commonRowCLM c x e v ((singleMixedObservation c x f).adjoint w) i=0
  rw [commonRowCLM_apply]
  exact own_mixed_hessian_zero hN c hc hdeg x (e i) v (htan i) hvtan f w

/-- Genuine original tensor-posterior corner law, unchanged by the point's
actual mixed observer at every specified target. -/
theorem single_corner_mixed_hasLaw {N P ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (hvtan : inner ℝ v x=0) (f : Fin ℓ → Vector N)
    (w : MixedObservationSpace ℓ) :
    HasLaw (actualObservation (cornerCLM c x v))
      ((stdGaussian (EuclideanDisorder N P)).map (cornerCLM c x v))
      (coefficientKernel (singleMixedObservation c x f) w) :=
  unaffected_actualObservation_hasLaw _ _ (single_corner_mixed_cross_zero hN c hc hdeg x v hvtan f) w

/-- The entire actual row law is unchanged, including every coefficient
and all specified mixed posterior targets. -/
theorem single_common_row_mixed_hasLaw {N P m ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (htan : ∀ i,inner ℝ (e i) x=0) (f : Fin ℓ → Vector N)
    (w : MixedObservationSpace ℓ) :
    HasLaw (actualObservation (commonRowCLM c x e v))
      ((stdGaussian (EuclideanDisorder N P)).map (commonRowCLM c x e v))
      (coefficientKernel (singleMixedObservation c x f) w) :=
  unaffected_actualObservation_hasLaw _ _ (single_common_row_mixed_cross_zero hN c hc hdeg x v hvtan e htan f) w

lemma single_corner_value_cross_zero {N P ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (hvtan : inner ℝ v x=0) (f : Fin ℓ → Vector N) :
    (cornerCLM c x v).comp (singleValueObservation c x f).adjoint=0 := by
  apply ContinuousLinearMap.ext
  intro w
  change cornerCLM c x v ((singleValueObservation c x f).adjoint w)=0
  exact own_value_hessian_zero hN c hc hdeg x v v hvtan hvtan f w

lemma single_common_row_value_cross_zero {N P m ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (htan : ∀ i,inner ℝ (e i) x=0) (f : Fin ℓ → Vector N) :
    (commonRowCLM c x e v).comp (singleValueObservation c x f).adjoint=0 := by
  apply ContinuousLinearMap.ext
  intro w
  apply PiLp.ext
  intro i
  change commonRowCLM c x e v ((singleValueObservation c x f).adjoint w) i=0
  rw [commonRowCLM_apply]
  exact own_value_hessian_zero hN c hc hdeg x (e i) v (htan i) hvtan f w

/-- Genuine original tensor-posterior corner law, unchanged by the point's
actual proper value-only observer at every specified target. -/
theorem single_corner_value_hasLaw {N P ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (hvtan : inner ℝ v x=0) (f : Fin ℓ → Vector N)
    (w : ValueObservationSpace ℓ) :
    HasLaw (actualObservation (cornerCLM c x v))
      ((stdGaussian (EuclideanDisorder N P)).map (cornerCLM c x v))
      (coefficientKernel (singleValueObservation c x f) w) :=
  unaffected_actualObservation_hasLaw _ _ (single_corner_value_cross_zero hN c hc hdeg x v hvtan f) w

/-- The entire actual row law is unchanged, including every coefficient
and all specified proper value-only posterior targets. -/
theorem single_common_row_value_hasLaw {N P m ℓ : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (htan : ∀ i,inner ℝ (e i) x=0) (f : Fin ℓ → Vector N)
    (w : ValueObservationSpace ℓ) :
    HasLaw (actualObservation (commonRowCLM c x e v))
      ((stdGaussian (EuclideanDisorder N P)).map (commonRowCLM c x e v))
      (coefficientKernel (singleValueObservation c x f) w) :=
  unaffected_actualObservation_hasLaw _ _ (single_common_row_value_cross_zero hN c hc hdeg x v hvtan e htan f) w

end
end SlowEquilibration.SphericalCommonHessianRegression
