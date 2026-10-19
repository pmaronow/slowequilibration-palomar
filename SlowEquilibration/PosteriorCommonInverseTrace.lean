-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorCommonMarginal
public import SlowEquilibration.GOEPhysicalCovarianceTraceIntegrability

/-! Actual original-posterior inverse trace error equals the genuine
physical GOE inverse trace error, at every target and real shift. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity SphericalConditionalMatrices
open NormalizedPairObservations GOEClippedResolvent GOEAsymptotics GOEScaling
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

/-- Exact actual mixed posterior trace-error integral, with original
coefficients and physical variance b/N. This is an identity of true laws. -/
theorem posterior_covariance_trace_error_mixed {n P ℓ : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (e : Fin (n+1) → Vector (n+3))
    (he : Orthonormal ℝ e) (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (f g : Fin ℓ → Vector (n+3)) (w : WithLp 2 (MixedObservationSpace ℓ×MixedObservationSpace ℓ))
    (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
    let b:=secondCovariance c 1
    let κ:=scaleFactor n (n+3) b*ρ
    let F:=fun J=>((b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1)))
      (clippedInverseOperator k κ (hessianMatrix c x e J)).toLinearMap-b*physicalResolvent b k)^2
    Integrable F (coefficientKernel A w) ∧
      (∫ J,F J ∂coefficientKernel A w)=
        (∫ W,(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2 ∂goeLaw (n+1) (n+3) b) := by
  dsimp only
  let b:=secondCovariance c 1
  let Φ:=fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2
  have hΦ : Measurable Φ:=((physicalCovarianceTrace_measurable n 2 b k ρ).sub_const _).pow_const 2
  have hΦI : Integrable Φ (goeLaw (n+1) (n+3) b):=
    physicalCovarianceTrace_square_integrable n 2 hb hρ k (b*physicalResolvent b k)
  have hLaw:=posterior_common_matrix_mixed_hasLaw (by omega : 0 < n+3) c hc hdeg x y hx e he htanx htany f g w
  have hEq (J:Disorder (n+3) P) : Φ (hessianMatrix c x e J)=
      ((b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1)))
        (clippedInverseOperator k (scaleFactor n (n+3) b*ρ) (hessianMatrix c x e J)).toLinearMap-b*physicalResolvent b k)^2 := by
    unfold Φ
    rw [physicalCovarianceTrace_eq_operator_trace n 2 hb.le k ρ]
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def,hEq] using hLaw.integrable_comp (f:=Φ) hΦI
  · have hh:=hLaw.integral_comp hΦ.aestronglyMeasurable
    simpa only [Function.comp_def,hEq] using hh

/-- Exact actual value posterior trace-error integral, with original
coefficients and physical variance b/N. This is an identity of true laws. -/
theorem posterior_covariance_trace_error_value {n P ℓ : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (e : Fin (n+1) → Vector (n+3))
    (he : Orthonormal ℝ e) (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (f g : Fin ℓ → Vector (n+3)) (w : WithLp 2 (ValueObservationSpace ℓ×ValueObservationSpace ℓ))
    (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
    let b:=secondCovariance c 1
    let κ:=scaleFactor n (n+3) b*ρ
    let F:=fun J=>((b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1)))
      (clippedInverseOperator k κ (hessianMatrix c x e J)).toLinearMap-b*physicalResolvent b k)^2
    Integrable F (coefficientKernel A w) ∧
      (∫ J,F J ∂coefficientKernel A w)=
        (∫ W,(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2 ∂goeLaw (n+1) (n+3) b) := by
  dsimp only
  let b:=secondCovariance c 1
  let Φ:=fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2
  have hΦ : Measurable Φ:=((physicalCovarianceTrace_measurable n 2 b k ρ).sub_const _).pow_const 2
  have hΦI : Integrable Φ (goeLaw (n+1) (n+3) b):=
    physicalCovarianceTrace_square_integrable n 2 hb hρ k (b*physicalResolvent b k)
  have hLaw:=posterior_common_matrix_value_hasLaw (by omega : 0 < n+3) c hc hdeg x y hx e he htanx htany f g w
  have hEq (J:Disorder (n+3) P) : Φ (hessianMatrix c x e J)=
      ((b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1)))
        (clippedInverseOperator k (scaleFactor n (n+3) b*ρ) (hessianMatrix c x e J)).toLinearMap-b*physicalResolvent b k)^2 := by
    unfold Φ
    rw [physicalCovarianceTrace_eq_operator_trace n 2 hb.le k ρ]
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def,hEq] using hLaw.integrable_comp (f:=Φ) hΦI
  · have hh:=hLaw.integral_comp hΦ.aestronglyMeasurable
    simpa only [Function.comp_def,hEq] using hh

end
end SlowEquilibration.SphericalCommonHessianRegression
