-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorGradientFixedTimeTail

/-! The actual posterior grid tangent-cutoff error is the finite union of
true fixed-time Gaussian events, not an assumed grid tail. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps
open SphericalRotationCovariance
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

theorem mixedPosterior_finiteTime_original_gradient_tail {ι : Type*} [Fintype ι]
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1))
    (hu : ‖u‖^2=(n+1:ℕ)) (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (T : ℝ≥0)
    (times : ι→PathTime T) {α : ℝ} (hα : 0≤α) :
    (posteriorTrajectoryLaw n μ).real {q | ∃ i, α/2≤
      |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)
        (mixedPosteriorContinuousPath n μ Q u marks β T q (times i))/(n+1:ℕ)|} ≤
      (Fintype.card ι:ℝ)*2*Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q))) := by
  let A := fun i : ι=>{q | α/2≤
    |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)
      (mixedPosteriorContinuousPath n μ Q u marks β T q (times i))/(n+1:ℕ)|}
  have he : {q | ∃ i, α/2≤
      |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)
        (mixedPosteriorContinuousPath n μ Q u marks β T q (times i))/(n+1:ℕ)|}=⋃ i,A i := by
    ext q
    simp only [A,mem_ofPred_eq,mem_iUnion]
  rw [he]
  calc
    _ ≤ ∑ i,(posteriorTrajectoryLaw n μ).real (A i) := measureReal_iUnion_fintype_le A
    _ ≤ ∑ _i : ι,2*Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q))) :=
      Finset.sum_le_sum (fun i _=>mixedPosterior_fixedTime_original_gradient_tail n μ hQ u hu marks β T (times i) hα)
    _ = _ := by simp; ring

theorem valuePosterior_finiteTime_original_gradient_tail {ι : Type*} [Fintype ι]
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1))
    (hu : ‖u‖^2=(n+1:ℕ)) (mark : ℝ) (β : ℝ) (T : ℝ≥0)
    (times : ι→PathTime T) {α : ℝ} (hα : 0≤α) :
    (posteriorTrajectoryLaw n μ).real {q | ∃ i, α/2≤
      |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)
        (valuePosteriorContinuousPath n μ Q u mark β T q (times i))/(n+1:ℕ)|} ≤
      (Fintype.card ι:ℝ)*2*Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q))) := by
  let A := fun i : ι=>{q | α/2≤
    |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)
      (valuePosteriorContinuousPath n μ Q u mark β T q (times i))/(n+1:ℕ)|}
  have he : {q | ∃ i, α/2≤
      |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)
        (valuePosteriorContinuousPath n μ Q u mark β T q (times i))/(n+1:ℕ)|}=⋃ i,A i := by
    ext q
    simp only [A,mem_ofPred_eq,mem_iUnion]
  rw [he]
  calc
    _ ≤ ∑ i,(posteriorTrajectoryLaw n μ).real (A i) := measureReal_iUnion_fintype_le A
    _ ≤ ∑ _i : ι,2*Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q))) :=
      Finset.sum_le_sum (fun i _=>valuePosterior_fixedTime_original_gradient_tail n μ hQ u hu mark β T (times i) hα)
    _ = _ := by simp; ring

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
