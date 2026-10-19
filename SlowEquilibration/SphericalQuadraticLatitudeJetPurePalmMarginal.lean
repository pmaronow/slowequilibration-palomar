-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPhysicalPalmMarginal
public import SlowEquilibration.SphericalPureMarkedWindows

@[expose] public section

/-! The genuine degree-two latitude bank keeps its finite-dimensional law
under every proper-pure scalar-value/tangent-gradient posterior target. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression IntrinsicHessianLaw SphericalSequentialRegression
open SphericalMarkedWindows
open ValueTangentConditioning
open ConditionedIntrinsicHessian
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem flatQuadraticLatitudeJet_physicalValueTangent_cross_zero
    {N m : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (hμ : 3 ≤ μ.minDegree) (Q a : ℝ) (u ω : Vector N)
    (hω : inner ℝ ω u=0) (e : Fin m → Vector N) :
    (flatQuadraticLatitudeJet μ a u ω).comp
      (valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u e).adjoint=0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Sum (Fin 1) (Fin m)) ℝ).toBasis.ext
  intro j
  have h := actual_scalar_cross_covariance (flatQuadraticLatitudeJet μ a u ω)
    (valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u e)
    (EuclideanSpace.basisFun (Sum (Fin 1) (Fin m)) ℝ j)
  simp only [EuclideanSpace.basisFun_inner] at h
  change cov[fun J : Disorder N μ.maxDegree =>
      flatQuadraticLatitudeJet μ a u ω (euclideanDisorder J),
      fun J : Disorder N μ.maxDegree =>
        valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u e
          (euclideanDisorder J) j; disorderLaw N μ.maxDegree] =
    flatQuadraticLatitudeJet μ a u ω
      ((valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u e).adjoint
        (EuclideanSpace.basisFun (Sum (Fin 1) (Fin m)) ℝ j)) at h
  simp only [flatQuadraticLatitudeJet_actual] at h
  change flatQuadraticLatitudeJet μ a u ω
    ((valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u e).adjoint
      (EuclideanSpace.basisFun (Sum (Fin 1) (Fin m)) ℝ j)) = 0
  rw [← h]
  cases j with
  | inl j =>
    simpa only [valueTangentCLM_apply_value, unpack_euclideanDisorder] using
      quadraticLatitudeJet_scaledCenter_value_covariance_zero hN μ Q a u ω hω
  | inr j =>
    simpa only [valueTangentCLM_apply_gradient, unpack_euclideanDisorder] using
      quadraticLatitudeJet_scaledCenter_gradient_covariance_zero
        hN μ hμ Q a u ω (e j) hω

/-- Every finite family of the literal Y₂ probes has its original joint
law under the exact proper-pure `valueConditionedLaw`, for every value
target, including probability-zero conditioning targets. -/
theorem quadraticLatitudeJetFamily_physicalPurePalm_marginal
    {n k : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a : ℝ) (u : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (ω : Fin k → Vector (n+2)) (hω : ∀ i, inner ℝ (ω i) u=0)
    (b : ℝ) :
    (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).map
      (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) =
      (disorderLaw (n+2) μ.maxDegree).map
        (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) := by
  let A := valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u
    (tangentFrame u hu)
  let B := flatQuadraticLatitudeJetFamily μ a u ω
  have hBA : B.comp A.adjoint=0 := by
    ext v i
    change flatQuadraticLatitudeJet μ a u (ω i) (A.adjoint v)=0
    have hi := flatQuadraticLatitudeJet_physicalValueTangent_cross_zero
      (by omega : 0 < n+2) μ hμ Q a u (ω i) (hω i) (tangentFrame u hu)
    exact congrArg (fun C : EuclideanSpace ℝ (Sum (Fin 1) (Fin (n+1))) →L[ℝ] ℝ => C v) hi
  have h := coefficientKernel_target_map_linear A B hBA
    (jointValueTarget (n+1) (((n+2:ℕ):ℝ)*b))
  change (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).map
      (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) =
    (disorderLaw (n+2) μ.maxDegree).map
      (fun J => flatQuadraticLatitudeJetFamily μ a u ω (euclideanDisorder J)) at h
  exact h

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
