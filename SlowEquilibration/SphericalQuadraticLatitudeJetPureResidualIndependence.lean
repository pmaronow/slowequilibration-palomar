-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPosteriorResidualIndependence
public import SlowEquilibration.SphericalQuadraticLatitudeJetPurePalmMarginal

@[expose] public section

/-! Under the literal proper-pure value/tangent posterior, the
nonquadratic latitude field is independent of the joint quadratic bank
and center Hessian. The quadratic bank and Hessian remain correlated. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression IntrinsicHessianLaw SphericalSequentialRegression
open ConditionedIntrinsicHessian ConditionedDeterminantMoments
open GaussianKernelOrthogonalBlocks ValueTangentConditioning
open SphericalMarkedWindows
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem flatQuadraticHessianBlock_physicalValueTangent_cross_zero
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a : ℝ) (hQ : 0 ≤ Q) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0) :
    (flatQuadraticHessianBlock μ Q a u ω hu).comp
      (valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q)
        u (tangentFrame u hu)).adjoint=0 := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let C := flatQuadraticHessianBlock μ Q a u ω hu
  let A := jointCLM c u (tangentFrame u hu)
  have hCA : C.comp A.adjoint=0 :=
    flatQuadraticHessianBlock_physicalJoint_cross_zero μ hμ Q a hQ u ω hu hω
  change C.comp ((forgetRadial (n+1)).comp A).adjoint=0
  rw [ContinuousLinearMap.adjoint_comp]
  rw [← ContinuousLinearMap.comp_assoc, hCA]
  simp

theorem nonquadraticLatitudeField_independent_quadraticHessian_physicalPurePalm
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a : ℝ) (hQ : 0 ≤ Q) (ha : 0 ≤ 1-a^2)
    (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0) (b : ℝ) :
    IndepFun
      (fun J : Disorder (n+2) μ.maxDegree =>
        field (mixtureCoefficients μ) J (originalLatitudePoint a u ω) -
          quadraticLatitudeJet μ a u ω J)
      (actualObservation (flatQuadraticHessianBlock μ Q a u ω hu))
      (valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
  let A := valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q)
    u (tangentFrame u hu)
  let B := flatNonquadraticLatitudeField μ a u ω
  let C := flatQuadraticHessianBlock μ Q a u ω hu
  have h := coefficientKernel_orthogonal_blocks_independent A B C
    (flatQuadraticHessianBlock_physicalValueTangent_cross_zero
      μ hμ Q a hQ u ω hu hω)
    (flatNonquadraticLatitudeField_quadraticHessian_cross_zero
      μ Q a ha u ω hu hω)
    (jointValueTarget (n+1) (((n+2:ℕ):ℝ)*b))
  change IndepFun (actualObservation B) (actualObservation C)
      (valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu b) at h
  have hEq : (actualObservation B : Disorder (n+2) μ.maxDegree → ℝ) =
      (fun J => field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω) - quadraticLatitudeJet μ a u ω J) := by
    funext J
    exact flatNonquadraticLatitudeField_actual μ a u ω J
  rw [hEq] at h
  exact h

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
