-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetCenterHessianOrthogonality
public import SlowEquilibration.GaussianKernelOrthogonalBlocks
public import SlowEquilibration.ConditionedIntrinsicHessian

@[expose] public section

/-! Under the genuine mixed coefficient posterior, the nonquadratic part of
the original latitude field is independent of the joint quadratic bank and
scaled-center tangential Hessian. The latter two remain correlated. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression IntrinsicHessianLaw SphericalSequentialRegression
open ConditionedIntrinsicHessian ConditionedDeterminantMoments
open GaussianKernelOrthogonalBlocks
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1200000

def flatNonquadraticLatitudeField {N : ℕ} (μ : FiniteMixture)
    (a : ℝ) (u ω : Vector N) :
    EuclideanDisorder N μ.maxDegree →L[ℝ] ℝ :=
  flatJetCLM (mixtureCoefficients μ) 0
    (originalLatitudePoint a u ω) (fun i => Fin.elim0 i) -
    flatQuadraticLatitudeJet μ a u ω

@[simp] theorem flatNonquadraticLatitudeField_actual {N : ℕ}
    (μ : FiniteMixture) (a : ℝ) (u ω : Vector N)
    (J : Disorder N μ.maxDegree) :
    flatNonquadraticLatitudeField μ a u ω (euclideanDisorder J) =
      field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω) -
      quadraticLatitudeJet μ a u ω J := by
  simp only [flatNonquadraticLatitudeField,sub_apply,
    flatJetCLM_apply,flatQuadraticLatitudeJet_actual,jet,
    iteratedFDeriv_zero_apply,unpack_euclideanDisorder]

def flatQuadraticHessianBlock {n : ℕ} (μ : FiniteMixture)
    (Q a : ℝ) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ)) :
    EuclideanDisorder (n+2) μ.maxDegree →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin 1) (Fin (n+1) × Fin (n+1))) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Sum (Fin 1) (Fin (n+1) × Fin (n+1)) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim
      (fun _ : Fin 1 => flatQuadraticLatitudeJet μ a u ω)
      (fun ij => (EuclideanSpace.proj ij).comp
        (ambientHessianCLM (centerCoefficients (mixtureCoefficients μ) Q)
          u (tangentFrame u hu)))))

@[simp] theorem flatQuadraticHessianBlock_inl {n : ℕ}
    (μ : FiniteMixture) (Q a : ℝ) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (g : EuclideanDisorder (n+2) μ.maxDegree) (i : Fin 1) :
    flatQuadraticHessianBlock μ Q a u ω hu g (Sum.inl i) =
      flatQuadraticLatitudeJet μ a u ω g := by
  simp [flatQuadraticHessianBlock]

@[simp] theorem flatQuadraticHessianBlock_inr {n : ℕ}
    (μ : FiniteMixture) (Q a : ℝ) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (g : EuclideanDisorder (n+2) μ.maxDegree)
    (ij : Fin (n+1) × Fin (n+1)) :
    flatQuadraticHessianBlock μ Q a u ω hu g (Sum.inr ij) =
      ambientHessianCLM (centerCoefficients (mixtureCoefficients μ) Q)
        u (tangentFrame u hu) g ij := by
  simp [flatQuadraticHessianBlock]

theorem flatQuadraticHessianBlock_physicalJoint_cross_zero
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a : ℝ) (hQ : 0 ≤ Q) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0) :
    (flatQuadraticHessianBlock μ Q a u ω hu).comp
      (jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
        u (tangentFrame u hu)).adjoint=0 := by
  let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
    u (tangentFrame u hu)
  have hY := flatQuadraticLatitudeJet_physicalJoint_cross_zero
    (by omega : 0 < n+2) μ hμ Q a u ω hω (tangentFrame u hu)
  have hH := ambientHessian_joint_lift_zero
    (centerCoefficients (mixtureCoefficients μ) Q)
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ)
    u (tangentFrame u hu) (tangentFrame_tangent u hu)
  ext v j
  cases j with
  | inl i =>
      change flatQuadraticLatitudeJet μ a u ω (A.adjoint v)=0
      exact congrArg (fun D : _ => D v) hY
  | inr ij =>
      change ambientHessianCLM
        (centerCoefficients (mixtureCoefficients μ) Q)
        u (tangentFrame u hu) (A.adjoint v) ij=0
      exact congrArg (fun D : _ => D v ij) hH

theorem flatNonquadraticLatitudeField_quadraticHessian_cross_zero
    {n : ℕ} (μ : FiniteMixture) (Q a : ℝ)
    (ha : 0 ≤ 1-a^2) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0) :
    (flatNonquadraticLatitudeField μ a u ω).comp
      (flatQuadraticHessianBlock μ Q a u ω hu).adjoint=0 := by
  let B := flatNonquadraticLatitudeField μ a u ω
  let C := flatQuadraticHessianBlock μ Q a u ω hu
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun
    (Sum (Fin 1) (Fin (n+1) × Fin (n+1))) ℝ).toBasis.ext
  intro j
  have h := actual_scalar_cross_covariance B C
    (EuclideanSpace.basisFun
      (Sum (Fin 1) (Fin (n+1) × Fin (n+1))) ℝ j)
  simp only [EuclideanSpace.basisFun_inner] at h
  change cov[fun J : Disorder (n+2) μ.maxDegree =>
      B (euclideanDisorder J),
    fun J : Disorder (n+2) μ.maxDegree =>
      C (euclideanDisorder J) j;
    disorderLaw (n+2) μ.maxDegree] =
    B (C.adjoint (EuclideanSpace.basisFun
      (Sum (Fin 1) (Fin (n+1) × Fin (n+1))) ℝ j)) at h
  change B (C.adjoint (EuclideanSpace.basisFun
      (Sum (Fin 1) (Fin (n+1) × Fin (n+1))) ℝ j))=0
  rw [←h]
  simp only [B,flatNonquadraticLatitudeField_actual]
  cases j with
  | inl j =>
      fin_cases j
      simp only [C,flatQuadraticHessianBlock_inl,
        flatQuadraticLatitudeJet_actual]
      rw [covariance_comm]
      exact quadraticLatitudeJet_residualField_covariance_zero
        (by omega : 0 < n+2) μ a ha u ω ω hu hω hω
  | inr ij =>
      rcases ij with ⟨i,l⟩
      simp only [C,flatQuadraticHessianBlock_inr,
        ambientHessianCLM_apply,unpack_euclideanDisorder]
      change cov[fun J : Disorder (n+2) μ.maxDegree =>
          field (mixtureCoefficients μ) J (originalLatitudePoint a u ω) -
            quadraticLatitudeJet μ a u ω J,
        jet (centerCoefficients (mixtureCoefficients μ) Q) 2 u
          ![tangentFrame u hu i,tangentFrame u hu l];
        disorderLaw (n+2) μ.maxDegree]=0
      rw [covariance_comm]
      exact scaledCenterHessian_residualField_covariance_zero
        (by omega : 0 < n+2) μ Q a ha u
        (tangentFrame u hu i) (tangentFrame u hu l) ω hu
        (tangentFrame_tangent u hu i) (tangentFrame_tangent u hu l) hω

/-- Pointwise source posterior factorization at every normalized mixed mark:
the actual nonquadratic latitude field is independent of the *joint* true
quadratic bank and scaled-center Hessian matrix. No independence between Y₂
and W is asserted. -/
theorem nonquadraticLatitudeField_independent_quadraticHessian_physicalPalm
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a : ℝ) (hQ : 0 ≤ Q) (ha : 0 ≤ 1-a^2)
    (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0)
    (z : EuclideanSpace ℝ (Fin 2)) :
    IndepFun
      (fun J : Disorder (n+2) μ.maxDegree =>
        field (mixtureCoefficients μ) J (originalLatitudePoint a u ω) -
          quadraticLatitudeJet μ a u ω J)
      (actualObservation (flatQuadraticHessianBlock μ Q a u ω hu))
      (mixedLaw μ Q u hu z) := by
  let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
    u (tangentFrame u hu)
  let B := flatNonquadraticLatitudeField μ a u ω
  let C := flatQuadraticHessianBlock μ Q a u ω hu
  have h := coefficientKernel_orthogonal_blocks_independent A B C
    (flatQuadraticHessianBlock_physicalJoint_cross_zero
      μ hμ Q a hQ u ω hu hω)
    (flatNonquadraticLatitudeField_quadraticHessian_cross_zero
      μ Q a ha u ω hu hω)
    (jointScoreTarget (n+1) (((n+2:ℕ):ℝ) • z))
  change IndepFun (actualObservation B) (actualObservation C)
      (mixedLaw μ Q u hu z) at h
  have hEq : (actualObservation B : Disorder (n+2) μ.maxDegree → ℝ) =
      (fun J => field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω) - quadraticLatitudeJet μ a u ω J) := by
    funext J
    exact flatNonquadraticLatitudeField_actual μ a u ω J
  rw [hEq] at h
  exact h

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
