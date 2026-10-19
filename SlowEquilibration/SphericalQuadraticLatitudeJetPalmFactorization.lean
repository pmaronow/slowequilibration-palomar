-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPosteriorDeterminantBlock
public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-! Exact determinant/field factorization in the actual mixed Palm posterior.
The residual is independent of the joint `(Y₂,W)` block, while the
determinant and Y₂ remain correlated within that block. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression IntrinsicHessianLaw SphericalSequentialRegression
open ConditionedDeterminantMoments
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem mixed_palm_determinant_latitude_factorization
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (hnp : μ.minDegree < μ.maxDegree)
    {Q : ℝ} (hQ : 0 < Q) (a β : ℝ) (ha : 0 ≤ 1-a^2)
    (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0)
    (z : EuclideanSpace ℝ (Fin 2)) :
    (∫ J, intrinsicDet μ Q u J *
      Real.exp (β*field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω))
      ∂mixedLaw μ Q u hu z) =
      (∫ J, Real.exp (β*(field (mixtureCoefficients μ) J
          (originalLatitudePoint a u ω) -
        quadraticLatitudeJet μ a u ω J))
        ∂mixedLaw μ Q u hu z) *
      (∫ J, intrinsicDet μ Q u J *
        Real.exp (β*quadraticLatitudeJet μ a u ω J)
        ∂mixedLaw μ Q u hu z) := by
  let ν := mixedLaw μ Q u hu z
  let R := fun J : Disorder (n+2) μ.maxDegree =>
    field (mixtureCoefficients μ) J (originalLatitudePoint a u ω) -
      quadraticLatitudeJet μ a u ω J
  let C := flatQuadraticHessianBlock μ Q a u ω hu
  let X := actualObservation C
  let f := fun t : ℝ => Real.exp (β*t)
  let g := fun v : EuclideanSpace ℝ
      (Sum (Fin 1) (Fin (n+1) × Fin (n+1))) =>
    quadraticHessianBlockDet n (z 1) v *
      Real.exp (β*v (Sum.inl 0))
  have hR : Measurable R := by
    have hm : Measurable (actualObservation
        (flatNonquadraticLatitudeField μ a u ω)) :=
      (flatNonquadraticLatitudeField μ a u ω).continuous.measurable.comp
        ((PiLp.continuousLinearEquiv 2 ℝ
          (fun _ : Coordinate (n+2) μ.maxDegree => ℝ)).symm.continuous.measurable.comp
          (flatDisorder_measurable (n+2) μ.maxDegree))
    convert hm using 1
    funext J
    exact (flatNonquadraticLatitudeField_actual μ a u ω J).symm
  have hX : Measurable X :=
    C.continuous.measurable.comp
      ((PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Coordinate (n+2) μ.maxDegree => ℝ)).symm.continuous.measurable.comp
        (flatDisorder_measurable (n+2) μ.maxDegree))
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by
    have hy : Measurable (fun v : EuclideanSpace ℝ
        (Sum (Fin 1) (Fin (n+1) × Fin (n+1))) => v (Sum.inl 0)) :=
      (EuclideanSpace.proj (Sum.inl 0)).continuous.measurable
    exact (quadraticHessianBlockDet_measurable n (z 1)).mul
      ((measurable_const.mul hy).exp)
  have hI := nonquadraticLatitudeField_independent_quadraticHessian_physicalPalm
    μ hμ Q a hQ.le ha u ω hu hω z
  change IndepFun R X ν at hI
  have hfact := hI.integral_fun_comp_mul_comp
    hR.aemeasurable hX.aemeasurable
    hf.stronglyMeasurable.aestronglyMeasurable
    hg.stronglyMeasurable.aestronglyMeasurable
  have hY (J : Disorder (n+2) μ.maxDegree) :
      X J (Sum.inl 0)=quadraticLatitudeJet μ a u ω J := by
    simp [X,C,actualObservation]
  have hD := intrinsicDet_eq_quadraticHessianBlockDet_ae
    μ hQ hnp a u ω hu z
  have hF : (∫ J, intrinsicDet μ Q u J *
      Real.exp (β*field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω)) ∂ν) =
      ∫ J, f (R J)*g (X J) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hD] with J hJ
    dsimp [f,g,R]
    rw [hJ,hY]
    change quadraticHessianBlockDet n (z 1) (X J) *
        Real.exp (β*field (mixtureCoefficients μ) J
          (originalLatitudePoint a u ω)) =
      Real.exp (β*(field (mixtureCoefficients μ) J
          (originalLatitudePoint a u ω)-quadraticLatitudeJet μ a u ω J)) *
        (quadraticHessianBlockDet n (z 1) (X J) *
          Real.exp (β*quadraticLatitudeJet μ a u ω J))
    rw [show β*field (mixtureCoefficients μ) J
      (originalLatitudePoint a u ω) =
        β*(field (mixtureCoefficients μ) J
          (originalLatitudePoint a u ω)-quadraticLatitudeJet μ a u ω J) +
        β*quadraticLatitudeJet μ a u ω J by ring,Real.exp_add]
    ring
  have hG : (∫ J, g (X J) ∂ν) =
      ∫ J, intrinsicDet μ Q u J *
        Real.exp (β*quadraticLatitudeJet μ a u ω J) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hD] with J hJ
    dsimp [g]
    rw [hY,← hJ]
  calc
    _ = ∫ J, f (R J)*g (X J) ∂ν := hF
    _ = (∫ J, f (R J) ∂ν)*(∫ J, g (X J) ∂ν) := hfact
    _ = _ := by rw [hG]

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
