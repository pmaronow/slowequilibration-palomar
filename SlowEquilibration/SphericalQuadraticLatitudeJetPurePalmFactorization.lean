-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPureDeterminantBlock
public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-! Exact determinant/field factorization in the proper-pure Palm
posterior. The determinant and Y₂ belong to one correlated block, while
the nonquadratic remainder is independent of that entire block. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression IntrinsicHessianLaw SphericalSequentialRegression
open ConditionedDeterminantMoments SphericalMarkedWindows
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem pure_palm_determinant_latitude_factorization
    {n : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (hμ : 3 ≤ (FiniteMixture.pure p hp alpha halpha).minDegree)
    {Q : ℝ} (hQ : 0 < Q) (a β : ℝ) (ha : 0 ≤ 1-a^2)
    (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0) (e : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫ J, intrinsicDet μ Q u J *
      Real.exp (β*field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω))
      ∂valueConditionedLaw c u hu e) =
      (∫ J, Real.exp (β*(field (mixtureCoefficients μ) J
          (originalLatitudePoint a u ω) -
        quadraticLatitudeJet μ a u ω J))
        ∂valueConditionedLaw c u hu e) *
      (∫ J, intrinsicDet μ Q u J *
        Real.exp (β*quadraticLatitudeJet μ a u ω J)
        ∂valueConditionedLaw c u hu e) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let ν := valueConditionedLaw c u hu e
  let R := fun J : Disorder (n+2) μ.maxDegree =>
    field (mixtureCoefficients μ) J (originalLatitudePoint a u ω) -
      quadraticLatitudeJet μ a u ω J
  let C := flatQuadraticHessianBlock μ Q a u ω hu
  let X := actualObservation C
  let f := fun t : ℝ => Real.exp (β*t)
  let g := fun v : EuclideanSpace ℝ
      (Sum (Fin 1) (Fin (n+1) × Fin (n+1))) =>
    quadraticHessianBlockDet n ((p:ℝ)*e) v *
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
    exact (quadraticHessianBlockDet_measurable n ((p:ℝ)*e)).mul
      ((measurable_const.mul hy).exp)
  have hI := nonquadraticLatitudeField_independent_quadraticHessian_physicalPurePalm
    μ hμ Q a hQ.le ha u ω hu hω e
  change IndepFun R X ν at hI
  have hfact := hI.integral_fun_comp_mul_comp
    hR.aemeasurable hX.aemeasurable
    hf.stronglyMeasurable.aestronglyMeasurable
    hg.stronglyMeasurable.aestronglyMeasurable
  have hY (J : Disorder (n+2) μ.maxDegree) :
      X J (Sum.inl 0)=quadraticLatitudeJet μ a u ω J := by
    simp [X,C,actualObservation]
  have hD := intrinsicDet_eq_quadraticHessianBlockDet_pure_ae
    p hp alpha halpha hQ a u ω hu e
  have hF : (∫ J, intrinsicDet μ Q u J *
      Real.exp (β*field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω)) ∂ν) =
      ∫ J, f (R J)*g (X J) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hD] with J hJ
    dsimp [f,g,R]
    rw [hJ,hY]
    change quadraticHessianBlockDet n ((p:ℝ)*e) (X J) *
        Real.exp (β*field (mixtureCoefficients μ) J
          (originalLatitudePoint a u ω)) =
      Real.exp (β*(field (mixtureCoefficients μ) J
          (originalLatitudePoint a u ω)-quadraticLatitudeJet μ a u ω J)) *
        (quadraticHessianBlockDet n ((p:ℝ)*e) (X J) *
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
