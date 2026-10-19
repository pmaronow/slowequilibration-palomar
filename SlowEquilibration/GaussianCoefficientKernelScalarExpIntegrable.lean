-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianCoefficientKernelScalarMGF

@[expose] public section

/-! Exponential integrability for every actual scalar linear observation
under every specified whole-coefficient Gaussian posterior. -/

namespace SlowEquilibration.GaussianCoefficientKernelScalarExpIntegrable
noncomputable section
open MeasureTheory ProbabilityTheory GaussianRegression WholeFieldRegression
open SphericalModel SphericalGaussianJet
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem coefficientKernel_scalar_exp_integrable
    {N P : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (A : EuclideanDisorder N P →L[ℝ] F)
    (B : EuclideanDisorder N P →L[ℝ] ℝ)
    (w : F) (β : ℝ) :
    Integrable (fun J => Real.exp (β * actualObservation B J))
      (coefficientKernel A w) := by
  let R := B.comp (residual A)
  let c := B (lift A w)
  have hG : HasGaussianLaw R (stdGaussian (EuclideanDisorder N P)) :=
    (IsGaussian.hasGaussianLaw_id
      (μ := stdGaussian (EuclideanDisorder N P))).map_fun R
  have hLaw : HasLaw (fun x => R x+c)
      (gaussianReal (∫ x, R x ∂stdGaussian (EuclideanDisorder N P) + c)
        (variance R (stdGaussian (EuclideanDisorder N P))).toNNReal)
      (stdGaussian (EuclideanDisorder N P)) :=
    gaussianReal_add_const
      (show HasLaw R (gaussianReal
        (∫ x, R x ∂stdGaussian (EuclideanDisorder N P))
        (variance R (stdGaussian (EuclideanDisorder N P))).toNNReal)
        (stdGaussian (EuclideanDisorder N P)) from
          ⟨hG.aemeasurable,hG.map_eq_gaussianReal⟩) c
  have hInt : Integrable (fun x => Real.exp (β*(R x+c)))
      (stdGaussian (EuclideanDisorder N P)) :=
    hLaw.integrable_comp (integrable_exp_mul_gaussianReal β)
  have hobs : Measurable (actualObservation B) :=
    B.continuous.measurable.comp
      ((PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
        (flatDisorder_measurable N P))
  have houter : Measurable (fun J => Real.exp (β*actualObservation B J)) :=
    (measurable_const.mul hobs).exp
  have hinner : Measurable (fun x => Real.exp
      (β*actualObservation B (unpackCLM N P x))) :=
    houter.comp (unpackCLM N P).continuous.measurable
  rw [coefficientKernel_apply,
    integrable_map_measure houter.aestronglyMeasurable
      (unpackCLM N P).continuous.measurable.aemeasurable,
    regressionKernel_apply]
  change Integrable (fun x => Real.exp
      (β*actualObservation B (unpackCLM N P x)))
    (Measure.map (fun x => residual A x+lift A w)
      (stdGaussian (EuclideanDisorder N P)))
  rw [integrable_map_measure hinner.aestronglyMeasurable (by fun_prop)]
  convert hInt using 1
  funext x
  change Real.exp (β*B (residual A x+lift A w)) = Real.exp (β*(R x+c))
  rw [map_add]
  rfl

end
end SlowEquilibration.GaussianCoefficientKernelScalarExpIntegrable
