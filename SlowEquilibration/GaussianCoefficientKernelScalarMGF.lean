-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegressionCovariance
public import SlowEquilibration.WholeFieldRegression

@[expose] public section

/-! The exact exponential moment of a genuine scalar linear observation
under the canonical full-coefficient Gaussian conditioning kernel. -/

namespace SlowEquilibration.GaussianCoefficientKernelScalarMGF
noncomputable section
open MeasureTheory ProbabilityTheory GaussianRegression WholeFieldRegression
open SphericalModel SphericalGaussianJet
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem coefficientKernel_scalar_exp_integral
    {N P : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (A : EuclideanDisorder N P →L[ℝ] F)
    (B : EuclideanDisorder N P →L[ℝ] ℝ)
    (w : F) (β : ℝ) :
    (∫ J, Real.exp (β * actualObservation B J) ∂coefficientKernel A w) =
      Real.exp (β * B (lift A w) +
        β^2 * ‖B.comp (residual A)‖^2 / 2) := by
  let R := B.comp (residual A)
  let c := B (lift A w)
  have hG : HasGaussianLaw R (stdGaussian (EuclideanDisorder N P)) :=
    (IsGaussian.hasGaussianLaw_id
      (μ := stdGaussian (EuclideanDisorder N P))).map_fun R
  have hM : (∫ x, R x ∂stdGaussian (EuclideanDisorder N P)) = 0 := by
    rw [R.integral_comp_id_comm IsGaussian.integrable_id, integral_id_stdGaussian,
      map_zero]
  have hLaw : HasLaw (fun x => R x + c)
      (gaussianReal c (‖R‖^2).toNNReal)
      (stdGaussian (EuclideanDisorder N P)) := by
    have hBase : HasLaw R
        (gaussianReal 0 (‖R‖^2).toNNReal)
        (stdGaussian (EuclideanDisorder N P)) := by
      have h := (show HasLaw R (gaussianReal
        (∫ x, R x ∂stdGaussian (EuclideanDisorder N P))
        (variance R (stdGaussian (EuclideanDisorder N P))).toNNReal)
        (stdGaussian (EuclideanDisorder N P)) from
          ⟨hG.aemeasurable,hG.map_eq_gaussianReal⟩)
      rwa [hM,variance_dual_stdGaussian] at h
    simpa using gaussianReal_add_const hBase c
  have hExp : (∫ x, Real.exp (β*(R x+c))
      ∂stdGaussian (EuclideanDisorder N P)) =
      Real.exp (β*c+β^2*‖R‖^2/2) := by
    change mgf (fun x => R x+c)
      (stdGaussian (EuclideanDisorder N P)) β = _
    rw [mgf_gaussianReal hLaw]
    simp only [Real.coe_toNNReal _ (sq_nonneg _)]
    congr 1
    ring
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
  rw [coefficientKernel_apply,integral_map]
  · rw [regressionKernel_apply,integral_map]
    · convert hExp using 1
      · congr 1
        funext x
        change Real.exp (β*B (residual A x+lift A w)) =
          Real.exp (β*(R x+c))
        rw [map_add]
        rfl
    · fun_prop
    · exact hinner.aestronglyMeasurable
  · fun_prop
  · exact houter.aestronglyMeasurable

end
end SlowEquilibration.GaussianCoefficientKernelScalarMGF
