-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegressionCovariance
public import SlowEquilibration.SphericalConditionalMatrices

/-! True Gaussian observations orthogonal to the conditioning map retain
exactly their full joint law under every specified posterior target. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegressionCovariance
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianRegression
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] in
lemma lift_map_eq_zero_of_cross_zero (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hcross : B.comp A.adjoint=0) (w : F) : B (lift A w)=0 := by
  have h:=congrArg (fun T : F →L[ℝ] G => T ((gram A).inverse w)) hcross
  exact h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] in
lemma residual_map_eq_of_cross_zero (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hcross : B.comp A.adjoint=0) : B.comp (residual A)=B := by
  ext z
  change B (z-lift A (A z))=B z
  rw [map_sub,lift_map_eq_zero_of_cross_zero A B hcross,sub_zero]

omit [FiniteDimensional ℝ G] in
/-- Complete unchanged joint law, rather than entrywise covariance alone. -/
theorem conditionalLaw_eq_original_of_cross_zero (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hcross : B.comp A.adjoint=0) (w : F) : conditionalLaw A B w=(stdGaussian E).map B := by
  rw [conditionalLaw_eq_translate,lift_map_eq_zero_of_cross_zero A B hcross]
  simp only [add_zero,Measure.map_id']
  rw [centeredLaw,residual_map_eq_of_cross_zero A B hcross]

end
end SlowEquilibration.GaussianRegressionCovariance

namespace SlowEquilibration.SphericalConditionalMatrices
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel WholeFieldRegression
open GaussianRegressionCovariance
variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

omit [FiniteDimensional ℝ G] in
/-- At every posterior target, all original tensor coordinates are retained
and their orthogonal complete matrix observation has its original law. -/
theorem unaffected_actualObservation_hasLaw {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F) (B : EuclideanDisorder N P →L[ℝ] G)
    (hcross : B.comp A.adjoint=0) (w : F) :
    HasLaw (actualObservation B) ((stdGaussian (EuclideanDisorder N P)).map B) (coefficientKernel A w) := by
  refine ⟨?_,?_⟩
  · exact (B.continuous.measurable.comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
        (flatDisorder_measurable N P))).aemeasurable
  · rw [coefficientKernel_linear_map,conditionalLaw_eq_original_of_cross_zero A B hcross w]

end
end SlowEquilibration.SphericalConditionalMatrices
