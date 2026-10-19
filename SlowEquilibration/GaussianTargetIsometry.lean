-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ObservationTargetEquiv

/-! Actual covariance determinant and literal zero-density invariance
under isometric changes of Gaussian observation coordinates. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace G] [BorelSpace G] in
lemma gram_det_target_isometry (A : E →L[ℝ] F) (e : F ≃ₗᵢ[ℝ] G) :
    (gram ((e : F →L[ℝ] G).comp A)).det=(gram A).det := by
  simp only [gram,ContinuousLinearMap.adjoint_comp,e.adjoint_eq_symm]
  change LinearMap.det ((e.toLinearEquiv.toLinearMap ∘ₗ (A.toLinearMap ∘ₗ A.adjoint.toLinearMap)) ∘ₗ
    e.symm.toLinearEquiv.toLinearMap)=LinearMap.det (A.toLinearMap ∘ₗ A.adjoint.toLinearMap)
  convert LinearMap.det_conj (A.toLinearMap ∘ₗ A.adjoint.toLinearMap) e.toLinearEquiv using 1
  congr 1

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace G] [BorelSpace G] in
/-- Pointwise identity at the specified zero target, including singular
observation maps; in the surjective case these are their actual densities. -/
theorem observationPdf_zero_target_isometry (A : E →L[ℝ] F) (e : F ≃ₗᵢ[ℝ] G) :
    observationPdf ((e : F →L[ℝ] G).comp A) 0=observationPdf A 0 := by
  rw [observationPdf_zero,observationPdf_zero,gram_det_target_isometry]
  have hn : GaussianDensity.normalizer G=GaussianDensity.normalizer F := by
    unfold GaussianDensity.normalizer
    rw [← e.toLinearEquiv.finrank_eq]
  rw [hn]

end
end SlowEquilibration.GaussianRegression
