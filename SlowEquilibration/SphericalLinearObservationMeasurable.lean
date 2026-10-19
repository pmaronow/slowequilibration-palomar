-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianClippedInverseField

/-! Borel measurability of actual coefficient-linear observations and
actual tensor Hessian matrices in the original disorder coordinates. -/
@[expose] public section
namespace SlowEquilibration.WholeFieldRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel

@[fun_prop]
lemma actual_linearObservation_measurable {N P : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (A : EuclideanDisorder N P →L[ℝ] F) : Measurable (actualObservation A) :=
  A.continuous.measurable.comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P=>ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P))

end
end SlowEquilibration.WholeFieldRegression

namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression

@[fun_prop]
lemma tensor_hessianMatrix_measurable {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) : Measurable (hessianMatrix c x e) := by
  convert (unflattenMatrix_measurable m).comp
    (actual_linearObservation_measurable (flatHessianCLM c x e)) using 1
  funext J
  exact (unflattenMatrix_actual_hessian c x e J).symm

end
end SlowEquilibration.SphericalCommonHessianRegression

