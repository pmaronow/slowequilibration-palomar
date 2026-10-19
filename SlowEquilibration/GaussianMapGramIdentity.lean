-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianCorrelatedPairLaw

/-! Equal full centered Gaussian image laws identify the literal Gram,
including singular observations. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianRegression
open scoped RealInnerProductSpace
variable {E E' F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem gram_eq_of_gaussian_map_eq (A : E →L[ℝ] F) (B : E' →L[ℝ] F)
    (hLaw : (stdGaussian E).map A=(stdGaussian E').map B) : gram A=gram B := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℝ
  intro v
  have h:=congrArg (fun μ : Measure F => covarianceBilin μ v w) hLaw
  rw [covarianceBilin_map IsGaussian.memLp_two_id,covarianceBilin_map IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian,covarianceBilin_stdGaussian,innerSL_apply_apply,innerSL_apply_apply,
    A.adjoint_inner_left,B.adjoint_inner_left] at h
  exact h

end
end SlowEquilibration.GaussianObservationCoercivity
