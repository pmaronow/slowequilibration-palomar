-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPosteriorResidualVariance
public import SlowEquilibration.GaussianUnaffectedRegression

@[expose] public section

/-! A scalar Gaussian bank that is orthogonal to the conditioning observer
and captures its covariance with a field can be subtracted from the true
conditioned scalar variance by Pythagoras. -/

namespace SlowEquilibration.GaussianOrthogonalScalarResidualVariance
noncomputable section
open MeasureTheory ProbabilityTheory Function GaussianRegression
open GaussianRegressionCovariance SphericalTaylorRemainder
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 600000

private theorem scalarCLM_norm_sq_eq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →L[ℝ] ℝ) : ‖f‖^2=f (f.adjoint 1) := by
  have hf : f=innerSL ℝ (f.adjoint 1) := by
    ext x
    have hh : f x=inner ℝ (f.adjoint 1) x := by
      rw [f.adjoint_inner_left]
      simp
    simpa only [innerSL_apply_apply] using hh
  rw [hf,innerSL_apply_norm,ContinuousLinearMap.adjoint_innerSL_apply]
  simp [innerSL_apply_apply]

private theorem scalar_coupling_comm_generic {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f y : E →L[ℝ] ℝ) : f (y.adjoint 1)=y (f.adjoint 1) := by
  calc
    f (y.adjoint 1)=inner ℝ (f.adjoint 1) (y.adjoint 1) := by
      rw [f.adjoint_inner_left]
      simp
    _=inner ℝ (y.adjoint 1) (f.adjoint 1) := real_inner_comm _ _
    _=y (f.adjoint 1) := by
      rw [y.adjoint_inner_left]
      simp

theorem scalar_residual_bank_subtraction
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) (hA : Surjective A)
    (f y : E →L[ℝ] ℝ)
    (hyA : y.comp A.adjoint=0)
    (hyf : y (f.adjoint 1)=y (y.adjoint 1)) :
    ‖(f-y).comp (residual A)‖^2 =
      ‖f.comp (residual A)‖^2-‖y‖^2 := by
  let C := residual A
  let r := f.comp C
  have hyC : y.comp C=y := residual_map_eq_of_cross_zero A y hyA
  have hCadj : C.adjoint=C := residual_adjoint A hA
  have hyfixed : C (y.adjoint 1)=y.adjoint 1 := by
    have h := congrArg (fun T : E →L[ℝ] ℝ => T.adjoint 1) hyC
    simpa only [ContinuousLinearMap.adjoint_comp,hCadj,
      ContinuousLinearMap.comp_apply] using h
  have hry : r (y.adjoint 1)=y (y.adjoint 1) := by
    change f (C (y.adjoint 1)) = _
    rw [hyfixed,scalar_coupling_comm_generic f y]
    exact hyf
  have hyr : y (r.adjoint 1)=y (y.adjoint 1) := by
    rw [← scalar_coupling_comm_generic r y]
    exact hry
  have hs : (f-y).comp C=r-y := by
    ext x
    simp [r,hyC]
  rw [hs,scalarCLM_norm_sq_eq (r-y),
    scalarCLM_norm_sq_eq r,scalarCLM_norm_sq_eq y]
  simp only [sub_apply,map_sub]
  rw [hry,hyr]
  ring

end
end SlowEquilibration.GaussianOrthogonalScalarResidualVariance
