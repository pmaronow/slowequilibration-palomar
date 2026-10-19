-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegressionCovariance
public import SlowEquilibration.GaussianOrthogonalRegression

/-! Actual residual score covariance and its Schur complement after
conditioning on a genuine finite-dimensional Gaussian observation. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

lemma residual_adjoint (A : E →L[ℝ] F) (hA : Surjective A) :
    (residual A).adjoint=residual A := by
  rw [residual_eq_starProjection A hA]
  exact A.ker.starProjection_isSymmetric.clm_adjoint_eq

lemma residual_comp_self (A : E →L[ℝ] F) (hA : Surjective A) :
    (residual A).comp (residual A)=residual A := by
  rw [residual_eq_starProjection A hA]
  exact Submodule.starProjection_comp_starProjection_of_le le_rfl

/-- The actual centered residual observation has the literal Schur Gram. -/
theorem residual_gram_schur (A : E →L[ℝ] F) (hA : Surjective A) (B : E →L[ℝ] G) :
    gram (B.comp (residual A))=gram B-
      ((B.comp A.adjoint).comp (gram A).inverse).comp (A.comp B.adjoint) := by
  calc
    gram (B.comp (residual A))=
      (B.comp ((residual A).comp (residual A))).comp B.adjoint := by
        rw [gram,ContinuousLinearMap.adjoint_comp,residual_adjoint A hA]
        simp only [ContinuousLinearMap.comp_assoc]
    _=(B.comp (residual A)).comp B.adjoint := by rw [residual_comp_self A hA]
    _=_ := by
      ext z
      simp only [gram,residual,lift,ContinuousLinearMap.comp_apply,sub_apply,
        ContinuousLinearMap.id_apply,map_sub]

/-- Conditioning reduces the Gram by the genuine squared cross coupling,
with no dimension factor in this perturbation bound. -/
theorem residual_gram_difference_bound (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] G) :
    ‖gram (B.comp (residual A))-gram B‖ ≤
      ‖B.comp A.adjoint‖^2*‖(gram A).inverse‖ := by
  rw [residual_gram_schur A hA B,sub_sub_cancel_left,norm_neg]
  have hadj : A.comp B.adjoint=(B.comp A.adjoint).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  rw [hadj]
  calc
    _ ≤ ‖(B.comp A.adjoint).comp (gram A).inverse‖*‖(B.comp A.adjoint).adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖B.comp A.adjoint‖*‖(gram A).inverse‖)*‖(B.comp A.adjoint).adjoint‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by rw [LinearIsometryEquiv.norm_map];ring

omit [FiniteDimensional ℝ G] in
lemma residual_observation_cross_zero (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] G) : (B.comp (residual A)).comp A.adjoint=0 := by
  have hz : A.comp (residual A)=0 := by
    ext z
    exact residual_mem_ker A hA z
  have hadj:=congrArg ContinuousLinearMap.adjoint hz
  simp only [ContinuousLinearMap.adjoint_comp,residual_adjoint A hA,map_zero] at hadj
  rw [ContinuousLinearMap.comp_assoc,hadj,ContinuousLinearMap.comp_zero]

end
end SlowEquilibration.GaussianRegression
