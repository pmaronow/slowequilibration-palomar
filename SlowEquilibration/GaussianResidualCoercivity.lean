-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegressionSchur
public import SlowEquilibration.GaussianObservationCoercivity

/-! A true joint observation lower bound gives the same dimension-free
lower bound for the actual conditional residual observation. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

theorem residual_coercivity (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] G) {α : ℝ} (hα : 0 ≤ α)
    (hjoint : CoerciveObservation (pairHilbert B A) α) :
    CoerciveObservation (B.comp (GaussianRegression.residual A)) α := by
  intro u
  let v:=-(gram A).inverse (A (B.adjoint u))
  let w:WithLp 2 (G×F):=WithLp.toLp 2 (u,v)
  have heq : (pairHilbert B A).adjoint w=(B.comp (GaussianRegression.residual A)).adjoint u := by
    rw [pairHilbert_adjoint,ContinuousLinearMap.adjoint_comp,residual_adjoint A hA]
    change B.adjoint u+A.adjoint v=GaussianRegression.residual A (B.adjoint u)
    simp only [v,map_neg]
    change B.adjoint u + -(A.adjoint ((gram A).inverse (A (B.adjoint u))))=
      B.adjoint u-A.adjoint ((gram A).inverse (A (B.adjoint u)))
    rw [sub_eq_add_neg]
  have hh:=hjoint w
  rw [heq] at hh
  have hnorm : ‖u‖^2 ≤ ‖w‖^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖u‖^2 ≤ ‖u‖^2+‖v‖^2
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left hnorm hα).trans hh

/-- The resulting actual residual Gram inverse bound has the joint
coercivity constant; no determinant or eigenbasis hypothesis is required. -/
theorem residual_gram_inverse_bound (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] G) {α : ℝ} (hα : 0 < α)
    (hjoint : CoerciveObservation (pairHilbert B A) α) :
    Surjective (B.comp (GaussianRegression.residual A)) ∧ ‖(gram (B.comp (GaussianRegression.residual A))).inverse‖ ≤ 1/α := by
  have h:=residual_coercivity A hA B hα.le hjoint
  exact ⟨observation_surjective _ hα h,gram_inverse_norm_le _ hα h⟩

end
end SlowEquilibration.GaussianObservationCoercivity
