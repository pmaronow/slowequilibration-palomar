-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianObservationCoercivity

/-! Actual inverse Gram perturbation and Gaussian quadratic-energy bounds. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem inverse_difference_identity (S T : F →L[ℝ] F) (hS : S.IsInvertible) (hT : T.IsInvertible) :
    S.inverse-T.inverse=(S.inverse.comp (T-S)).comp T.inverse := by
  ext u
  simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub]
  rw [hT.self_apply_inverse]
  have hh:=congrArg (fun L : F →L[ℝ] F => L (T.inverse u)) hS.inverse_comp_self
  change S.inverse (S (T.inverse u))=T.inverse u at hh
  rw [hh]

theorem inverse_difference_bound (S T : F →L[ℝ] F) (hS : S.IsInvertible) (hT : T.IsInvertible) :
    ‖S.inverse-T.inverse‖ ≤ ‖S.inverse‖*‖S-T‖*‖T.inverse‖ := by
  rw [inverse_difference_identity S T hS hT]
  calc
    _ ≤ ‖S.inverse.comp (T-S)‖*‖T.inverse‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖S.inverse‖*‖T-S‖)*‖T.inverse‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by rw [norm_sub_rev]

/-- Literal difference of Gaussian target energies, retaining the true
squared target norm and both actual inverse bounds. -/
theorem inverse_quadratic_difference_bound (S T : F →L[ℝ] F)
    (hS : S.IsInvertible) (hT : T.IsInvertible) (w : F) :
    |inner ℝ w (S.inverse w)-inner ℝ w (T.inverse w)| ≤
      ‖S.inverse‖*‖S-T‖*‖T.inverse‖*‖w‖^2 := by
  rw [← inner_sub_right,← sub_apply]
  calc
    _ ≤ ‖w‖*‖(S.inverse-T.inverse) w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖w‖*(‖S.inverse-T.inverse‖*‖w‖) :=
      mul_le_mul_of_nonneg_left ((S.inverse-T.inverse).le_opNorm w) (norm_nonneg w)
    _ ≤ ‖w‖*((‖S.inverse‖*‖S-T‖*‖T.inverse‖)*‖w‖) := by
      gcongr
      exact inverse_difference_bound S T hS hT
    _ = _ := by ring

end
end SlowEquilibration.GaussianObservationCoercivity
