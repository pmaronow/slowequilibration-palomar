-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairGramSchurDeterminant
public import SlowEquilibration.NearIdentityLogDeterminant

/-! A genuine quadratic log-determinant error for actual isotropic pair
Gram operators. The cross block enters squared through the exact Schur
complement; no linear-in-correlation determinant bound is substituted. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem isotropic_pair_gram_logdet (A B : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hA : gram A=a • ContinuousLinearMap.id ℝ F)
    (hB : gram B=a • ContinuousLinearMap.id ℝ F)
    (hcross : ‖A.comp B.adjoint‖ ≤ a/2) :
    0 < (gram (pairHilbert A B)).det ∧
      |Real.log (gram (pairHilbert A B)).det-2*(Module.finrank ℝ F:ℝ)*Real.log a| ≤
        2*(Module.finrank ℝ F:ℝ)*(‖A.comp B.adjoint‖/a)^2 := by
  let T:=A.comp B.adjoint
  let C:=(a⁻¹^2) • T.adjoint.comp T
  let ε:=(‖T‖/a)^2
  have hAdj : B.comp A.adjoint=T.adjoint := by
    dsimp only [T]
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  have hC : C.toLinearMap.IsSymmetric := by
    intro u v
    change inner ℝ (a⁻¹^2 • T.adjoint (T u)) v=inner ℝ u (a⁻¹^2 • T.adjoint (T v))
    rw [real_inner_smul_left,inner_smul_right,T.adjoint_inner_left,T.adjoint_inner_right]
  have hε : 0 ≤ ε := sq_nonneg _
  have hhalf : ε ≤ 1/2 := by
    have hdiv : ‖T‖/a ≤ 1/2 := (div_le_iff₀ ha).mpr (by nlinarith [hcross])
    have hdiv0 : 0 ≤ ‖T‖/a := div_nonneg (norm_nonneg _) ha.le
    dsimp only [ε]
    nlinarith
  have hbound : ‖C‖ ≤ ε := by
    calc
      _ = a⁻¹^2*‖T.adjoint.comp T‖ := by dsimp only [C]; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      _ ≤ a⁻¹^2*(‖T.adjoint‖*‖T‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (sq_nonneg _)
      _ = ε := by rw [LinearIsometryEquiv.norm_map];dsimp [ε];field_simp
  have hlog:=NearIdentityLogDeterminant.det_positive_and_abs_log_le C hC hε hhalf hbound
  have hdet : (gram (pairHilbert A B)).det=
      a^(2*Module.finrank ℝ F)*(ContinuousLinearMap.id ℝ F-C).det := by
    rw [isotropic_pair_gram_det A B ha.ne' hA hB,hAdj]
  have hpos : 0 < (gram (pairHilbert A B)).det := by rw [hdet];exact mul_pos (pow_pos ha _) hlog.1
  have heq : Real.log (gram (pairHilbert A B)).det-2*(Module.finrank ℝ F:ℝ)*Real.log a=
      Real.log (ContinuousLinearMap.id ℝ F-C).det := by
    rw [hdet,Real.log_mul (pow_pos ha _).ne' hlog.1.ne',Real.log_pow]
    push_cast
    ring
  exact ⟨hpos,by rw [heq];exact hlog.2⟩

end
end SlowEquilibration.GaussianObservationCoercivity
