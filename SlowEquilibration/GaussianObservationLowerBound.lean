-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianObservationCoercivity

@[expose] public section

/-! A genuine positive coercivity constant for every finite surjective observation. -/
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_coercivity_of_surjective (A : E →L[ℝ] F) (hA : Surjective A) :
    ∃ α : ℝ, 0 < α ∧ CoerciveObservation A α := by
  let B := (GaussianRegression.gram A).inverse.comp A
  let M : ℝ := ‖B‖+1
  have hM : 0 < M := by dsimp [M];positivity
  have hleft : B.comp A.adjoint=ContinuousLinearMap.id ℝ F := by
    dsimp [B]
    rw [ContinuousLinearMap.comp_assoc]
    exact (GaussianRegression.gram_isInvertible A hA).inverse_comp_self
  refine ⟨1/M^2,by positivity,?_⟩
  intro u
  have he : B (A.adjoint u)=u := congrArg (fun T : F →L[ℝ] F => T u) hleft
  have hb : ‖u‖ ≤ M*‖A.adjoint u‖ := by
    calc
      _ = ‖B (A.adjoint u)‖ := congrArg norm he.symm
      _ ≤ ‖B‖*‖A.adjoint u‖ := B.le_opNorm _
      _ ≤ _ := by dsimp [M];nlinarith [norm_nonneg (A.adjoint u)]
  have hp := pow_le_pow_left₀ (norm_nonneg u) hb 2
  rw [mul_pow] at hp
  have hd : ‖u‖^2/M^2 ≤ ‖A.adjoint u‖^2 :=
    (div_le_iff₀ (sq_pos_of_pos hM)).mpr (by nlinarith [hp])
  convert hd using 1
  ring

end
end SlowEquilibration.GaussianObservationCoercivity
