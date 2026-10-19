-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKilledPerturbation
public import SlowEquilibration.SemigroupCoreLaplace

/-! A bounded left inverse on the full domain of a self-adjoint operator
is automatically its genuine two-sided inverse. This supplies the
maximality step after the physical core Laplace identity. -/
@[expose] public section
noncomputable section
open Set
open scoped InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.KilledOperator
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem adjoint_leftInverse_domain (B : E →ₗ.[ℝ] E) (hB : IsSelfAdjoint B)
    (R : E →L[ℝ] E) (hleft : ∀ x : B.domain, R (B x) = (x : E)) (y : E) :
    R.adjoint y ∈ B.domain := by
  have hm : R.adjoint y ∈ B.adjoint.domain := by
    apply B.mem_adjoint_domain_of_exists
    refine ⟨y,fun x => ?_⟩
    rw [ContinuousLinearMap.adjoint_inner_left,hleft]
  rwa [show B.adjoint=B from hB] at hm

theorem adjoint_leftInverse_apply (B : E →ₗ.[ℝ] E) (hB : IsSelfAdjoint B)
    (R : E →L[ℝ] E) (hleft : ∀ x : B.domain, R (B x) = (x : E)) (y : E) :
    B ⟨R.adjoint y,adjoint_leftInverse_domain B hB R hleft y⟩ = y := by
  have hd := adjoint_leftInverse_domain B hB R hleft y
  have hf : ∀ x : B.domain, inner ℝ y (x : E) = inner ℝ (R.adjoint y) (B x) := by
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left,hleft]
  have hformal : B.IsFormalAdjoint B := by
    have h := LinearPMap.adjoint_isFormalAdjoint (T := B) hB.dense_domain
    rwa [show B.adjoint=B from hB] at h
  apply hB.dense_domain.eq_of_inner_left ℝ
  intro v hv
  exact (hformal ⟨R.adjoint y,hd⟩ ⟨v,hv⟩).trans (hf ⟨v,hv⟩).symm

/-- The actual bounded Laplace inverse becomes symmetric and onto the
operator domain by adjoint maximality, without a symmetry premise on the
physical killed transition semigroup. -/
theorem leftInverse_eq_adjoint (B : E →ₗ.[ℝ] E) (hB : IsSelfAdjoint B)
    (R : E →L[ℝ] E) (hleft : ∀ x : B.domain, R (B x) = (x : E)) : R = R.adjoint := by
  ext y
  have h := hleft ⟨R.adjoint y,adjoint_leftInverse_domain B hB R hleft y⟩
  rw [adjoint_leftInverse_apply B hB R hleft y] at h
  exact h

theorem leftInverse_domain (B : E →ₗ.[ℝ] E) (hB : IsSelfAdjoint B)
    (R : E →L[ℝ] E) (hleft : ∀ x : B.domain, R (B x) = (x : E)) (y : E) : R y ∈ B.domain := by
  rw [leftInverse_eq_adjoint B hB R hleft]
  exact adjoint_leftInverse_domain B hB R hleft y

theorem leftInverse_rightInverse (B : E →ₗ.[ℝ] E) (hB : IsSelfAdjoint B)
    (R : E →L[ℝ] E) (hleft : ∀ x : B.domain, R (B x) = (x : E)) (y : E) :
    B ⟨R y,leftInverse_domain B hB R hleft y⟩ = y := by
  have h := adjoint_leftInverse_apply B hB R hleft y
  convert h using 1
  congr 1
  exact Subtype.ext (congrArg (fun T : E →L[ℝ] E => T y)
    (leftInverse_eq_adjoint B hB R hleft))

end SlowEquilibration.ConditionedEntrance.KilledOperator
