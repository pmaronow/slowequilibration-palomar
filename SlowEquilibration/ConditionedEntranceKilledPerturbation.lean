-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.UnitaryBoundedPerturbationCore

/-! Actual closed, self-adjoint bounded perturbations on the original
operator domain. No perturbed self-adjointness or core identity is a
premise. -/
@[expose] public section
noncomputable section
open Set
open scoped InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.KilledOperator
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def boundedPerturbation (A : E →ₗ.[ℝ] E) (V : E →L[ℝ] E) : E →ₗ.[ℝ] E where
  domain := A.domain
  toFun := A.toFun + V.toLinearMap.comp A.domain.subtype

omit [CompleteSpace E] in
@[simp] theorem boundedPerturbation_domain (A : E →ₗ.[ℝ] E) (V : E →L[ℝ] E) :
    (boundedPerturbation A V).domain = A.domain := rfl

omit [CompleteSpace E] in
@[simp] theorem boundedPerturbation_apply (A : E →ₗ.[ℝ] E) (V : E →L[ℝ] E)
    (x : A.domain) : boundedPerturbation A V x = A x + V (x : E) := rfl

theorem boundedPerturbation_selfAdjoint (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (V : E →L[ℝ] E) (hV : V.IsSymmetric) : IsSelfAdjoint (boundedPerturbation A V) := by
  let B := boundedPerturbation A V
  have hd : Dense (B.domain : Set E) := hA.dense_domain
  have hAf : A.IsFormalAdjoint A := by
    have h := LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [show A.adjoint = A from hA] at h
  have hBf : B.IsFormalAdjoint B := by
    intro x y
    change inner ℝ (A x+V (x : E)) (y : E) = inner ℝ (x : E) (A y+V (y : E))
    rw [inner_add_left,inner_add_right,hAf]
    exact congrArg (fun z => inner ℝ (x : E) (A y)+z) (hV (x : E) (y : E))
  have hBaf := LinearPMap.adjoint_isFormalAdjoint (T := B) hd
  have hback (y : B.adjoint.domain) : (y : E) ∈ B.domain := by
    have hm : (y : E) ∈ A.adjoint.domain := by
      apply A.mem_adjoint_domain_of_exists
      refine ⟨B.adjoint y-V (y : E),fun x => ?_⟩
      have hi := hBaf y x
      change inner ℝ (B.adjoint y) (x : E) = inner ℝ (y : E) (A x+V (x : E)) at hi
      rw [inner_add_right] at hi
      rw [inner_sub_left]
      have hv := hV (y : E) (x : E)
      change inner ℝ (V (y : E)) (x : E) = inner ℝ (y : E) (V (x : E)) at hv
      linarith
    rwa [show A.adjoint=A from hA] at hm
  have hle : B ≤ B.adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hd hBf
  have hge : B.adjoint ≤ B := by
    constructor
    · intro y hy
      exact hback ⟨y,hy⟩
    · intro y z hyz
      apply hd.eq_of_inner_left ℝ
      intro v hv
      have hi := hBaf y ⟨v,hv⟩
      have hj := hBf z ⟨v,hv⟩
      rw [hyz] at hi
      exact hi.trans hj.symm
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm hge hle)

theorem boundedPerturbation_isClosed (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (V : E →L[ℝ] E) (hV : V.IsSymmetric) : (boundedPerturbation A V).IsClosed :=
  (boundedPerturbation_selfAdjoint A hA V hV).isClosed

/-- Every true core of the original self-adjoint operator is a true core
of the actual bounded killing perturbation on exactly the same domain. -/
theorem boundedPerturbation_hasCore (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (V : E →L[ℝ] E) (hV : V.IsSymmetric) (C : Submodule ℝ E) (hC : A.HasCore C) :
    (boundedPerturbation A V).HasCore C := by
  have h := UnitaryBoundedPerturbation.hasCore_of_unitary_bounded_perturbation
    A (boundedPerturbation A V) hA (boundedPerturbation_selfAdjoint A hA V hV)
    (LinearIsometryEquiv.refl ℝ E) V hV C hC
    (fun x => hC.le_domain x.property) (fun _ => rfl)
  simpa only [LinearIsometryEquiv.toLinearEquiv_refl,LinearEquiv.refl_toLinearMap,Submodule.map_id] using h

end SlowEquilibration.ConditionedEntrance.KilledOperator
