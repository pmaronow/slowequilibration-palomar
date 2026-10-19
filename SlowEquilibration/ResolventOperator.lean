module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Tactic

@[expose] public section

/-!
# An actual self-adjoint unbounded operator from an injective resolvent

For a bounded injective symmetric Hilbert operator `R` with dense range, the
operator with domain `range R` and value `A(Rf)=f-Rf` is self-adjoint. Its
construction uses the actual inverse linear equivalence onto the range.
-/

namespace SlowEquilibration.ResolventOperator

noncomputable section
open Set Filter
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual unbounded inverse resolvent minus identity on its actual range. -/
def inverseShift (R : E →L[ℝ] E) (hR : Function.Injective R) : E →ₗ.[ℝ] E where
  domain := R.range
  toFun := (LinearEquiv.ofInjective R.toLinearMap hR).symm.toLinearMap - R.range.subtype

omit [CompleteSpace E] in
@[simp] theorem inverseShift_domain (R : E →L[ℝ] E) (hR : Function.Injective R) :
    (inverseShift R hR).domain = R.range := rfl

omit [CompleteSpace E] in
/-- Exact action of the constructed unbounded operator on its actual domain. -/
theorem inverseShift_apply (R : E →L[ℝ] E) (hR : Function.Injective R) (f : E) :
    inverseShift R hR ⟨R f, ⟨f, rfl⟩⟩ = f - R f := by
  change (LinearEquiv.ofInjective R.toLinearMap hR).symm ⟨R f, ⟨f, rfl⟩⟩ - R f = _
  have he : (⟨R f, ⟨f, rfl⟩⟩ : R.range) = LinearEquiv.ofInjective R.toLinearMap hR f := rfl
  rw [he, LinearEquiv.symm_apply_apply]

/-- Symmetry and injectivity force the actual resolvent range to be dense. -/
theorem dense_range (R : E →L[ℝ] E) (hR : Function.Injective R) (hS : R.IsSymmetric) :
    Dense (R.range : Set E) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, ContinuousLinearMap.orthogonal_range (𝕜 := ℝ),
    hS.clm_adjoint_eq]
  exact LinearMap.ker_eq_bot.mpr hR

omit [CompleteSpace E] in
/-- The actual inverse shift is symmetric on its full actual domain. -/
theorem inverseShift_formalAdjoint (R : E →L[ℝ] E) (hR : Function.Injective R)
    (hS : R.IsSymmetric) : (inverseShift R hR).IsFormalAdjoint (inverseShift R hR) := by
  intro u v
  obtain ⟨f, hf⟩ := u.property
  obtain ⟨g, hg⟩ := v.property
  have hu : u = (⟨R f, ⟨f, rfl⟩⟩ : (inverseShift R hR).domain) := Subtype.ext hf.symm
  have hv : v = (⟨R g, ⟨g, rfl⟩⟩ : (inverseShift R hR).domain) := Subtype.ext hg.symm
  rw [hu, hv]
  change inner ℝ (inverseShift R hR ⟨R f, ⟨f, rfl⟩⟩) (R g) =
    inner ℝ (R f) (inverseShift R hR ⟨R g, ⟨g, rfl⟩⟩)
  rw [inverseShift_apply R hR f, inverseShift_apply R hR g, inner_sub_left, inner_sub_right]
  have hs : inner ℝ (R f) g = inner ℝ f (R g) := hS f g
  exact congrArg (fun t => t - inner ℝ (R f) (R g)) hs.symm

/-- Every vector in the adjoint domain is actually in the inverse-resolvent
range: `R(A* y+y)=y`. This proves maximality without an assumed conclusion. -/
theorem inverseShift_adjoint_recover (R : E →L[ℝ] E) (hR : Function.Injective R)
    (hS : R.IsSymmetric) (y : (inverseShift R hR).adjoint.domain) :
    R ((inverseShift R hR).adjoint y + (y : E)) = (y : E) := by
  apply ext_inner_right ℝ
  intro f
  have hi := LinearPMap.adjoint_isFormalAdjoint (T := inverseShift R hR) (dense_range R hR hS)
    y ⟨R f, ⟨f, rfl⟩⟩
  rw [inverseShift_apply, inner_sub_right] at hi
  change inner ℝ ((inverseShift R hR).adjoint y) (R f) =
    inner ℝ (y : E) f - inner ℝ (y : E) (R f) at hi
  have hs : inner ℝ (R ((inverseShift R hR).adjoint y + (y : E))) f =
    inner ℝ ((inverseShift R hR).adjoint y + (y : E)) (R f) := hS _ f
  rw [hs, inner_add_left, hi]
  ring

/-- Self-adjointness of the actual unbounded inverse resolvent minus identity. -/
theorem inverseShift_selfAdjoint (R : E →L[ℝ] E) (hR : Function.Injective R)
    (hS : R.IsSymmetric) : IsSelfAdjoint (inverseShift R hR) := by
  have hd : Dense ((inverseShift R hR).domain : Set E) := dense_range R hR hS
  have hle : inverseShift R hR ≤ (inverseShift R hR).adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint hd (inverseShift_formalAdjoint R hR hS)
  have hge : (inverseShift R hR).adjoint ≤ inverseShift R hR := by
    constructor
    · intro y hy
      exact ⟨(inverseShift R hR).adjoint ⟨y, hy⟩ + y, inverseShift_adjoint_recover R hR hS ⟨y, hy⟩⟩
    · intro y z hyz
      let f := (inverseShift R hR).adjoint y + (y : E)
      have he : R f = (y : E) := inverseShift_adjoint_recover R hR hS y
      have hz : z = (⟨R f, ⟨f, rfl⟩⟩ : (inverseShift R hR).domain) := by
        apply Subtype.ext
        exact hyz.symm.trans he.symm
      rw [hz, inverseShift_apply, he]
      dsimp [f]
      exact (add_sub_cancel_right _ _).symm
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm hge hle)

/-- The operator is closed as a consequence of proved self-adjointness. -/
theorem inverseShift_isClosed (R : E →L[ℝ] E) (hR : Function.Injective R)
    (hS : R.IsSymmetric) : (inverseShift R hR).IsClosed :=
  (inverseShift_selfAdjoint R hR hS).isClosed

end
end SlowEquilibration.ResolventOperator
