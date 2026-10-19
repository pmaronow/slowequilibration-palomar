-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Positive coercive Hilbert operators have actual inverses whose
parameter dependence is continuous. No inverse or continuity oracle. -/
@[expose] public section
noncomputable section
open Filter InnerProductSpace
open scoped InnerProductSpace Topology
namespace SlowEquilibration.CoerciveOperatorContinuity
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem isUnit_of_inner_lower_bound (A : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hA : ∀ u,c*‖u‖^2 ≤ inner ℝ (A u) u) : IsUnit A := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).comp A
  have hB : IsCoercive B := by
    refine ⟨c,hc,?_⟩
    intro u
    change c*‖u‖*‖u‖ ≤ inner ℝ (A u) u
    nlinarith [hA u]
  have he : continuousLinearMapOfBilin B=A := by
    ext u
    apply ext_inner_right ℝ
    intro v
    rw [continuousLinearMapOfBilin_apply]
    rfl
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  rw [← he]
  exact hB.continuousLinearEquivOfBilin.bijective

theorem inverse_apply_equation (A : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hA : ∀ u,c*‖u‖^2 ≤ inner ℝ (A u) u) (f : E) :
    A (Ring.inverse A f)=f := by
  have hi := Ring.mul_inverse_cancel A (isUnit_of_inner_lower_bound A c hc hA)
  exact congrArg (fun T : E →L[ℝ] E => T f) hi

theorem inverse_continuous {Θ : Type*} [TopologicalSpace Θ]
    (A : Θ → E →L[ℝ] E) (hA : Continuous A)
    (hc : ∀ p,∃ c : ℝ,0<c ∧ ∀ u,c*‖u‖^2 ≤ inner ℝ (A p u) u) :
    Continuous (fun p => Ring.inverse (A p)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨c,hc0,hcp⟩ := hc p
  obtain ⟨a,ha⟩ := isUnit_of_inner_lower_bound (A p) c hc0 hcp
  have hi : ContinuousAt Ring.inverse (A p) := ha ▸ NormedRing.inverse_continuousAt a
  exact hi.comp hA.continuousAt

theorem solution_continuous {Θ : Type*} [TopologicalSpace Θ]
    (A : Θ → E →L[ℝ] E) (hA : Continuous A)
    (hc : ∀ p,∃ c : ℝ,0<c ∧ ∀ u,c*‖u‖^2 ≤ inner ℝ (A p u) u)
    (f : Θ → E) (hf : Continuous f) :
    Continuous (fun p => Ring.inverse (A p) (f p)) :=
  (inverse_continuous A hA hc).clm_apply hf

end SlowEquilibration.CoerciveOperatorContinuity
