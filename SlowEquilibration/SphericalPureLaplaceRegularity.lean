-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeProfile

@[expose] public section

/-! Local regularity of the genuine pure-model latitude exponent and
Jacobian amplitude on the physical interval. -/

namespace SlowEquilibration.SphericalPureLaplaceRegularity
noncomputable section
open Set SphericalTAPCriticalPureLatitudeProfile
set_option autoImplicit false

theorem sourcePureLatitudeExponent_contDiffAt
    (p : ℕ) (alpha Q β e a : ℝ) (hQ : 0 < Q)
    (ha : a ∈ Ioo (-1:ℝ) 1) :
    ContDiffAt ℝ 2 (sourcePureLatitudeExponent p alpha Q β e) a := by
  have hroot : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have harg : 1-a^2 ≠ 0 := by
    have hp : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
    exact hp.ne'
  unfold sourcePureLatitudeExponent
  unfold SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance
  fun_prop (disch := assumption)

theorem sourcePureLatitudeExponent_contDiffOn
    (p : ℕ) (alpha Q β e : ℝ) (hQ : 0 < Q) :
    ContDiffOn ℝ 2 (sourcePureLatitudeExponent p alpha Q β e)
      (Ioo (-1:ℝ) 1) := by
  intro a ha
  exact (sourcePureLatitudeExponent_contDiffAt p alpha Q β e a hQ ha).contDiffWithinAt

def sourcePureLatitudeJacobian (a : ℝ) : ℝ :=
  (1-a^2)^(-(3/2:ℝ))

theorem sourcePureLatitudeJacobian_contact {Q : ℝ} (hQ : 0 ≤ Q) :
    sourcePureLatitudeJacobian (Real.sqrt Q) = (1-Q)^(-(3/2:ℝ)) := by
  unfold sourcePureLatitudeJacobian
  rw [Real.sq_sqrt hQ]

theorem sourcePureLatitudeJacobian_continuousAt
    {a : ℝ} (ha : a ∈ Ioo (-1:ℝ) 1) :
    ContinuousAt sourcePureLatitudeJacobian a := by
  have harg : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  unfold sourcePureLatitudeJacobian
  have hpoly : ContinuousAt (fun t : ℝ => 1-t^2) a := by fun_prop
  exact hpoly.rpow_const (Or.inl harg.ne')

theorem sourcePureLatitudeJacobian_bounded_on_band
    {l r : ℝ}
    (hband : Icc l r ⊆ Ioo (-1:ℝ) 1) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ a ∈ Icc l r, |sourcePureLatitudeJacobian a| ≤ M := by
  have hcont : ContinuousOn (fun a : ℝ => |sourcePureLatitudeJacobian a|)
      (Icc l r) := by
    intro a ha
    exact ((sourcePureLatitudeJacobian_continuousAt (hband ha)).abs).continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro a ha
  exact (hM ⟨a,ha,rfl⟩).trans (le_max_left _ _)

end
end SlowEquilibration.SphericalPureLaplaceRegularity
