module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic

@[expose] public section

/-! # An actual global smooth overlap profile with the source plateaus -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
open Set
open scoped ContDiff

/-- An explicit source profile, independent of the dimension and disorder. -/
def profile (K q₁ q₂ r : ℝ) : ℝ :=
  K*(1-Real.smoothTransition ((r-q₁)/(q₂-q₁)))

lemma profile_contDiff (K q₁ q₂ : ℝ) : ContDiff ℝ ∞ (profile K q₁ q₂) :=
  contDiff_const.mul (contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _)))

lemma profile_nonneg (K q₁ q₂ : ℝ) (hK : 0 ≤ K) (r : ℝ) : 0 ≤ profile K q₁ q₂ r :=
  mul_nonneg hK (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma profile_le (K q₁ q₂ : ℝ) (hK : 0 ≤ K) (r : ℝ) : profile K q₁ q₂ r ≤ K := by
  have hn := Real.smoothTransition.nonneg ((r-q₁)/(q₂-q₁))
  dsimp [profile]
  nlinarith

lemma profile_low (K : ℝ) {q₁ q₂ r : ℝ} (hq : q₁ < q₂) (hr : r ≤ q₁) :
    profile K q₁ q₂ r = K := by
  rw [profile, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hr) (sub_pos.mpr hq).le), sub_zero, mul_one]

lemma profile_high (K : ℝ) {q₁ q₂ r : ℝ} (hq : q₁ < q₂) (hr : q₂ ≤ r) :
    profile K q₁ q₂ r = 0 := by
  have hd : 1 ≤ (r-q₁)/(q₂-q₁) := (le_div_iff₀ (sub_pos.mpr hq)).mpr (by linarith)
  rw [profile, Real.smoothTransition.one_of_one_le hd, sub_self, mul_zero]

lemma profile_antitone (K : ℝ) {q₁ q₂ : ℝ} (hK : 0 ≤ K) (hq : q₁ < q₂) :
    Antitone (profile K q₁ q₂) := by
  intro x y hxy
  have hR : (x-q₁)/(q₂-q₁) ≤ (y-q₁)/(q₂-q₁) :=
    div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hq).le
  have hs := Real.smoothTransition.monotone hR
  dsimp [profile]
  nlinarith

/-- Its genuine derivative has a fixed finite bound on the entire source
closed overlap interval, obtained from compactness and proved C∞. -/
theorem exists_profile_deriv_bound (K q₁ q₂ : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ r ∈ Icc (-1:ℝ) 1, |deriv (profile K q₁ q₂) r| ≤ M := by
  have hc := (profile_contDiff K q₁ q₂).continuous_deriv (by simp)
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,fun r hr => ?_⟩
  have hb : |deriv (profile K q₁ q₂) r| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC r hr
  exact hb.trans (le_max_left _ _)

end
end SlowEquilibration.SphericalBarycenter
