module
public import FourPapersCommon.MixtureCoercivity

@[expose] public section

/-! Genuine compact derivative bounds for an admissible analytic covariance. -/
noncomputable section
open Set Filter Topology
namespace FourPapersCommon.AdmissibleEvenMixture
set_option maxHeartbeats 600000

theorem continuousOn_third (ξ : AdmissibleEvenMixture) :
    ContinuousOn (deriv ξ.second) (Icc (0 : ℝ) 1) := by
  intro x hx
  exact ((ξ.analyticAt_second (by rw [abs_of_nonneg hx.1]; linarith [hx.2])).deriv.continuousAt).continuousWithinAt

theorem continuousOn_fourth (ξ : AdmissibleEvenMixture) :
    ContinuousOn (deriv (deriv ξ.second)) (Icc (0 : ℝ) 1) := by
  intro x hx
  exact ((ξ.analyticAt_second (by rw [abs_of_nonneg hx.1]; linarith [hx.2])).deriv.deriv.continuousAt).continuousWithinAt

theorem exists_jetBound (ξ : AdmissibleEvenMixture) :
    ∃ K : ℝ, 1 ≤ K ∧ ξ.second 1 ≤ K ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |deriv ξ.second x| ≤ K) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |deriv (deriv ξ.second) x| ≤ K) := by
  obtain ⟨K3, hK3⟩ := isCompact_Icc.exists_bound_of_continuousOn (ξ.continuousOn_third)
  obtain ⟨K4, hK4⟩ := isCompact_Icc.exists_bound_of_continuousOn (ξ.continuousOn_fourth)
  refine ⟨max (max 1 (ξ.second 1)) (max K3 K4), ?_, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · intro x hx
    exact (show |deriv ξ.second x| ≤ K3 by simpa only [Real.norm_eq_abs] using hK3 x hx).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · intro x hx
    exact (show |deriv (deriv ξ.second) x| ≤ K4 by simpa only [Real.norm_eq_abs] using hK4 x hx).trans
      ((le_max_right _ _).trans (le_max_right _ _))

def jetBound (ξ : AdmissibleEvenMixture) : ℝ := Classical.choose ξ.exists_jetBound

theorem jetBound_spec (ξ : AdmissibleEvenMixture) :
    1 ≤ ξ.jetBound ∧ ξ.second 1 ≤ ξ.jetBound ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |deriv ξ.second x| ≤ ξ.jetBound) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |deriv (deriv ξ.second) x| ≤ ξ.jetBound) :=
  Classical.choose_spec ξ.exists_jetBound

theorem hasDerivAt_second_unit (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    HasDerivAt ξ.second (deriv ξ.second q) q :=
  (ξ.analyticAt_second (by rw [abs_of_nonneg hq.1]; linarith [hq.2])).differentiableAt |>.hasDerivAt

theorem hasDerivAt_third_unit (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (deriv ξ.second) (deriv (deriv ξ.second) q) q :=
  (ξ.analyticAt_second (by rw [abs_of_nonneg hq.1]; linarith [hq.2])).deriv.differentiableAt |>.hasDerivAt

theorem second_lipschitz_unit (ξ : AdmissibleEvenMixture) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |ξ.second x - ξ.second y| ≤ ξ.jetBound * |x - y| := by
  have H := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (ξ.hasDerivAt_second_unit hz).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using ξ.jetBound_spec.2.2.1 z hz) hy hx
  simpa only [Real.norm_eq_abs] using H

theorem third_lipschitz_unit (ξ : AdmissibleEvenMixture) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |deriv ξ.second x - deriv ξ.second y| ≤ ξ.jetBound * |x - y| := by
  have H := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (ξ.hasDerivAt_third_unit hz).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using ξ.jetBound_spec.2.2.2 z hz) hy hx
  simpa only [Real.norm_eq_abs] using H

end FourPapersCommon.AdmissibleEvenMixture
