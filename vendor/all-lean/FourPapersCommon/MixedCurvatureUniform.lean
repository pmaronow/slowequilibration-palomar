module
public import FourPapersCommon.MixedCurvature
public import FourPapersCommon.MixedInitialCurvature

@[expose] public section

/-! Actual depth-independent instability bound at every nondegenerate level. -/
noncomputable section
open Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def mixedInstabilityConstant (ξ : AdmissibleEvenMixture) : ℝ :=
  max (mixedInitialCurvatureConstant ξ)
    (4 * (mixedCurvatureLipschitz ξ + section4OptimalityBound (mixedBeta ξ)))

theorem mixedInstabilityConstant_nonneg (ξ : AdmissibleEvenMixture) :
    0 ≤ mixedInstabilityConstant ξ := by
  apply le_trans _ (le_max_right _ _)
  exact mul_nonneg (by norm_num) (add_nonneg (mixedCurvatureLipschitz_nonneg ξ)
    (section4OptimalityBound_pos (mixedBeta ξ)).le)

theorem mixed_instability_bound_all_levels (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε) :
    ξ.second (s.q r) * section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h r 0 - 1 ≤
      mixedInstabilityConstant ξ * ε ^ (1 / 6 : ℝ) := by
  have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [← mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  have hε : 0 ≤ ε := by linarith
  have hη : 0 ≤ ε ^ (1 / 6 : ℝ) := Real.rpow_nonneg hε _
  by_cases he : r = 1
  · subst r
    have hq : 0 < s.q 1 := by simpa only [Nat.sub_self, s.q_zero] using hleft
    have hm' : s.m 0 < s.m 1 := by simpa only [Nat.sub_self] using hm
    by_cases hshort : s.q 1 ≤ ε ^ (1 / 6 : ℝ)
    · have H := mixed_initial_curvature_bound ξ s h hm' hq hright hmin
      have hC : 0 ≤ mixedInitialCurvatureConstant ξ := by
        have hK : 0 ≤ ξ.jetBound := zero_le_one.trans ξ.jetBound_spec.1
        dsimp [mixedInitialCurvatureConstant]
        positivity
      exact H.trans ((mul_le_mul_of_nonneg_left hshort hC).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hη))
    · have H := mixedSection4FirstVariation_long_initial_curvature_bound ξ s h ε hm' hq
        hright hmin hnear (lt_of_not_ge hshort).le
      rw [mixedSection4FirstVariationD2_upper ξ s h (r := 1) le_rfl (by omega) hm
        (Or.inl hleft) hright hmin] at H
      have HE : 0 ≤ 2 * (mixedCurvatureLipschitz ξ + section4OptimalityBound (mixedBeta ξ)) * ε ^ (1 / 6 : ℝ) := by
        exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (mixedCurvatureLipschitz_nonneg ξ)
          (section4OptimalityBound_pos (mixedBeta ξ)).le)) hη
      have HH := mixed_instability_le_of_weighted_curvature (ξ.second_nonneg (s.q 1))
        (section4THessianSquare_mem_Icc (mixedClockScheme ξ s) (mixedBeta ξ) h (r := 1) (by omega) 0) HE H
      have HB := mul_le_mul_of_nonneg_right (le_max_right (mixedInitialCurvatureConstant ξ)
        (4 * (mixedCurvatureLipschitz ξ + section4OptimalityBound (mixedBeta ξ)))) hη
      change _ ≤ mixedInstabilityConstant ξ * ε ^ (1 / 6 : ℝ) at HB
      nlinarith only [HH, HB]
  · have H := mixed_noninitial_instability_bound ξ s h ε (by omega) hr hm hleft hright hmin hnear
    exact H.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hη)

end FourPapersCommon
