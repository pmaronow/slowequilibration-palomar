module
public import FourPapersCommon.MixedCurvature
public import FourPapersCommon.MixedSecondInterpolationComparison

@[expose] public section

/-! A genuine small-time deficit for arbitrary signed physical constraints.
Using the trial overlap at the actual stationary level avoids the open-time
restriction of the strict interleaved scalar comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
set_option maxHeartbeats 800000

def mixedSmallTime (ξ : AdmissibleEvenMixture) : ℝ := 1 / (4 * ξ.jetBound)

theorem mixedSmallTime_pos (ξ : AdmissibleEvenMixture) : 0 < mixedSmallTime ξ := by
  have hK : 0 < ξ.jetBound := lt_of_lt_of_le (by norm_num) ξ.jetBound_spec.1
  exact one_div_pos.mpr (mul_pos (by norm_num) hK)

theorem mixedSmallTime_le_one (ξ : AdmissibleEvenMixture) : mixedSmallTime ξ ≤ 1 := by
  have hK : 0 < ξ.jetBound := lt_of_lt_of_le (by norm_num) ξ.jetBound_spec.1
  rw [mixedSmallTime, div_le_iff₀ (mul_pos (by norm_num) hK)]
  linarith [ξ.jetBound_spec.1]

theorem exists_mixedSmallTime_scalar_gain (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (u : ℝ) :
    ∃ ℓ : ℝ, section5V (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1)) 0 ℓ - ℓ * u ≤
      2 * parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h - (u - s.q r) ^ 2 / 2 := by
  have hv : (0 : ℝ) ∈ Icc 0 ((mixedBeta ξ) ^ 2 *
      ((mixedClockScheme ξ s).q r - (mixedClockScheme ξ s).q (r - 1))) :=
    ⟨le_rfl, mul_nonneg (sq_nonneg _) (sub_nonneg.mpr
      ((mixedClockScheme ξ s).q_mono' r (by omega) (r - 1) (by omega)))⟩
  obtain ⟨ℓ, H⟩ := section5V_baseline_lambda_gain_Q (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hv u
  simp only [mixedClockScheme_m] at H
  rw [mixed_endpointQ_eq_overlap_of_min_all_levels ξ s h hr0 hr hm hleft hright hmin] at H
  refine ⟨ℓ, ?_⟩
  simpa only [sub_sq_comm] using H

theorem mixed_constrainedPhi_small_time_signed_gain
    {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) (mixedSmallTime ξ)) (hu : u ∈ Icc (-1 : ℝ) 1)
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      2 * mixedInterpolationPsi ξ s h t - (u - s.q r) ^ 2 / 4 := by
  obtain ⟨ℓ, Hℓ⟩ := exists_mixedSmallTime_scalar_gain ξ s h hr0 hr hm hleft hright hmin u
  have hm0 := s.m_nonneg (p := r - 1) (by omega)
  have hma : s.m (r - 1) ∈ Icc (s.m (r - 1) / 2) (s.m r) := ⟨by linarith, hm.le⟩
  have hqr : s.q r ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [s.q_nonneg (by omega : r ≤ k + 2)], s.q_le_one (by omega)⟩
  have H := mixedLeft_constrainedPhi_le hn ξ s h sk (u := u) (v := s.q r) hr0 hr hma
    ⟨ht.1, ht.2.trans (mixedSmallTime_le_one ξ)⟩
    ⟨s.q_mono' r (by omega) (r - 1) (by omega), le_rfl⟩ ℓ
  simp only [mixedLeftSplitVariance, sub_self, mul_zero, add_zero] at H
  have HK := ξ.jetBound_spec.2.1
  have HR := ξ.tangentRemainder_quadratic_upper hu hqr
  have HR' : ξ.tangentRemainder u (s.q r) ≤ ξ.jetBound * (u - s.q r) ^ 2 :=
    HR.trans (mul_le_mul_of_nonneg_right HK (sq_nonneg _))
  have HT := mul_le_mul_of_nonneg_left HR' ht.1
  have hK : 0 < ξ.jetBound := lt_of_lt_of_le (by norm_num) ξ.jetBound_spec.1
  have htK : t * ξ.jetBound ≤ 1 / 4 := by
    have HH := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hK)).mp ht.2
    change t * (4 * ξ.jetBound) ≤ 1 at HH
    linarith
  have HQ := mul_le_mul_of_nonneg_right htK (sq_nonneg (u - s.q r))
  unfold mixedInterpolationPsi
  nlinarith only [H, Hℓ, HT, HQ]

end FourPapersCommon
