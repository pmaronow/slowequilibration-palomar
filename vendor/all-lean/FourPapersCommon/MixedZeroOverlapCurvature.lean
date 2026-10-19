module
public import FourPapersCommon.MixedZeroOverlapVariation
public import Targets.OneSidedCurvature

@[expose] public section

/-! The genuine boundary curvature bound for mixtures containing a quadratic
term. Only a same-depth physical-overlap competitor is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem mixed_parisiFDeriv_initial_zero_of_min {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (hq : s.q 1 = 0) (hm : s.m 0 < s.m 1) (hq2 : 0 < s.q 2)
    (hmin : ∀ s' : RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    parisiFDeriv (mixedClockScheme ξ s) (mixedBeta ξ) (k+1) h=0 := by
  have H : section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h 1 (s.m 0) 0=0 := by
    cases k with
    | zero =>
      have hh := mixed_endpointQ_eq_overlap_of_min_terminal ξ s h
        (by simpa only [s.m_top] using hm) (Or.inr hq) hmin
      simpa only [Nat.zero_add,hq] using hh
    | succ k =>
      have hh := mixed_endpointQ_eq_overlap_of_min_nonterminal ξ s h (r := 1) le_rfl
        (by omega) (by simpa only [Nat.sub_self] using hm) (Or.inr hq)
        (Or.inl (by simpa only [hq] using hq2)) hmin
      simpa only [Nat.sub_self,hq] using hh
  rw [section4TVarianceQ_initial_zero_eq_sq (mixedClockScheme ξ s) (mixedBeta ξ) h
    (s.m 0) (by simp only [mixedClockScheme_q,hq,ξ.clock_zero])] at H
  exact sq_eq_zero_iff.mp H

theorem mixed_initial_zero_curvature_bound {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (hq : s.q 1 = 0) (hm : s.m 0 < s.m 1) (hq2 : 0 < s.q 2)
    (hmin : ∀ s' : RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    ξ.second 0*section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0 ≤ 1 := by
  by_cases hsec : 0 < ξ.second 0
  · have hm1 : 0 < s.m 1 := by simpa only [s.m_zero] using hm
    have hqclock : (mixedClockScheme ξ s).q 1=0 := by simp only [mixedClockScheme_q,hq,ξ.clock_zero]
    have hV : 0 < (mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2 := by
      rw [mixedClockScheme_q,mixedBeta_sq_mul_clock]
      have H := ξ.first_strictMonoOn (show (0:ℝ)∈Icc (-1:ℝ) 1 by norm_num)
        (show s.q 2∈Icc (-1:ℝ) 1 from ⟨by linarith [s.q_nonneg (p := 2) (by omega)],s.q_le_one (by omega)⟩) hq2
      simpa only [ξ.first_zero] using H
    have hS : stepD1 (parisiF (mixedClockScheme ξ s) (mixedBeta ξ) k)
        (parisiFDeriv (mixedClockScheme ξ s) (mixedBeta ξ) k) (s.m 1)
        ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2) h=0 := by
      change stepD1 (parisiF (mixedClockScheme ξ s) (mixedBeta ξ) k)
        (parisiFDeriv (mixedClockScheme ξ s) (mixedBeta ξ) k) ((mixedClockScheme ξ s).m 1)
        ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2) h=0
      rw [stepD1_initial_totalVariance (mixedClockScheme ξ s) (mixedBeta ξ) h hqclock]
      exact mixed_parisiFDeriv_initial_zero_of_min ξ s h hq hm hq2 hmin
    let Q := zeroOuterSquaredSlope (parisiF (mixedClockScheme ξ s) (mixedBeta ξ) k)
      (parisiFDeriv (mixedClockScheme ξ s) (mixedBeta ξ) k)
      (s.m 1) ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2) h
    let R := (parisiFSecond (mixedClockScheme ξ s) (mixedBeta ξ) (k+1) h)^2
    let c := ξ.second 0*s.m 1/2
    have hc : 0 < c := div_pos (mul_pos hsec hm1) (by norm_num)
    have hQ0 : Q 0=0 := by
      dsimp only [Q]
      rw [zeroOuterSquaredSlope_zero,hS]
      norm_num
    have hDQ : HasDerivWithinAt Q R (Icc 0 ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2)) 0 := by
      have H := hasDerivWithinAt_zeroOuterSquaredSlope_zero
        (parisiF_hasLinearGrowth (mixedClockScheme ξ s) (mixedBeta ξ) k)
        (parisiF_C2_props (mixedClockScheme ξ s) (mixedBeta ξ) k).1
        (continuous_parisiFSecond (mixedClockScheme ξ s) (mixedBeta ξ) k)
        (show s.m 1∈Icc (0:ℝ) 1 from ⟨s.m_nonneg (by omega),s.m_le_one (by omega)⟩) hV hS
      change HasDerivWithinAt Q ((stepD2 (parisiF (mixedClockScheme ξ s) (mixedBeta ξ) k)
        (parisiFDeriv (mixedClockScheme ξ s) (mixedBeta ξ) k)
        (parisiFSecond (mixedClockScheme ξ s) (mixedBeta ξ) k) ((mixedClockScheme ξ s).m 1)
        ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2) h)^2)
        (Icc 0 ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2)) 0 at H
      rw [stepD2_initial_totalVariance (mixedClockScheme ξ s) (mixedBeta ξ) h hqclock] at H
      exact H
    have hmap : MapsTo ξ.first (Icc 0 (s.q 2)) (Icc 0 ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2)) := by
      intro u hu
      rw [mixedClockScheme_q,mixedBeta_sq_mul_clock]
      refine ⟨ξ.first_nonneg hu.1,?_⟩
      exact ξ.first_strictMonoOn.monotoneOn
        ⟨by linarith [hu.1],hu.2.trans (s.q_le_one (by omega))⟩
        ⟨by linarith [s.q_nonneg (p := 2) (by omega)],s.q_le_one (by omega)⟩ hu.2
    have hdQ : HasDerivWithinAt (fun u=>Q (ξ.first u)) (R*ξ.second 0) (Icc 0 (s.q 2)) 0 := by
      have H := (show HasDerivWithinAt Q R (Icc 0 ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2))
          (ξ.first 0) by simpa only [ξ.first_zero] using hDQ).comp 0
        (ξ.hasDerivAt_first_unit (show (0:ℝ)∈Icc (-1:ℝ) 1 by norm_num)).hasDerivWithinAt hmap
      exact H
    have hd2 : HasDerivWithinAt (fun u=>ξ.second u*s.m 1/2*(u-Q (ξ.first u)))
        (c*(1-ξ.second 0*R)) (Icc 0 (s.q 2)) 0 := by
      have Hg := ((ξ.hasDerivAt_second_unit (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)).mul_const
        (s.m 1)).div_const 2
      convert! Hg.hasDerivWithinAt.mul ((hasDerivAt_id (0:ℝ)).hasDerivWithinAt.sub hdQ) using 1
      all_goals first | rfl | (simp only [Pi.sub_apply,id_eq,ξ.first_zero,hQ0,sub_self,mul_zero,zero_add]; dsimp only [c]; ring)
    obtain ⟨f,hfmin,hfd⟩ := exists_mixedZeroOverlap_comparator ξ s h hq hmin
    have H := oneSidedCurvature_nonneg_of_min hq2 hfmin hfd
      (show ξ.second 0*s.m 1/2*(0-Q (ξ.first 0))=0 by simp only [ξ.first_zero,hQ0,sub_self,mul_zero]) hd2
    have HB : 0 ≤ 1-ξ.second 0*R := (mul_nonneg_iff_of_pos_left hc).mp H
    rw [section4THessianSquare_initial_zero_eq_sq (mixedClockScheme ξ s) (mixedBeta ξ) h hqclock]
    change ξ.second 0*R ≤ 1
    linarith
  · have hz : ξ.second 0=0 := le_antisymm (le_of_not_gt hsec) (ξ.second_nonneg 0)
    rw [hz,zero_mul]
    norm_num

end FourPapersCommon
