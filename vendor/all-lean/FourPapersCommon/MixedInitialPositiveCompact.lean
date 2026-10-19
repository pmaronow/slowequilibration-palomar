module
public import FourPapersCommon.MixedNoninitialCompact
public import FourPapersCommon.MixedInitialLeft
public import FourPapersCommon.MixedZeroOverlapCurvature
public import FourPapersCommon.MixedZeroInitialReflection

@[expose] public section

/-! Actual first-level positive-overlap witnesses, including zero initial
overlap and a quadratic covariance term.  Boundary curvature is obtained
from the genuine same-depth competitor, not from a positive-gap estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
set_option maxHeartbeats 1400000

theorem mixed_initial_instability_data (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h ε : ℝ) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1) {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ e ≥ (0 : ℝ), e ≤ (1 - t₀) / 4 ∧
      ξ.second (s.q 1) * section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0 ≤ 1 + e := by
  by_cases hq : s.q 1 = 0
  · have hq2 : 0 < s.q 2 := by
      rcases hright with H | H
      · simpa only [hq] using H
      · simp only [hq] at H
        norm_num at H
    have H := mixed_initial_zero_curvature_bound ξ s h hq hm hq2 hmin
    refine ⟨0, le_rfl, ?_, ?_⟩
    · linarith
    · simpa only [hq, add_zero] using H
  · have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
      rw [← mixedMinimizer_value ξ h]
      exact isMixedMinimizer_selected ξ h _
    have hε : 0 ≤ ε := by linarith
    have hpow := Real.rpow_nonneg hε (1 / 6 : ℝ)
    let e := mixedInstabilityConstant ξ * ε ^ (1 / 6 : ℝ)
    have he : 0 ≤ e := mul_nonneg (mixedInstabilityConstant_nonneg ξ) hpow
    have HC := mul_le_mul_of_nonneg_right (mixedLocalLeftConstant_bounds ξ).2.2 hpow
    have hes : e ≤ (1 - t₀) / 4 := by dsimp [e]; nlinarith only [HC, hsmall]
    have H := mixed_instability_bound_all_levels ξ s h ε (r := 1) le_rfl (by omega)
      (by simpa only [Nat.sub_self] using hm)
      (by simpa only [Nat.sub_self, s.q_zero] using
        (lt_of_le_of_ne (s.q_nonneg (by omega : 1 ≤ k + 2)) (Ne.symm hq)))
      hright hmin hnear
    exact ⟨e, he, hes, by dsimp [e]; linarith only [H]⟩

theorem mixed_initial_Q_baseline (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h 1 (s.m 0) 0 = s.q 1 := by
  have hleft : s.q (1 - 1) < s.q 1 ∨ s.q 1 = 0 := by
    by_cases H : s.q 1 = 0
    · exact Or.inr H
    · exact Or.inl (by simpa only [Nat.sub_self, s.q_zero] using
        (lt_of_le_of_ne (s.q_nonneg (by omega : 1 ≤ k + 2)) (Ne.symm H)))
  simpa only [Nat.sub_self] using mixed_endpointQ_eq_overlap_of_min_all_levels ξ s h
    (r := 1) le_rfl (by omega) (by simpa only [Nat.sub_self] using hm) hleft hright hmin

theorem exists_mixedPressureWitness_initial_left
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : s.m 0 < s.m 1) (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (0 : ℝ) (s.q 1)) (hne : u ≠ s.q 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ w : MixedPressureWitness s 1, 0 < mixedPressureWitnessDeficit ξ s h 1 w (t, u) := by
  obtain ⟨e, he, hes, hR⟩ := mixed_initial_instability_data ξ s h ε hm hright ht₀ hmin hnear hsmall
  have hQ := mixed_initial_Q_baseline ξ s h hm hright hmin
  have HS := mixedLeftSlope_initial_ge_of_endpoint_curvature ξ s h ht ht₀ he hu hQ hR (by linarith)
  have hv := mixedLeftSplitVariance_mem ξ s (r := 1) (by omega)
    ⟨ht.1, ht.2.trans ht₀.le⟩ (by simpa only [Nat.sub_self, s.q_zero] using hu)
  obtain ⟨ell, H⟩ := section5V_baseline_lambda_gain_Q (mixedClockScheme ξ s) (mixedBeta ξ) h
    (r := 1) le_rfl (by omega) hv u
  simp only [mixedClockScheme_m] at H
  change _ ≤ 2 * parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h -
    (mixedLeftSlope ξ s h 1 t u) ^ 2 / 2 at H
  have Hpos : 0 < (1 - t₀) / 2 * (s.q 1 - u) := mul_pos
    (div_pos (sub_pos.mpr ht₀) (by norm_num)) (sub_pos.mpr (lt_of_le_of_ne hu.2 hne))
  have Hsq := div_pos (sq_pos_of_pos (Hpos.trans_le HS)) (by norm_num : (0 : ℝ) < 2)
  have hmass : s.m 0 ∈ Icc (s.m (1 - 1) / 2) (s.m 1) := by
    constructor
    · simp only [Nat.sub_self, s.m_zero]
      norm_num
    · exact hm.le
  let w : MixedPressureWitness s 1 := .left (s.m 0) u ell hmass
    (by simpa only [Nat.sub_self, s.q_zero] using hu)
  refine ⟨w, ?_⟩
  dsimp [w, mixedPressureWitnessDeficit]
  simp only [Nat.sub_self, sub_self, mul_zero, tangentRemainder_self, sub_zero]
  linarith

theorem mixedRightSlope_initial_le_local (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h ε : ℝ) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (s.q 1) (s.q 2))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : mixedLocalLeftConstant ξ * (u - s.q 1) ≤ 1 - t₀) :
    mixedRightSlope ξ s h 1 t u ≤ -(1 - t₀) / 2 * (u - s.q 1) := by
  obtain ⟨e, he, hes, hR⟩ := mixed_initial_instability_data ξ s h ε hm hright ht₀ hmin hnear hsmall
  have hQ : section4RightQ (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0 = s.q 1 := by
    rw [section4RightQ, sub_zero]
    have H := section4TVarianceQ_neighbor_full_eq_zero_all_levels (mixedClockScheme ξ s)
      (mixedBeta ξ) h (r := 1) le_rfl (by omega)
    simp only [mixedClockScheme_m, Nat.sub_self] at H
    simp only [mixedClockScheme_m]
    rw [H]
    exact mixed_initial_Q_baseline ξ s h hm hright hmin
  have hR' : ξ.second (s.q 1) * section4RightR (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0 ≤ 1 + e := by
    rw [section4RightR, sub_zero, section4THessianSquare_neighbor_full_eq_zero_all_levels
      (mixedClockScheme ξ s) (mixedBeta ξ) h (r := 1) le_rfl (by omega)]
    exact hR
  have hlocal' : mixedLocalSlopeConstant ξ * (u - s.q 1) ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right (mixedLocalLeftConstant_bounds ξ).2.1 (sub_nonneg.mpr hu.1)
    nlinarith only [H, hlocal]
  exact mixedRightSlope_le_local_of_endpoint_curvature ξ s h (r := 1) (by omega)
    ht ht₀ he hu hQ hR' hes hlocal'

theorem exists_mixedPressureWitness_initial_right_local
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : s.m 0 < s.m 1) (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (s.q 1) (s.q 2)) (hne : u ≠ s.q 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : mixedLocalLeftConstant ξ * (u - s.q 1) ≤ 1 - t₀) :
    ∃ w : MixedPressureWitness s 1, 0 < mixedPressureWitnessDeficit ξ s h 1 w (t, u) := by
  have HS := mixedRightSlope_initial_le_local ξ s h ε hm hright ht ht₀ hu hmin hnear hsmall hlocal
  have Hpos : 0 < (1 - t₀) / 2 * (u - s.q 1) := mul_pos
    (div_pos (sub_pos.mpr ht₀) (by norm_num)) (sub_pos.mpr (lt_of_le_of_ne hu.1 (Ne.symm hne)))
  have Hnegative : mixedRightSlope ξ s h 1 t u < 0 := by linarith only [HS, Hpos]
  have hv := mixedRightSplitVariance_mem ξ s (r := 1) (by omega) ⟨ht.1, ht.2.trans ht₀.le⟩ hu
  obtain ⟨ell, H⟩ := section5RightV_lambda_gain (mixedClockScheme ξ s) (mixedBeta ξ) h (r := 1) (by omega)
    (m := s.m 1) ⟨s.m_nonneg (by omega), (s.m_le_one (by omega)).trans (by norm_num)⟩
    (mixedRightSplitVariance ξ s 1 t u) u
  have HB := section5RightV_zero_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h (r := 1) (by omega) hv
  have HD := deriv_section5RightV_zero_eq_Q_all_levels (mixedClockScheme ξ s) (mixedBeta ξ) h (r := 1) (by omega) hv
  simp only [mixedClockScheme_m] at HB HD
  rw [HB, HD] at H
  change _ ≤ 2 * parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h -
    (mixedRightSlope ξ s h 1 t u) ^ 2 / 2 at H
  have ha := s.m_nonneg (p := 1) (by omega)
  let w : MixedPressureWitness s 1 := .right (s.m 1) u ell
    ⟨by simpa only [Nat.sub_self] using hm.le, by linarith⟩ hu
  refine ⟨w, ?_⟩
  have Hsq := div_pos (sq_pos_of_ne_zero Hnegative.ne) (by norm_num : (0 : ℝ) < 2)
  dsimp [w, mixedPressureWitnessDeficit]
  simp only [sub_self, mul_zero, tangentRemainder_self, sub_zero]
  linarith

theorem exists_mixedPressureWitness_initial_positive
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hne : u ≠ s.q 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : ∀ v ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      (1 - t₀) / mixedLocalLeftConstant ξ ≤ |v - q| →
      2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
        (1 - t₀) * ξ.tangentRemainder v q) :
    ∃ w : MixedPressureWitness s 1, 0 < mixedPressureWitnessDeficit ξ s h 1 w (t, u) := by
  have hm1 : s.m 0 < s.m 1 := hm (show (⟨0, by omega⟩ : Fin (k + 2)) < ⟨1, by omega⟩ by
    simp only [Fin.mk_lt_mk]; omega)
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.le⟩
  have hleft : s.q (1 - 1) < s.q 1 ∨ s.q 1 = 0 := by
    by_cases H : s.q 1 = 0
    · exact Or.inr H
    · exact Or.inl (by simpa only [Nat.sub_self, s.q_zero] using
        (lt_of_le_of_ne (s.q_nonneg (by omega : 1 ≤ k + 2)) (Ne.symm H)))
  by_cases htzero : t = 0
  · subst t
    obtain ⟨ell, H⟩ := exists_mixedSmallTime_scalar_gain ξ s h (r := 1) le_rfl (by omega)
      (by simpa only [Nat.sub_self] using hm1) hleft hright hmin u
    have hmass : s.m 0 ∈ Icc (s.m (1 - 1) / 2) (s.m 1) :=
      ⟨by simp [s.m_zero], hm1.le⟩
    let w : MixedPressureWitness s 1 := .left (s.m 0) (s.q 1) ell hmass
      ⟨by simpa only [Nat.sub_self, s.q_zero] using s.q_nonneg (by omega : 1 ≤ k + 2), le_rfl⟩
    refine ⟨w, ?_⟩
    have Hpos := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) (by norm_num : (0 : ℝ) < 2)
    dsimp [w, mixedPressureWitnessDeficit, mixedLeftSplitVariance]
    simp only [sub_self, zero_mul, add_zero, sub_zero]
    linarith
  by_cases huq : u ≤ s.q 1
  · exact exists_mixedPressureWitness_initial_left ξ s h ε hm1 hright ht ht₀
      ⟨hu.1, huq⟩ hne hmin hnear hsmall
  · have hqleu : s.q 1 ≤ u := (lt_of_not_ge huq).le
    by_cases hurnext : u ≤ s.q 2
    · have huI : u ∈ Icc (s.q 1) (s.q 2) := ⟨hqleu, hurnext⟩
      by_cases hlocal : mixedLocalLeftConstant ξ * (u - s.q 1) ≤ 1 - t₀
      · exact exists_mixedPressureWitness_initial_right_local ξ s h ε hm1 hright
          ht ht₀ huI hne hmin hnear hsmall hlocal
      · have hdist : (1 - t₀) / mixedLocalLeftConstant ξ ≤ |u - s.q 1| := by
          rw [abs_of_nonneg (sub_nonneg.mpr hqleu)]
          exact (div_le_iff₀ (mixedLocalLeftConstant_pos ξ)).mpr (by linarith)
        have Hfar := hfar u hu (s.q 1) ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩ hdist
        have Hsmall : 2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
            (1 - t) * ξ.tangentRemainder u (s.q 1) := Hfar.trans_le
          (mul_le_mul_of_nonneg_right (by linarith [ht.2])
            (ξ.tangentRemainder_nonneg ⟨by linarith [hu.1], hu.2⟩
              ⟨by linarith [s.q_nonneg (by omega : 1 ≤ k + 2)], s.q_le_one (by omega)⟩))
        obtain ⟨m, hmass, ell, H⟩ := exists_mixedRightComparison_witness_of_gap ξ s h ε
          (r := 1) le_rfl (by omega) (by simpa only [Nat.sub_self] using hm1)
          ht1 huI hmin hnear Hsmall
        refine ⟨.right m u ell hmass huI, ?_⟩
        rwa [mixedPressureWitnessDeficit_right_at_trial]
    · have hright' : s.q 1 < s.q 2 := by
        rcases hright with H | H
        · exact H
        · linarith [s.q_mono (p := 1) (by omega), hu.2]
      obtain ⟨j, hj0, hj, hv, H⟩ := exists_mixedInterleavedComparison_witness_outside_right ξ s h
        ⟨lt_of_le_of_ne ht.1 (Ne.symm htzero), ht.2.trans_lt ht₀⟩ (r := 1) le_rfl
        (by omega) hm hright' (lt_of_not_ge hurnext) hu.2
      exact ⟨.interleaved j u 0 hj0 hj hv, H⟩

theorem exists_mixed_initial_positive_away_gap
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : ∀ v ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      (1 - t₀) / mixedLocalLeftConstant ξ ≤ |v - q| →
      2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
        (1 - t₀) * ξ.tangentRemainder v q) :
    ∃ δ > (0 : ℝ), ∀ (Ω : Type u) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀ {n : ℕ}, 0 < n → ∀ sk : MixedDisorder (Ω := Ω) n ξ,
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q 1| →
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 1) t u ≤
        2 * mixedInterpolationPsi ξ s h t - δ := by
  let S : Set (ℝ × ℝ) := (Icc (0 : ℝ) t₀ ×ˢ Icc (0 : ℝ) 1) ∩
    {p | η ≤ |p.2 - s.q 1|}
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_snd.sub continuous_const).abs)
  have hpos : ∀ p ∈ S, ∃ w : MixedPressureWitness s 1,
      0 < mixedPressureWitnessDeficit ξ s h 1 w p := by
    intro p hp
    have hne : p.2 ≠ s.q 1 := by
      intro he
      have HH : η ≤ |p.2 - s.q 1| := hp.2
      simp only [he, sub_self, abs_zero] at HH
      exact (not_le_of_gt hη) HH
    exact exists_mixedPressureWitness_initial_positive ξ s h ε hm hright hp.1.1 ht₀ hp.1.2
      hne hmin hnear hsmall hfar
  obtain ⟨δ, hδ, Hδ⟩ := exists_mixed_constrainedPhi_compact_pressureWitness_gap ξ s h
    (r := 1) le_rfl (by omega) hS
    (fun _ hp => ⟨by linarith [hp.1.2.1], hp.1.2.2⟩)
    (fun _ hp => ⟨hp.1.1.1, hp.1.1.2.trans ht₀.le⟩) hpos
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ _ n hn sk t ht u hu hdist hatt
  simpa only [show k + 2 - 1 = k + 1 by omega] using
    Hδ Ω (t, u) ⟨⟨ht, hu⟩, hdist⟩ hn sk hatt

end FourPapersCommon
