module
public import FourPapersCommon.MixedPressureWitness
public import FourPapersCommon.MixedSmallTimeGain

@[expose] public section

/-! Closed compact signed-overlap deficits at every noninitial physical
level.  Local/far neighbors and fixed-trial interleaved comparisons are
combined through one continuous scalar witness family. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1400000
universe u

theorem exists_mixedPressureWitness_left_local
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) (hne : u ≠ s.q r)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : mixedLocalLeftConstant ξ * (s.q r - u) ≤ 1 - t₀) :
    ∃ w : MixedPressureWitness s r, 0 < mixedPressureWitnessDeficit ξ s h r w (t, u) := by
  obtain ⟨ell, H⟩ := exists_mixedLeft_lambda_local_gain ξ s h ε hr0 hr hm hleft hright
    ht ht₀ hu hmin hnear hsmall hlocal
  have ha := s.m_nonneg (p := r - 1) (by omega)
  let w : MixedPressureWitness s r := .left (s.m (r - 1)) u ell ⟨by linarith, hm.le⟩ hu
  refine ⟨w, ?_⟩
  have Hpos : 0 < (1 - t₀) ^ 2 / 8 * (u - s.q r) ^ 2 :=
    mul_pos (div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) (by norm_num))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
  dsimp [w, mixedPressureWitnessDeficit]
  simp only [sub_self, mul_zero, tangentRemainder_self, sub_zero]
  linarith

theorem exists_mixedPressureWitness_right_local
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (s.q r) (s.q (r + 1))) (hne : u ≠ s.q r)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : mixedLocalLeftConstant ξ * (u - s.q r) ≤ 1 - t₀) :
    ∃ w : MixedPressureWitness s r, 0 < mixedPressureWitnessDeficit ξ s h r w (t, u) := by
  have HS := mixedRightSlope_le_local_of_near_minimum ξ s h ε hr0 hr hm hleft hright
    ht ht₀ hu hmin hnear hsmall hlocal
  have hdiff : 0 < u - s.q r := sub_pos.mpr (lt_of_le_of_ne hu.1 (Ne.symm hne))
  have Hnegative : mixedRightSlope ξ s h r t u < 0 := by
    have Hpos := mul_pos (div_pos (sub_pos.mpr ht₀) (by norm_num : (0 : ℝ) < 2)) hdiff
    linarith only [HS, Hpos]
  have ha := s.m_nonneg hr
  have hv := mixedRightSplitVariance_mem ξ s hr ⟨ht.1, ht.2.trans ht₀.le⟩ hu
  obtain ⟨ell, H⟩ := section5RightV_lambda_gain (mixedClockScheme ξ s) (mixedBeta ξ) h hr
    (m := s.m r) ⟨ha, (s.m_le_one hr).trans (by norm_num)⟩ (mixedRightSplitVariance ξ s r t u) u
  have HB := section5RightV_zero_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv
  have HD := deriv_section5RightV_zero_eq_Q_all_levels (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv
  simp only [mixedClockScheme_m] at HB HD
  rw [HB, HD] at H
  change _ ≤ 2 * parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h -
    (mixedRightSlope ξ s h r t u) ^ 2 / 2 at H
  let w : MixedPressureWitness s r := .right (s.m r) u ell ⟨hm.le, by linarith⟩ hu
  refine ⟨w, ?_⟩
  have Hpos := div_pos (sq_pos_of_ne_zero Hnegative.ne) (by norm_num : (0 : ℝ) < 2)
  dsimp [w, mixedPressureWitnessDeficit]
  simp only [sub_self, mul_zero, tangentRemainder_self, sub_zero]
  linarith

theorem exists_mixedPressureWitness_noninitial
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    {r : ℕ} (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hq12 : s.q 1 < s.q 2) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hne : u ≠ s.q r)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : ∀ v ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      (1 - t₀) / mixedLocalLeftConstant ξ ≤ |v - q| →
      2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
        (1 - t₀) * ξ.tangentRemainder v q) :
    ∃ w : MixedPressureWitness s r, 0 < mixedPressureWitnessDeficit ξ s h r w (t, u) := by
  have hr1 : 1 ≤ r := by omega
  have hgap : s.m (r - 1) < s.m r :=
    hm (show (⟨r - 1, by omega⟩ : Fin (k + 2)) < ⟨r, by omega⟩ by
      simp only [Fin.mk_lt_mk]; omega)
  have hmpos : 0 < s.m (r - 1) := by
    have H := hm (show (⟨0, by omega⟩ : Fin (k + 2)) < ⟨r - 1, by omega⟩ by
      simp only [Fin.mk_lt_mk]; omega)
    simpa only [s.m_zero] using H
  have hm1 : 0 < s.m 1 := by
    have H := hm (show (⟨0, by omega⟩ : Fin (k + 2)) < ⟨1, by omega⟩ by
      simp only [Fin.mk_lt_mk]; omega)
    simpa only [s.m_zero] using H
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.le⟩
  have hqr : s.q r ∈ Icc (0 : ℝ) 1 := ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  have Hfar {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
      (hdist : (1 - t₀) / mixedLocalLeftConstant ξ ≤ |v - s.q r|) :
      2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
        (1 - t) * ξ.tangentRemainder v (s.q r) :=
    (hfar v hv (s.q r) hqr hdist).trans_le (mul_le_mul_of_nonneg_right
      (by linarith [ht.2]) (ξ.tangentRemainder_nonneg ⟨by linarith [hv.1], hv.2⟩
        ⟨by linarith [hqr.1], hqr.2⟩))
  by_cases htzero : t = 0
  · subst t
    obtain ⟨ell, H⟩ := exists_mixedSmallTime_scalar_gain ξ s h hr1 hr hgap (Or.inl hleft) hright hmin u
    have hma : s.m (r - 1) ∈ Icc (s.m (r - 1) / 2) (s.m r) := ⟨by linarith, hgap.le⟩
    let w : MixedPressureWitness s r := .left (s.m (r - 1)) (s.q r) ell hma
      ⟨hleft.le, le_rfl⟩
    refine ⟨w, ?_⟩
    have Hpos := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) (by norm_num : (0 : ℝ) < 2)
    dsimp [w, mixedPressureWitnessDeficit, mixedLeftSplitVariance]
    simp only [sub_self, zero_mul, add_zero, sub_zero]
    linarith
  have htopen : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm htzero), ht.2.trans_lt ht₀⟩
  by_cases huneg : u < 0
  · obtain ⟨j, hj0, hj, hv, H⟩ := exists_mixedInterleavedComparison_witness_negative ξ s h
      htopen hr0 hr hm1 hq12 huneg (abs_le.mpr hu)
    exact ⟨.interleaved j u 0 hj0 hj hv, H⟩
  have hu0 : 0 ≤ u := le_of_not_gt huneg
  have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hu0, hu.2⟩
  by_cases houtleft : u < s.q (r - 1)
  · obtain ⟨j, hj0, hj, hv, H⟩ := exists_mixedInterleavedComparison_witness_outside_left ξ s h
      htopen hr1 hr hm hleft hu0 houtleft
    exact ⟨.interleavedBase j u 0 hj0 hj hv, H⟩
  have huprev : s.q (r - 1) ≤ u := le_of_not_gt houtleft
  by_cases huq : u ≤ s.q r
  · have huI : u ∈ Icc (s.q (r - 1)) (s.q r) := ⟨huprev, huq⟩
    by_cases hlocal : mixedLocalLeftConstant ξ * (s.q r - u) ≤ 1 - t₀
    · exact exists_mixedPressureWitness_left_local ξ s h ε hr1 hr hgap hleft hright
        ht ht₀ huI hne hmin hnear hsmall hlocal
    · have hdist : (1 - t₀) / mixedLocalLeftConstant ξ ≤ |u - s.q r| := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr huq)]
        exact (div_le_iff₀ (mixedLocalLeftConstant_pos ξ)).mpr (by linarith)
      obtain ⟨m, hmass, ell, H⟩ := exists_mixedLeftComparison_witness_of_gap ξ s h ε
        hr1 hr hmpos hgap ht1 huI hmin hnear (Hfar hu01 hdist)
      refine ⟨.left m u ell hmass huI, ?_⟩
      rwa [mixedPressureWitnessDeficit_left_at_trial]
  · have hqleu : s.q r ≤ u := (lt_of_not_ge huq).le
    by_cases hurnext : u ≤ s.q (r + 1)
    · have huI : u ∈ Icc (s.q r) (s.q (r + 1)) := ⟨hqleu, hurnext⟩
      by_cases hlocal : mixedLocalLeftConstant ξ * (u - s.q r) ≤ 1 - t₀
      · exact exists_mixedPressureWitness_right_local ξ s h ε hr1 hr hgap hleft hright
          ht ht₀ huI hne hmin hnear hsmall hlocal
      · have hdist : (1 - t₀) / mixedLocalLeftConstant ξ ≤ |u - s.q r| := by
          rw [abs_of_nonneg (sub_nonneg.mpr hqleu)]
          exact (div_le_iff₀ (mixedLocalLeftConstant_pos ξ)).mpr (by linarith)
        obtain ⟨m, hmass, ell, H⟩ := exists_mixedRightComparison_witness_of_gap ξ s h ε
          hr1 hr hgap ht1 huI hmin hnear (Hfar hu01 hdist)
        refine ⟨.right m u ell hmass huI, ?_⟩
        rwa [mixedPressureWitnessDeficit_right_at_trial]
    · have hright' : s.q r < s.q (r + 1) := by
        rcases hright with HH | HH
        · exact HH
        · have Hmono := s.q_mono r hr
          linarith [hu.2]
      obtain ⟨j, hj0, hj, hv, H⟩ := exists_mixedInterleavedComparison_witness_outside_right ξ s h
        htopen hr1 hr hm hright' (lt_of_not_ge hurnext) hu.2
      exact ⟨.interleaved j u 0 hj0 hj hv, H⟩

theorem exists_mixed_noninitial_signed_away_gap
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    {r : ℕ} (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hq12 : s.q 1 < s.q 2) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
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
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1, η ≤ |u - s.q r| →
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
        2 * mixedInterpolationPsi ξ s h t - δ := by
  let S : Set (ℝ × ℝ) := (Icc (0 : ℝ) t₀ ×ˢ Icc (-1 : ℝ) 1) ∩
    {p | η ≤ |p.2 - s.q r|}
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_snd.sub continuous_const).abs)
  have hpos : ∀ p ∈ S, ∃ w : MixedPressureWitness s r,
      0 < mixedPressureWitnessDeficit ξ s h r w p := by
    intro p hp
    have hne : p.2 ≠ s.q r := by
      intro he
      have HH : η ≤ |p.2 - s.q r| := hp.2
      simp only [he, sub_self, abs_zero] at HH
      exact (not_le_of_gt hη) HH
    exact exists_mixedPressureWitness_noninitial ξ s h ε hr0 hr hm hq12 hleft hright
      hp.1.1 ht₀ hp.1.2 hne hmin hnear hsmall hfar
  obtain ⟨δ, hδ, Hδ⟩ := exists_mixed_constrainedPhi_compact_pressureWitness_gap ξ s h
    (by omega) hr hS (fun _ hp => hp.1.2)
    (fun _ hp => ⟨hp.1.1.1, hp.1.1.2.trans ht₀.le⟩) hpos
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ _ n hn sk t ht u hu hdist hatt
  exact Hδ Ω (t, u) ⟨⟨ht, hu⟩, hdist⟩ hn sk hatt

theorem exists_mixed_noninitial_signed_gap_tolerance (ξ : AdmissibleEvenMixture)
    {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k) (h : ℝ) {r : ℕ},
      2 ≤ r → r ≤ k + 1 → StrictMono (fun p : Fin (k + 2) => s.m p) →
      s.q 1 < s.q 2 → s.q (r - 1) < s.q r →
      (s.q r < s.q (r + 1) ∨ s.q r = 1) →
      (∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
        mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) →
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε →
      ∀ η > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (Ω : Type u) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀ {n : ℕ}, 0 < n → ∀ sk : MixedDisorder (Ω := Ω) n ξ,
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1, η ≤ |u - s.q r| →
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
        2 * mixedInterpolationPsi ξ s h t - δ := by
  obtain ⟨ε, hε, _, hsmall, hfar⟩ := exists_mixed_nearOptimal_tolerance ξ ht₀
  refine ⟨ε, hε, ?_⟩
  intro k s h r hr0 hr hm hq12 hleft hright hmin hnear η hη
  exact exists_mixed_noninitial_signed_away_gap ξ s h ε hr0 hr hm hq12 hleft hright
    ht₀ hη hmin hnear hsmall hfar

end FourPapersCommon
