module
public import FourPapersCommon.MixedSignedInitialCompact
public import FourPapersCommon.MixedSignedInitialTube
public import FourPapersCommon.MixedInterleavedCompactGaps
public import FourPapersCommon.MixedSmallTimeGain

@[expose] public section

/-! A common actual pressure deficit on the entire negative physical
overlap interval at the first level.  The origin, signed first breakpoint,
terminal trial and zero interpolation time are included. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
set_option maxHeartbeats 1400000

theorem exists_mixed_initial_negative_gap
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : s.m 0 < s.m 1) (hq1 : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
        mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ δ > (0 : ℝ), ∀ (Ω : Type u) [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)], ∀ {n : ℕ}, 0 < n →
      ∀ sk : MixedDisorder (Ω := Ω) n ξ,
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ v ∈ Icc (-1 : ℝ) 0,
      (∃ σ τ : Config n, overlap n σ τ = v) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 1) t v ≤
        2 * mixedInterpolationPsi ξ s h t - δ := by
  obtain ⟨δi, hi, Hi⟩ := exists_mixed_constrainedPhi_compact_negative_initial_interval_gap
    ξ s h ε hm hq1 hright ht₀
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (0 : ℝ) t₀ ×ˢ Icc (-s.q 1) 0))
    (fun _ hp => hp.1) (fun _ hp => hp.2) hmin hnear hsmall
  by_cases hqtop : s.q 1 = 1
  · refine ⟨δi, hi, ?_⟩
    intro Ω _ _ n hn sk t ht v hv hatt
    exact Hi (t, v) ⟨ht, by simpa only [hqtop] using hv⟩ hn sk hatt
  have hq12 : s.q 1 < s.q 2 := hright.resolve_right hqtop
  obtain ⟨ρ, hρ, δb, hb, Hb⟩ := exists_mixed_constrainedPhi_signed_initial_breakpoint_tube
    ξ s h ε hm hq1 hright ht₀ hmin hnear hsmall
  have hm1 : 0 < s.m 1 := by simpa only [s.m_zero] using hm
  have hτ : 0 < mixedSmallTime ξ / 2 := div_pos (mixedSmallTime_pos ξ) (by norm_num)
  obtain ⟨δf, hf, Hf⟩ := exists_mixed_constrainedPhi_compact_negative_first_beyond_gap_all_spaces
    ξ s h hm1 hq1 hq12
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (mixedSmallTime ξ / 2) t₀ ×ˢ Icc (-1 : ℝ) (-s.q 1 - ρ / 2)))
    (by
      intro p hp
      exact ⟨hτ.trans_le hp.1.1, hp.1.2.trans_lt ht₀⟩)
    (by
      intro p hp
      exact ⟨hp.2.1, by linarith [hp.2.2]⟩)
    (by
      intro p hp
      have hpneg : p.2 < 0 := by linarith [hp.2.2]
      rw [abs_of_neg hpneg]
      linarith [hp.2.2])
  let D : ℝ := (s.q 1) ^ 2 / 4
  have hD : 0 < D := div_pos (sq_pos_of_pos hq1) (by norm_num)
  let δ := min δi (min δb (min δf D))
  have hδ : 0 < δ := lt_min hi (lt_min hb (lt_min hf hD))
  have hδi : δ ≤ δi := min_le_left _ _
  have hδb : δ ≤ δb := (min_le_right _ _).trans (min_le_left _ _)
  have hδf : δ ≤ δf := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδD : δ ≤ D := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ _ n hn sk t ht v hv hatt
  by_cases hins : -s.q 1 ≤ v
  · have H := Hi (t, v) ⟨ht, ⟨hins, hv.2⟩⟩ hn sk hatt
    linarith only [H, hδi]
  by_cases htime : t ≤ mixedSmallTime ξ
  · obtain ⟨σ, τ, hστ⟩ := hatt
    letI : Nonempty (AT.ConstrainedPair n v) := ⟨⟨(σ, τ), hστ⟩⟩
    have H := mixed_constrainedPhi_small_time_signed_gain hn ξ s h sk (r := 1)
      le_rfl (by omega) (by simpa only [Nat.sub_self] using hm)
      (Or.inl (by simpa only [Nat.sub_self, s.q_zero] using hq1)) hright hmin
      ⟨ht.1, htime⟩ ⟨hv.1, hv.2.trans zero_le_one⟩
    simp only [show k + 2 - 1 = k + 1 by omega] at H
    have Hsq : (s.q 1) ^ 2 ≤ (v - s.q 1) ^ 2 := by nlinarith only [hq1.le, hv.2]
    dsimp [D] at hδD
    linarith only [H, Hsq, hδD]
  by_cases htube : |v - (-s.q 1)| ≤ ρ
  · have H := Hb t ht v hv htube hn sk hatt
    linarith only [H, hδb]
  have hbelow : v < -s.q 1 := lt_of_not_ge hins
  have Habs : |v - (-s.q 1)| = -v - s.q 1 := by
    rw [abs_of_neg (by linarith only [hbelow])]
    ring
  have hvfar : v ≤ -s.q 1 - ρ / 2 := by
    have H := lt_of_not_ge htube
    rw [Habs] at H
    linarith only [H, hρ]
  have htfar : mixedSmallTime ξ / 2 ≤ t := by
    have H := lt_of_not_ge htime
    linarith only [H, (mixedSmallTime_pos ξ).le]
  have H := Hf (t, v) ⟨⟨htfar, ht.2⟩, ⟨hv.1, hvfar⟩⟩ hn sk hatt
  linarith only [H, hδf]

end FourPapersCommon
