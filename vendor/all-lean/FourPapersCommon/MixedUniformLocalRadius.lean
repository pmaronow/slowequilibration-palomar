module
public import FourPapersCommon.MixedInitialPositiveCompact
public import FourPapersCommon.MixedLocalRadius

@[expose] public section

/-! One model-independent physical local radius for every level of a
genuinely reduced mixed near-minimizer, including the zero first overlap. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
set_option maxHeartbeats 1200000

theorem mixed_constrainedPhi_initial_right_local
    {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (s.q 1) (s.q 2)) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : mixedLocalLeftConstant ξ * (u - s.q 1) ≤ 1 - t₀) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 1) t u ≤
      2 * mixedInterpolationPsi ξ s h t - (1 - t₀) ^ 2 / 8 * (u - s.q 1) ^ 2 := by
  have HS := mixedRightSlope_initial_le_local ξ s h ε hm hright ht ht₀ hu hmin hnear hsmall hlocal
  have H := mixed_constrainedPhi_le_two_Psi_sub_right_factor_sq hn ξ s h sk
    (r := 1) le_rfl (by omega) ⟨ht.1, ht.2.trans ht₀.le⟩ hu
  have HD := deriv_section5RightV_zero_eq_Q_all_levels (mixedClockScheme ξ s) (mixedBeta ξ) h
    (r := 1) (by omega) (mixedRightSplitVariance_mem ξ s (r := 1) (by omega)
      ⟨ht.1, ht.2.trans ht₀.le⟩ hu)
  simp only [mixedClockScheme_m] at HD
  rw [HD] at H
  change _ ≤ 2 * mixedInterpolationPsi ξ s h t - (mixedRightSlope ξ s h 1 t u) ^ 2 / 2 at H
  have HN : 0 ≤ (1 - t₀) / 2 * (u - s.q 1) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num)) (sub_nonneg.mpr hu.1)
  have Hneg : (1 - t₀) / 2 * (u - s.q 1) ≤ -mixedRightSlope ξ s h 1 t u := by linarith only [HS]
  have HQ := mul_self_le_mul_self HN Hneg
  rw [show k + 2 - 1 = k + 1 by omega] at H
  nlinarith only [H, HQ]

theorem exists_mixed_initial_zero_local_radius
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hq : s.q 1 = 0) (hm : s.m 0 < s.m 1) (hq2 : 0 < s.q 2)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ η > (0 : ℝ), ∀ (Ω : Type u) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀ {n : ℕ}, 0 < n → ∀ sk : MixedDisorder (Ω := Ω) n ξ,
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1, |u - s.q 1| ≤ η →
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 1) t u ≤
        2 * mixedInterpolationPsi ξ s h t - (1 - t₀) ^ 2 / 8 * (u - s.q 1) ^ 2 := by
  let η := min ((1 - t₀) / mixedLocalLeftConstant ξ) (s.q 2)
  have hη : 0 < η := lt_min (div_pos (sub_pos.mpr ht₀) (mixedLocalLeftConstant_pos ξ)) hq2
  have HηC : mixedLocalLeftConstant ξ * η ≤ 1 - t₀ := by
    have H := (le_div_iff₀ (mixedLocalLeftConstant_pos ξ)).mp (min_le_left _ _ : η ≤ _)
    simpa only [mul_comm] using H
  have Hηq : η ≤ s.q 2 := min_le_right _ _
  refine ⟨η, hη, ?_⟩
  intro Ω _ _ n hn sk t ht u hu hdist hatt
  have Hpos {v : ℝ} (hv : 0 ≤ v) (hvdist : v ≤ η)
      (hvatt : ∃ σ τ : Config n, overlap n σ τ = v) :
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 1) t v ≤
        2 * mixedInterpolationPsi ξ s h t - (1 - t₀) ^ 2 / 8 * v ^ 2 := by
    obtain ⟨σ, τ, hστ⟩ := hvatt
    letI : Nonempty (AT.ConstrainedPair n v) := ⟨⟨(σ, τ), hστ⟩⟩
    have H := mixed_constrainedPhi_initial_right_local hn ξ s h ε sk hm
      (Or.inl (by simpa only [hq] using hq2)) ht ht₀
      ⟨by simpa only [hq] using hv, hvdist.trans Hηq⟩ hmin hnear hsmall
      (by rw [hq, sub_zero]; exact (mul_le_mul_of_nonneg_left hvdist
        (mixedLocalLeftConstant_pos ξ).le).trans HηC)
    simpa only [hq, sub_zero] using H
  rw [hq, sub_zero] at hdist ⊢
  by_cases hu0 : 0 ≤ u
  · exact Hpos hu0 ((le_abs_self u).trans hdist) hatt
  · have H := Hpos (neg_nonneg.mpr (le_of_not_ge hu0))
      (by rw [abs_of_neg (lt_of_not_ge hu0)] at hdist; exact hdist)
      (attainableOverlap_neg hatt)
    rw [mixedConstrainedPhi_initial_zero_reflection_of_min ξ s h sk hq hm hq2 hmin t u]
    simpa only [neg_sq] using H

theorem exists_mixed_uniform_local_radius
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hq : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ η > (0 : ℝ), ∀ (Ω : Type u) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀ {n : ℕ}, 0 < n → ∀ sk : MixedDisorder (Ω := Ω) n ξ,
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ r, 1 ≤ r → r ≤ k + 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1, |u - s.q r| ≤ η →
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
        2 * mixedInterpolationPsi ξ s h t - (1 - t₀) ^ 2 / 8 * (u - s.q r) ^ 2 := by
  have Hlevel : ∀ r, 1 ≤ r → r ≤ k + 1 → ∃ η > (0 : ℝ),
      ∀ (Ω : Type u) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀ {n : ℕ}, 0 < n → ∀ sk : MixedDisorder (Ω := Ω) n ξ,
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1, |u - s.q r| ≤ η →
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
        2 * mixedInterpolationPsi ξ s h t - (1 - t₀) ^ 2 / 8 * (u - s.q r) ^ 2 := by
    intro r hr0 hr
    have hmass : s.m (r - 1) < s.m r := by
      have H := hm (r - 1) (by omega)
      simpa only [Nat.sub_add_cancel hr0] using H
    have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 := by
      by_cases H : r ≤ k
      · exact Or.inl (hq r hr0 H)
      · have he : r = k + 1 := by omega
        subst r
        rw [show k + 1 + 1 = k + 2 by omega, s.q_top]
        exact lt_or_eq_of_le (s.q_le_one (by omega))
    by_cases hrone : r = 1
    · subst r
      by_cases hq0 : s.q 1 = 0
      · have hq2 : 0 < s.q 2 := by
          rcases hright with H | H
          · simpa only [hq0] using H
          · rw [hq0] at H
            norm_num at H
        obtain ⟨η, hη, Hη⟩ := exists_mixed_initial_zero_local_radius ξ s h ε hq0
          (by simpa only [Nat.sub_self] using hmass) hq2 ht₀ hmin hnear hsmall
        exact ⟨η, hη, by simpa only [show k + 2 - 1 = k + 1 by omega] using Hη⟩
      · have hleft : s.q (1 - 1) < s.q 1 := by
          simpa only [Nat.sub_self, s.q_zero] using
            (lt_of_le_of_ne (s.q_nonneg (by omega : 1 ≤ k + 2)) (Ne.symm hq0))
        obtain ⟨η, hη, Hη⟩ := exists_mixed_positive_level_local_radius ξ s h ε le_rfl (by omega)
          hmass hleft hright hmin hnear ht₀ hsmall
        refine ⟨η, hη, ?_⟩
        intro Ω _ _ n hn sk t ht u hu hdist hatt
        obtain ⟨σ, τ, hστ⟩ := hatt
        exact Hη Ω hn sk t ht u hu hdist ⟨⟨(σ, τ), hστ⟩⟩
    · have hleft : s.q (r - 1) < s.q r := by
        simpa only [Nat.sub_add_cancel hr0] using hq (r - 1) (by omega) (by omega)
      obtain ⟨η, hη, Hη⟩ := exists_mixed_positive_level_local_radius ξ s h ε hr0 hr
        hmass hleft hright hmin hnear ht₀ hsmall
      refine ⟨η, hη, ?_⟩
      intro Ω _ _ n hn sk t ht u hu hdist hatt
      obtain ⟨σ, τ, hστ⟩ := hatt
      exact Hη Ω hn sk t ht u hu hdist ⟨⟨(σ, τ), hστ⟩⟩
  let D : Finset ℕ := Finset.Icc 1 (k + 1)
  have hD : D.Nonempty := ⟨1, by simp [D]⟩
  let e : ℕ → ℝ := fun r => if hr : 1 ≤ r ∧ r ≤ k + 1 then
    Classical.choose (Hlevel r hr.1 hr.2) else 1
  let η := D.inf' hD e
  have hη : 0 < η := (Finset.lt_inf'_iff hD).mpr (by
    intro r hr
    have H := Finset.mem_Icc.mp (show r ∈ Finset.Icc 1 (k + 1) from hr)
    simpa [e, H.1, H.2] using (Classical.choose_spec (Hlevel r H.1 H.2)).1)
  refine ⟨η, hη, ?_⟩
  intro Ω _ _ n hn sk t ht r hr0 hr u hu hdist hatt
  have Hηe : η ≤ e r := Finset.inf'_le e (by simp [D, hr0, hr])
  have Hdist : |u - s.q r| ≤ Classical.choose (Hlevel r hr0 hr) := by
    simpa [e, hr0, hr] using hdist.trans Hηe
  exact (Classical.choose_spec (Hlevel r hr0 hr)).2 Ω hn sk t ht u hu Hdist hatt

end FourPapersCommon
