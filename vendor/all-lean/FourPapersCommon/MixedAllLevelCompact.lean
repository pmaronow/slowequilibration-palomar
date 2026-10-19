module
public import FourPapersCommon.MixedUniformLocalRadius
public import FourPapersCommon.MixedInitialNegativeCompact

@[expose] public section

/-! Genuine uniform signed away-from-level margins for every reduced mixed
near-minimizer.  The zero initial overlap is reflected only after actual
minimality has forced the field to vanish. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
set_option maxHeartbeats 1000000

theorem exists_mixed_initial_signed_away_gap
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
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ v ∈ Icc (-1 : ℝ) 1, η ≤ |v - s.q 1| →
      (∃ σ τ : Config n, overlap n σ τ = v) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 1) t v ≤
        2 * mixedInterpolationPsi ξ s h t - δ := by
  obtain ⟨δp, hδp, Hp⟩ := exists_mixed_initial_positive_away_gap ξ s h ε hm hright
    ht₀ hη hmin hnear hsmall hfar
  have hm1 : s.m 0 < s.m 1 := hm
    (show (⟨0, by omega⟩ : Fin (k + 2)) < ⟨1, by omega⟩ by simp only [Fin.mk_lt_mk]; omega)
  by_cases hqzero : s.q 1 = 0
  · have hq2 : 0 < s.q 2 := by
      rcases hright with H | H
      · simpa only [hqzero] using H
      · rw [hqzero] at H
        norm_num at H
    refine ⟨δp, hδp, ?_⟩
    intro Ω _ _ n hn sk t ht v hv hdist hatt
    by_cases hv0 : 0 ≤ v
    · exact Hp Ω hn sk t ht v ⟨hv0, hv.2⟩ hdist hatt
    · have H := Hp Ω hn sk t ht (-v)
        ⟨neg_nonneg.mpr (le_of_not_ge hv0), by linarith [hv.1]⟩
        (by simpa only [hqzero, sub_zero, abs_neg] using hdist) (attainableOverlap_neg hatt)
      rw [mixedConstrainedPhi_initial_zero_reflection_of_min ξ s h sk hqzero hm1 hq2 hmin t v]
      exact H
  · have hqpos := lt_of_le_of_ne (s.q_nonneg (by omega : 1 ≤ k + 2)) (Ne.symm hqzero)
    obtain ⟨δn, hδn, Hn⟩ := exists_mixed_initial_negative_gap ξ s h ε hm1 hqpos hright
      ht₀ hmin hnear hsmall
    refine ⟨min δp δn, lt_min hδp hδn, ?_⟩
    intro Ω _ _ n hn sk t ht v hv hdist hatt
    by_cases hv0 : 0 ≤ v
    · exact (Hp Ω hn sk t ht v ⟨hv0, hv.2⟩ hdist hatt).trans
        (by linarith [min_le_left δp δn])
    · exact (Hn Ω hn sk t ht v ⟨hv.1, (lt_of_not_ge hv0).le⟩ hatt).trans
        (by linarith [min_le_right δp δn])

theorem mixed_strictMass_fin {k : ℕ} (s : RSBScheme k)
    (hm : ∀ p, p ≤ k → s.m p < s.m (p + 1)) :
    StrictMono (fun p : Fin (k + 2) => s.m p) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro p
  exact hm p (by have H := p.isLt; omega)

theorem exists_mixed_signed_away_gap_reduced
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hq : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
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
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ v ∈ Icc (-1 : ℝ) 1, η ≤ |v - s.q r| →
      (∃ σ τ : Config n, overlap n σ τ = v) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t v ≤
        2 * mixedInterpolationPsi ξ s h t - δ := by
  have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 := by
    by_cases H : r ≤ k
    · exact Or.inl (hq r hr0 H)
    · have he : r = k + 1 := by omega
      subst r
      rw [show k + 1 + 1 = k + 2 by omega, s.q_top]
      exact lt_or_eq_of_le (s.q_le_one (by omega))
  by_cases he : r = 1
  · subst r
    simpa only [show k + 2 - 1 = k + 1 by omega] using
      exists_mixed_initial_signed_away_gap ξ s h ε (mixed_strictMass_fin s hm) hright
        ht₀ hη hmin hnear hsmall hfar
  · exact exists_mixed_noninitial_signed_away_gap ξ s h ε (by omega) hr
      (mixed_strictMass_fin s hm) (hq 1 le_rfl (by omega))
      (by simpa only [Nat.sub_add_cancel hr0] using hq (r - 1) (by omega) (by omega))
      hright ht₀ hη hmin hnear hsmall hfar

end FourPapersCommon
