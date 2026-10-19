module
public import FourPapersCommon.MixedAllLevelCompact
public import FourPapersCommon.MixedNearOptimalTolerance

@[expose] public section

/-! The actual signed constrained-pressure quadratic estimate for every
reduced near-minimizer of an arbitrary admissible even mixed model.  Its
constant is selected before the finite probability space or Hamiltonian. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
set_option maxHeartbeats 1000000

theorem exists_mixed_uniform_quadratic_bound_reduced
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (hm : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hq : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : ∀ v ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      (1 - t₀) / mixedLocalLeftConstant ξ ≤ |v - q| →
      2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
        (1 - t₀) * ξ.tangentRemainder v q) :
    ∃ K > (0 : ℝ), ∀ (Ω : Type u) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀ {n : ℕ}, 0 < n → ∀ sk : MixedDisorder (Ω := Ω) n ξ,
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ r, 1 ≤ r → r ≤ k + 1 →
      ∀ v ∈ Icc (-1 : ℝ) 1, (∃ σ τ : Config n, overlap n σ τ = v) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t v ≤
        2 * mixedInterpolationPsi ξ s h t - (v - s.q r) ^ 2 / K := by
  obtain ⟨η, hη, Hlocal⟩ := exists_mixed_uniform_local_radius ξ s h ε hm hq ht₀ hmin hnear hsmall
  have Hlevel : ∀ r, 1 ≤ r → r ≤ k + 1 → ∃ δ > (0 : ℝ),
      ∀ (Ω : Type u) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀ {n : ℕ}, 0 < n → ∀ sk : MixedDisorder (Ω := Ω) n ξ,
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ v ∈ Icc (-1 : ℝ) 1, η ≤ |v - s.q r| →
      (∃ σ τ : Config n, overlap n σ τ = v) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t v ≤
        2 * mixedInterpolationPsi ξ s h t - δ :=
    fun r hr0 hr => exists_mixed_signed_away_gap_reduced ξ s h ε hm hq hr0 hr ht₀ hη
      hmin hnear hsmall hfar
  let D : Finset ℕ := Finset.Icc 1 (k + 1)
  have hD : D.Nonempty := ⟨1, by simp [D]⟩
  let e : ℕ → ℝ := fun r => if hr : 1 ≤ r ∧ r ≤ k + 1 then
    Classical.choose (Hlevel r hr.1 hr.2) else 1
  let c := D.inf' hD e
  have hc : 0 < c := (Finset.lt_inf'_iff hD).mpr (by
    intro r hr
    have H := Finset.mem_Icc.mp (show r ∈ Finset.Icc 1 (k + 1) from hr)
    simpa [e, H.1, H.2] using (Classical.choose_spec (Hlevel r H.1 H.2)).1)
  let a : ℝ := (1 - t₀) ^ 2 / 8
  have ha : 0 < a := div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) (by norm_num)
  let K : ℝ := max (1 / a) (4 / c)
  have hKa : 1 / a ≤ K := le_max_left _ _
  have hKc : 4 / c ≤ K := le_max_right _ _
  have hK : 0 < K := lt_of_lt_of_le (div_pos zero_lt_one ha) hKa
  refine ⟨K, hK, ?_⟩
  intro Ω _ _ n hn sk t ht r hr0 hr v hv hatt
  by_cases hlocal : |v - s.q r| ≤ η
  · have H := Hlocal Ω hn sk t ht r hr0 hr v hv hlocal hatt
    have hdiv : 1 / K ≤ a := by
      have hprod : 1 ≤ K * a := (div_le_iff₀ ha).mp hKa
      exact (div_le_iff₀ hK).2 (by simpa only [one_mul, mul_comm] using hprod)
    have hquad : (v - s.q r) ^ 2 / K ≤ a * (v - s.q r) ^ 2 := by
      calc
        _ = (1 / K) * (v - s.q r) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)
    change _ ≤ 2 * mixedInterpolationPsi ξ s h t - a * (v - s.q r) ^ 2 at H
    linarith
  · have H := (Classical.choose_spec (Hlevel r hr0 hr)).2 Ω hn sk t ht v hv
        (le_of_not_ge hlocal) hatt
    have hce : c ≤ Classical.choose (Hlevel r hr0 hr) := by
      have Hc := Finset.inf'_le e (show r ∈ D by simp [D, hr0, hr])
      change D.inf' hD e ≤ _
      simpa only [e, dif_pos (show 1 ≤ r ∧ r ≤ k + 1 from ⟨hr0, hr⟩)] using Hc
    have hq0 := s.q_nonneg (p := r) (by omega : r ≤ k + 2)
    have hq1 := s.q_le_one (p := r) (by omega : r ≤ k + 2)
    have hdiff : |v - s.q r| ≤ 2 := abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hsq : (v - s.q r) ^ 2 ≤ 4 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (v - s.q r)]
    have hdiv : 4 / K ≤ c := by
      have hprod : 4 ≤ K * c := (div_le_iff₀ hc).mp hKc
      exact (div_le_iff₀ hK).2 (by simpa only [mul_comm] using hprod)
    have hquad := (div_le_div_of_nonneg_right hsq hK.le).trans hdiv
    linarith

theorem exists_mixed_uniform_quadratic_tolerance (ξ : AdmissibleEvenMixture)
    {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k) (h : ℝ),
      (∀ p, p ≤ k → s.m p < s.m (p + 1)) →
      (∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1)) →
      (∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
        mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) →
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε →
      ∃ K > (0 : ℝ), ∀ (Ω : Type u) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
        ∀ {n : ℕ}, 0 < n → ∀ sk : MixedDisorder (Ω := Ω) n ξ,
        ∀ t ∈ Icc (0 : ℝ) t₀, ∀ r, 1 ≤ r → r ≤ k + 1 →
        ∀ v ∈ Icc (-1 : ℝ) 1, (∃ σ τ : Config n, overlap n σ τ = v) →
        constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t v ≤
          2 * mixedInterpolationPsi ξ s h t - (v - s.q r) ^ 2 / K := by
  obtain ⟨ε, hε, _, hsmall, hfar⟩ := exists_mixed_nearOptimal_tolerance ξ ht₀
  exact ⟨ε, hε, fun s h hm hq hmin hnear =>
    exists_mixed_uniform_quadratic_bound_reduced ξ s h ε hm hq ht₀ hmin hnear hsmall hfar⟩

end FourPapersCommon
