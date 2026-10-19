module
public import FourPapersCommon.MixedRightScalarComparison
public import FourPapersCommon.MixedLocalRightUniform
public import FourPapersCommon.MixedNearOptimalTolerance

@[expose] public section

/-! Compact physical-right pressure margins selected before all finite
Gaussian models, including terminal-level right scalar recursions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 800000
universe u

theorem mixed_constrainedPhi_le_rightComparison
    {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {m t u : ℝ} (hm : m ∈ Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] (ℓ : ℝ) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      mixedRightComparison ξ s h r m ℓ (t, u) := by
  have H := mixedRight_constrainedPhi_le hn ξ s h sk (u := u) (v := u) hr0 hr hm ht hu ℓ
  simpa only [mixedRightComparison, AdmissibleEvenMixture.tangentRemainder,
    sub_self, mul_zero, sub_zero, add_zero] using H

theorem exists_mixed_constrainedPhi_compact_right_gap_all_spaces
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hgap : s.m (r - 1) < s.m r)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S) (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) 1)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q r) (s.q (r + 1)))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : ∀ z ∈ S, 2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
      (1 - z.1) * ξ.tangentRemainder z.2 (s.q r)) :
    ∃ δ > (0 : ℝ), ∀ (Ω : Type u) [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)], ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : MixedDisorder (Ω := Ω) n ξ, Nonempty (AT.ConstrainedPair n z.2) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * mixedInterpolationPsi ξ s h z.1 - δ := by
  obtain ⟨δ, hδ, Hδ⟩ := exists_mixedRightComparison_compact_witnesses ξ s h ε
    hr0 hr hgap hS ht hu hmin hnear hsmall
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ _ z hz n hn sk hatt
  let := hatt
  obtain ⟨m, hm, ℓ, Hm⟩ := Hδ z hz
  have H := mixed_constrainedPhi_le_rightComparison hn ξ s h sk hr0 hr hm (ht z hz) (hu z hz) ℓ
  change δ ≤ 2 * mixedInterpolationPsi ξ s h z.1 - mixedRightComparison ξ s h r m ℓ z at Hm
  exact H.trans (by linarith)

theorem exists_mixed_constrainedPhi_compact_right_gap_of_near_minimum
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hgap : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S) (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q r) (s.q (r + 1)))
    (haway : ∀ z ∈ S, η ≤ |z.2 - s.q r|)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : ∀ u ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      (1 - t₀) / mixedLocalLeftConstant ξ ≤ |u - q| →
      2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
        (1 - t₀) * ξ.tangentRemainder u q) :
    ∃ δ > (0 : ℝ), ∀ (Ω : Type u) [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)], ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : MixedDisorder (Ω := Ω) n ξ, Nonempty (AT.ConstrainedPair n z.2) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * mixedInterpolationPsi ξ s h z.1 - δ := by
  let Sf := S ∩ {z : ℝ × ℝ | 1 - t₀ ≤ mixedLocalLeftConstant ξ * (z.2 - s.q r)}
  have hSf : IsCompact Sf := hS.inter_right (isClosed_le continuous_const
    (continuous_const.mul (continuous_snd.sub continuous_const)))
  have hu01 (z : ℝ × ℝ) (hz : z ∈ S) : z.2 ∈ Icc (0 : ℝ) 1 :=
    ⟨(s.q_nonneg (by omega)).trans (hu z hz).1,
      (hu z hz).2.trans (s.q_le_one (by omega))⟩
  have hfar' : ∀ z ∈ Sf, 2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
      (1 - z.1) * ξ.tangentRemainder z.2 (s.q r) := by
    intro z hz
    have hdist : (1 - t₀) / mixedLocalLeftConstant ξ ≤ |z.2 - s.q r| := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hu z hz.1).1)]
      exact (div_le_iff₀ (mixedLocalLeftConstant_pos ξ)).mpr (by
        have H : 1 - t₀ ≤ mixedLocalLeftConstant ξ * (z.2 - s.q r) := hz.2
        simpa only [mul_comm] using H)
    have H := hfar z.2 (hu01 z hz.1) (s.q r)
      ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩ hdist
    have HB : (1 - t₀) * ξ.tangentRemainder z.2 (s.q r) ≤
        (1 - z.1) * ξ.tangentRemainder z.2 (s.q r) :=
      mul_le_mul_of_nonneg_right (by linarith [(ht z hz.1).2])
        (ξ.tangentRemainder_nonneg ⟨by linarith [(hu01 z hz.1).1], (hu01 z hz.1).2⟩
          ⟨by linarith [s.q_nonneg (by omega : r ≤ k + 2)], s.q_le_one (by omega)⟩)
    exact H.trans_le HB
  obtain ⟨δf, hδf, Hδf⟩ := exists_mixed_constrainedPhi_compact_right_gap_all_spaces ξ s h ε
    hr0 hr hgap hSf (fun z hz => ⟨(ht z hz.1).1, (ht z hz.1).2.trans ht₀.le⟩)
    (fun z hz => hu z hz.1) hmin hnear hfar'
  let δl := (1 - t₀) ^ 2 / 8 * η ^ 2
  have hδl : 0 < δl := mul_pos (div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) (by norm_num))
    (sq_pos_of_pos hη)
  refine ⟨min δl δf, lt_min hδl hδf, ?_⟩
  intro Ω _ _ z hz n hn sk hatt
  let := hatt
  by_cases hlocal : mixedLocalLeftConstant ξ * (z.2 - s.q r) ≤ 1 - t₀
  · have H := mixed_constrainedPhi_local_right_of_near_minimum hn ξ s h ε sk
      hr0 hr hgap hleft hright (ht z hz) ht₀ (hu z hz) hmin hnear hsmall hlocal
    have HQ := mul_self_le_mul_self hη.le (haway z hz)
    rw [← pow_two, ← pow_two, sq_abs] at HQ
    have HB := mul_le_mul_of_nonneg_left HQ
      (div_nonneg (sq_nonneg (1 - t₀)) (by norm_num : (0 : ℝ) ≤ 8))
    change δl ≤ (1 - t₀) ^ 2 / 8 * (z.2 - s.q r) ^ 2 at HB
    exact H.trans (by linarith [min_le_left δl δf])
  · have H := Hδf Ω z ⟨hz, (lt_of_not_ge hlocal).le⟩ hn sk hatt
    exact H.trans (by linarith [min_le_right δl δf])

end FourPapersCommon
