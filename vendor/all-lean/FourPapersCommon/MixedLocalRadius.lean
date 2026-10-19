module
public import FourPapersCommon.MixedLocalLeftUniform
public import FourPapersCommon.MixedLocalRightUniform

@[expose] public section

/-! Genuine two-sided local tubes at positive physical levels.  The radius
is selected before the probability space, and repeated terminal level one is
handled using the physical overlap range. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
set_option maxHeartbeats 800000

theorem exists_mixed_positive_level_local_radius
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ η > (0 : ℝ), ∀ (Ω : Type u) [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)], ∀ {n : ℕ}, 0 < n →
      ∀ sk : MixedDisorder (Ω := Ω) n ξ, ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (-1 : ℝ) 1, |u - s.q r| ≤ η →
      Nonempty (AT.ConstrainedPair n u) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
        2 * mixedInterpolationPsi ξ s h t - (1 - t₀) ^ 2 / 8 * (u - s.q r) ^ 2 := by
  let R := if s.q r < s.q (r + 1) then s.q (r + 1) - s.q r else (1 : ℝ)
  have hR : 0 < R := by
    dsimp [R]
    split_ifs with hh
    · exact sub_pos.mpr hh
    · norm_num
  let η := min ((1 - t₀) / mixedLocalLeftConstant ξ)
    (min (s.q r / 2) (min (s.q r - s.q (r - 1)) R))
  have hq : 0 < s.q r := (s.q_nonneg (by omega)).trans_lt hleft
  have hη : 0 < η := lt_min (div_pos (sub_pos.mpr ht₀) (mixedLocalLeftConstant_pos ξ))
    (lt_min (by positivity) (lt_min (sub_pos.mpr hleft) hR))
  have hηC : η ≤ (1 - t₀) / mixedLocalLeftConstant ξ := min_le_left _ _
  have hηQ : η ≤ s.q r / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηL : η ≤ s.q r - s.q (r - 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηR : η ≤ R := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨η, hη, ?_⟩
  intro Ω _ _ n hn sk t ht u hu hdist hatt
  let := hatt
  have Habs := abs_le.mp hdist
  have hCη : mixedLocalLeftConstant ξ * η ≤ 1 - t₀ := by
    have H := (le_div_iff₀ (mixedLocalLeftConstant_pos ξ)).mp hηC
    simpa only [mul_comm] using H
  by_cases huq : u ≤ s.q r
  · have huI : u ∈ Icc (s.q (r - 1)) (s.q r) := ⟨by linarith [Habs.1], huq⟩
    have hlocal : mixedLocalLeftConstant ξ * (s.q r - u) ≤ 1 - t₀ :=
      (mul_le_mul_of_nonneg_left (by linarith [Habs.1] : s.q r - u ≤ η)
        (mixedLocalLeftConstant_pos ξ).le).trans hCη
    exact mixed_constrainedPhi_local_left_of_near_minimum hn ξ s h ε sk
      hr0 hr hm hleft hright ht ht₀ huI hmin hnear hsmall hlocal
  · have huI : u ∈ Icc (s.q r) (s.q (r + 1)) := by
      refine ⟨(lt_of_not_ge huq).le, ?_⟩
      rcases hright with hright | hterminal
      · have Hη : η ≤ s.q (r + 1) - s.q r := by simpa [R, hright] using hηR
        linarith [Habs.2]
      · have Htop := s.q_mono r hr
        linarith [hu.2]
    have hlocal : mixedLocalLeftConstant ξ * (u - s.q r) ≤ 1 - t₀ :=
      (mul_le_mul_of_nonneg_left Habs.2 (mixedLocalLeftConstant_pos ξ).le).trans hCη
    exact mixed_constrainedPhi_local_right_of_near_minimum hn ξ s h ε sk
      hr0 hr hm hleft hright ht ht₀ huI hmin hnear hsmall hlocal

end FourPapersCommon
