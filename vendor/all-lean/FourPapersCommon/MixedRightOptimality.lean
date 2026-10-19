module
public import FourPapersCommon.MixedRightInsertedFunctional
public import Targets.Section4RightOptimality

@[expose] public section

/-! Genuine quantitative near-optimality of the physical mixed right
variation, with actual inserted-measure mass comparisons. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def mixedSection4RightFirstVariation (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (r : ℕ) (u : ℝ) : ℝ :=
  section4RightU (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedRightSplitVariance ξ s r 1 u)/2-
    (ξ.correction u-ξ.correction (s.q r))/2

theorem hasDerivAt_mixedSection4RightPhi_mass_baseline (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r ≤ k+1) {u : ℝ}
    (hu : u∈Icc (s.q r) (s.q (r+1))) :
    HasDerivAt (fun m=>mixedSection4RightPhi ξ s h r m u)
      (mixedSection4RightFirstVariation ξ s h r u) (s.m r) := by
  have hv := mixedRightSplitVariance_mem ξ s hr (t := 1) (by norm_num) hu
  have H := hasDerivAt_section4RightT_mass_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv.1
  simp only [mixedClockScheme_m] at H
  have HD := ((hasDerivAt_id (s.m r)).const_sub (s.m r)).mul_const
    ((ξ.correction u-ξ.correction (s.q r))/2)
  convert! ((H.const_add (Real.log 2)).sub_const (mixedSchemeCorrection ξ s)).add HD using 1
  · unfold mixedSection4RightPhi
    funext m
    simp only [Pi.add_apply,id_eq]
    ring
  · unfold mixedSection4RightFirstVariation
    ring

theorem mixedSection4RightPhi_mass_taylor_baseline (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r ≤ k+1) {m u : ℝ}
    (hm : m∈Icc (0 : ℝ) 1) (hu : u∈Icc (s.q r) (s.q (r+1))) :
    |mixedSection4RightPhi ξ s h r m u-mixedFunctional ξ h (Paper.parisiSchemeMeasure s)-
      mixedSection4RightFirstVariation ξ s h r u*(m-s.m r)| ≤
      section4MassSecondBound ((mixedBeta ξ)^2)*(m-s.m r)^2 := by
  have hv := mixedRightSplitVariance_mem ξ s hr (t := 1) (by norm_num) hu
  have H := section4RightT_mass_taylor_bound (mixedClockScheme ξ s) (mixedBeta ξ) h hr
    ⟨s.m_nonneg hr,s.m_le_one hr⟩ hm hv
  have hD := (hasDerivAt_section4RightT_mass_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv.1).deriv
  have hbase := section4RightT_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv
  simp only [mixedClockScheme_m] at H hD hbase
  rw [hD,hbase] at H
  rw [mixedSection4RightPhi,mixedFunctional_scheme,mixedSection4RightFirstVariation]
  convert! H using 1
  congr 1
  ring

theorem mixedSection4RightFirstVariation_upper_bound (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hgap : s.m (r - 1) < s.m r) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε) :
    mixedSection4RightFirstVariation ξ s h r u ≤ section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε := by
  let C := section4MassSecondBound ((mixedBeta ξ) ^ 2) + 1
  have hC : 0 < C := by dsimp [C]; linarith [section4MassSecondBound_nonneg ((mixedBeta ξ) ^ 2)]
  have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [←mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  have hε : 0 ≤ ε := by linarith
  by_cases hf : mixedSection4RightFirstVariation ξ s h r u ≤ 0
  · exact hf.trans (mul_nonneg (section4OptimalityBound_pos (mixedBeta ξ)).le (Real.sqrt_nonneg ε))
  have hTaylor (m : ℝ) (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r)) :
      mixedSection4RightPhi ξ s h r m u - mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
        mixedSection4RightFirstVariation ξ s h r u * (m - s.m r) + C * (m - s.m r) ^ 2 := by
    have H := (abs_le.mp (mixedSection4RightPhi_mass_taylor_baseline ξ s h hr
      ⟨(s.m_nonneg (by omega)).trans hm.1, hm.2.trans (s.m_le_one hr)⟩ hu)).2
    dsimp [C]
    nlinarith [sq_nonneg (m - s.m r)]
  have hlower : 0 ≤ -mixedSection4RightFirstVariation ξ s h r u * (s.m r - s.m (r - 1)) +
      C * (s.m r - s.m (r - 1)) ^ 2 := by
    have H := mixedSection4RightPhi_lower_mass_min ξ s h hr0 hr hu hmin
    rw [mixedSection4RightPhi_baseline ξ s h hr hu] at H
    nlinarith only [H, hTaylor (s.m (r - 1)) ⟨le_rfl, hgap.le⟩]
  have hcomp (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) (s.m r - s.m (r - 1))) :
      -ε ≤ -mixedSection4RightFirstVariation ξ s h r u * δ + C * δ ^ 2 := by
    have hm : s.m r - δ ∈ Set.Icc (s.m (r - 1)) (s.m r) := by
      constructor <;> linarith [hδ.1, hδ.2]
    have H := mixedSection4RightPhi_near_min ξ s h ε hr0 hr hm hu hnear
    rw [mixedSection4RightPhi_baseline ξ s h hr hu] at H
    nlinarith only [H, hTaylor (s.m r - δ) hm]
  have hsq := firstVariation_sq_le_of_quadratic_comparisons hC hgap
    (neg_neg_of_pos (lt_of_not_ge hf)) hlower hcomp
  rw [neg_sq] at hsq
  have H : mixedSection4RightFirstVariation ξ s h r u ≤ Real.sqrt (4 * C * ε) :=
    Real.le_sqrt_of_sq_le hsq
  have hsqrt : Real.sqrt (4 * C * ε) = section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε := by
    rw [Real.sqrt_mul' (4 * C) hε, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num [section4OptimalityBound, C]
  rwa [hsqrt] at H


end FourPapersCommon
