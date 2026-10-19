module
public import FourPapersCommon.MixedLocalRight
public import FourPapersCommon.MixedLocalLeftUniform

@[expose] public section

/-! Closed local-right quadratic gain for actual near-minimizing mixed schemes,
with the original physical stationarity and actual mixed instability bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem mixedRightSlope_le_local_of_near_minimum (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (s.q r) (s.q (r+1)))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : mixedLocalLeftConstant ξ * (u - s.q r) ≤ 1 - t₀) :
    mixedRightSlope ξ s h r t u ≤ -(1-t₀)/2*(u-s.q r) := by
  have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [← mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  have hε : 0 ≤ ε := by linarith
  have hη : 0 ≤ ε ^ (1 / 6 : ℝ) := Real.rpow_nonneg hε _
  let e := mixedInstabilityConstant ξ * ε ^ (1 / 6 : ℝ)
  have he : 0 ≤ e := mul_nonneg (mixedInstabilityConstant_nonneg ξ) hη
  have hc := mixedLocalLeftConstant_bounds ξ
  have he_small : e ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.2 hη
    change 4 * mixedInstabilityConstant ξ * ε ^ (1 / 6 : ℝ) ≤ _ at H
    dsimp [e]
    nlinarith only [H, hsmall]
  have hu_small : mixedLocalSlopeConstant ξ * (u - s.q r) ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.1 (sub_nonneg.mpr hu.1)
    nlinarith only [H, hlocal]
  have Hcurv := mixed_instability_bound_all_levels ξ s h ε hr0 hr hm hleft hright hmin hnear
  have hR : ξ.second (s.q r) * section4RightR (mixedClockScheme ξ s) (mixedBeta ξ) h r 0 ≤ 1 + e := by
    rw [section4RightR,sub_zero,section4THessianSquare_neighbor_full_eq_zero_all_levels
      (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr]
    dsimp [e]
    linarith
  have hQ : section4RightQ (mixedClockScheme ξ s) (mixedBeta ξ) h r 0=s.q r := by
    rw [section4RightQ,sub_zero]
    simp only [mixedClockScheme_m]
    have HH:=section4TVarianceQ_neighbor_full_eq_zero_all_levels (mixedClockScheme ξ s)
      (mixedBeta ξ) h hr0 hr
    simp only [mixedClockScheme_m] at HH
    rw [HH]
    exact mixed_endpointQ_eq_overlap_of_min_all_levels ξ s h hr0 hr hm (Or.inl hleft) hright hmin
  exact mixedRightSlope_le_local_of_endpoint_curvature ξ s h hr ht ht₀ he hu hQ hR he_small hu_small

universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem mixed_constrainedPhi_local_right_of_near_minimum
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (s.q r) (s.q (r+1))) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : mixedLocalLeftConstant ξ * (u - s.q r) ≤ 1 - t₀) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      2 * mixedInterpolationPsi ξ s h t - (1 - t₀) ^ 2 / 8 * (u - s.q r) ^ 2 := by
  have HS := mixedRightSlope_le_local_of_near_minimum ξ s h ε hr0 hr hm hleft hright
    ht ht₀ hu hmin hnear hsmall hlocal
  have H := mixed_constrainedPhi_le_two_Psi_sub_right_factor_sq hn ξ s h sk hr0 hr
    ⟨ht.1, ht.2.trans ht₀.le⟩ hu
  have HL:=deriv_section5RightV_zero_eq_Q_all_levels (mixedClockScheme ξ s) (mixedBeta ξ)
    h hr (mixedRightSplitVariance_mem ξ s hr ⟨ht.1,ht.2.trans ht₀.le⟩ hu)
  simp only [mixedClockScheme_m] at HL
  rw [HL] at H
  change _ ≤ 2 * mixedInterpolationPsi ξ s h t - (mixedRightSlope ξ s h r t u) ^ 2 / 2 at H
  have HN : 0 ≤ (1 - t₀) / 2 * (u - s.q r) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num)) (sub_nonneg.mpr hu.1)
  have Hneg : (1-t₀)/2*(u-s.q r)≤-mixedRightSlope ξ s h r t u := by linarith only [HS]
  have HQ := mul_self_le_mul_self HN Hneg
  nlinarith only [H, HQ]

end FourPapersCommon
