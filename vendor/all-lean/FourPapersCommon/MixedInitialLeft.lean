module
public import FourPapersCommon.MixedLocalLeftUniform
public import FourPapersCommon.MixtureMonotonicity
public import Targets.Section4InitialHessian

@[expose] public section

/-! Genuine quadratic overlap gain on the entire compulsory zero-mass interval.
Monotonicity of the mixed curvature and the actual Gaussian Jensen comparison
replace the local-overlap restriction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem mixedLeftSlope_initial_ge_of_endpoint_curvature
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) {t t₀ u e : ℝ}
    (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1) (he : 0 ≤ e)
    (hu : u ∈ Set.Icc 0 (s.q 1))
    (hQ : section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h 1 (s.m 0) 0 = s.q 1)
    (hR : ξ.second (s.q 1) * section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0 ≤ 1 + e)
    (he_small : e ≤ (1 - t₀) / 2) :
    (1 - t₀) / 2 * (s.q 1 - u) ≤ mixedLeftSlope ξ s h 1 t u := by
  have ht1 : t ∈ Set.Icc 0 1 := ⟨ht.1, ht.2.trans ht₀.le⟩
  have hsub : Set.Icc u (s.q 1) ⊆ Set.Icc (s.q (1 - 1)) (s.q 1) := by
    simpa only [Nat.sub_self, s.q_zero] using Set.Icc_subset_Icc hu.1 (le_refl (s.q 1))
  have hderiv (z : ℝ) (hz : z ∈ Set.Icc u (s.q 1)) :
      HasDerivWithinAt (mixedLeftSlope ξ s h 1 t)
        (t * ξ.second z * section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 (mixedLeftSplitVariance ξ s 1 t z) - 1)
        (Set.Icc u (s.q 1)) z :=
    (hasDerivWithinAt_mixedLeftSlope ξ s h (r := 1) le_rfl (by omega) ht1 (hsub hz)).mono hsub
  have hbound (z : ℝ) (hz : z ∈ Set.Icc u (s.q 1)) :
      t * ξ.second z * section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 (mixedLeftSplitVariance ξ s 1 t z) - 1 ≤
        -(1 - t₀) / 2 := by
    have hv : mixedLeftSplitVariance ξ s 1 t z ∈ Icc (0 : ℝ)
        ((mixedBeta ξ) ^ 2 * (mixedClockScheme ξ s).q 1) := by
      have HV := mixedLeftSplitVariance_mem ξ s (r := 1) (by omega) ht1 (hsub hz)
      simpa only [Nat.sub_self, mixedClockScheme_q, s.q_zero, ξ.clock_zero, sub_zero] using HV
    have HR := section4THessianSquare_initial_le_zero (mixedClockScheme ξ s) (mixedBeta ξ) h hv
    have HS := ξ.second_monotoneOn
      (show z ∈ Icc (0 : ℝ) 1 from ⟨hu.1.trans hz.1, hz.2.trans (s.q_le_one (by omega))⟩)
      (show s.q 1 ∈ Icc (0 : ℝ) 1 from ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩) hz.2
    have HR0 := section4THessianSquare_mem_Icc (mixedClockScheme ξ s) (mixedBeta ξ) h (r := 1) (by omega)
      (mixedLeftSplitVariance ξ s 1 t z)
    have Hscaled := mul_le_mul_of_nonneg_left
      (mul_le_mul HS HR HR0.1 (ξ.second_nonneg (s.q 1))) ht.1
    have Hbase := mul_le_mul_of_nonneg_left hR ht.1
    have He := mul_le_of_le_one_left he ht1.2
    nlinarith only [Hscaled, Hbase, He, ht.2, he_small]
  have hc : ContinuousOn (mixedLeftSlope ξ s h 1 t) (Set.Icc u (s.q 1)) :=
    fun z hz => (hderiv z hz).continuousWithinAt
  have hd : DifferentiableOn ℝ (mixedLeftSlope ξ s h 1 t) (interior (Set.Icc u (s.q 1))) := by
    rw [interior_Icc]
    exact fun z hz => ((hderiv z ⟨hz.1.le, hz.2.le⟩).hasDerivAt
      (Icc_mem_nhds hz.1 hz.2)).differentiableAt.differentiableWithinAt
  have HB : ∀ z ∈ interior (Set.Icc u (s.q 1)), deriv (mixedLeftSlope ξ s h 1 t) z ≤
      -(1 - t₀) / 2 := by
    rw [interior_Icc]
    intro z hz
    rw [((hderiv z ⟨hz.1.le, hz.2.le⟩).hasDerivAt (Icc_mem_nhds hz.1 hz.2)).deriv]
    exact hbound z ⟨hz.1.le, hz.2.le⟩
  have H := (convex_Icc u (s.q 1)).image_sub_le_mul_sub_of_deriv_le hc hd HB
    u ⟨le_rfl, hu.2⟩ (s.q 1) ⟨hu.2, le_rfl⟩ hu.2
  have Hzero : mixedLeftSlope ξ s h 1 t (s.q 1) = 0 := by
    simp only [mixedLeftSlope, mixedLeftSplitVariance, sub_self, mul_zero, Nat.sub_self, hQ]
  rw [Hzero] at H
  linarith


universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem mixed_constrainedPhi_initial_left_of_near_minimum
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) (hm : s.m 0 < s.m 1) (hq : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (0 : ℝ) (s.q 1)) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 1) t u ≤
      2 * mixedInterpolationPsi ξ s h t - (1 - t₀) ^ 2 / 8 * (u - s.q 1) ^ 2 := by
  have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [← mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  have hε : 0 ≤ ε := by linarith
  let e := mixedInstabilityConstant ξ * ε ^ (1 / 6 : ℝ)
  have he : 0 ≤ e := mul_nonneg (mixedInstabilityConstant_nonneg ξ) (Real.rpow_nonneg hε _)
  have He := mul_le_mul_of_nonneg_right (mixedLocalLeftConstant_bounds ξ).2.2 (Real.rpow_nonneg hε (1 / 6 : ℝ))
  have hes : e ≤ (1 - t₀) / 2 := by dsimp [e]; nlinarith only [He, hsmall, he]
  have HC := mixed_instability_bound_all_levels ξ s h ε (r := 1) le_rfl (by omega)
    (by simpa only [Nat.sub_self] using hm) (by simpa only [Nat.sub_self, s.q_zero] using hq) hright hmin hnear
  have hR : ξ.second (s.q 1) * section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0 ≤ 1 + e := by
    dsimp [e]; linarith only [HC]
  have hQ := mixed_endpointQ_eq_overlap_of_min_all_levels ξ s h (r := 1) le_rfl (by omega)
    (by simpa only [Nat.sub_self] using hm) (Or.inl (by simpa only [Nat.sub_self, s.q_zero] using hq)) hright hmin
  simp only [Nat.sub_self] at hQ
  have HS := mixedLeftSlope_initial_ge_of_endpoint_curvature ξ s h ht ht₀ he hu hQ hR hes
  have H := mixed_constrainedPhi_le_two_Psi_sub_left_factor_sq hn ξ s h sk (r := 1) le_rfl (by omega)
    ⟨ht.1, ht.2.trans ht₀.le⟩ (by simpa only [Nat.sub_self, s.q_zero] using hu)
  change constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - 1) t u ≤
    2 * mixedInterpolationPsi ξ s h t - (mixedLeftSlope ξ s h 1 t u) ^ 2 / 2 at H
  rw [show k + 2 - 1 = k + 1 by omega] at H
  have HN : 0 ≤ (1 - t₀) / 2 * (s.q 1 - u) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num)) (sub_nonneg.mpr hu.2)
  have HQ := mul_self_le_mul_self HN HS
  nlinarith only [H, HQ]

end FourPapersCommon
