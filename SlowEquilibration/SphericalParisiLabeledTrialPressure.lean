-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledTrialEndpoint
public import SlowEquilibration.SphericalParisiLabeledOriginalPressure

@[expose] public section

/-! Genuine finite linear-trial pressure endpoint and its exact common/fresh
Gaussian determinant bound, before taking any thermodynamic or zero-temp
limit. The original reference measure on the sphere is arbitrary. -/

namespace SlowEquilibration.SphericalParisiLabeledTrialPressure
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledRealization SphericalParisiLabeledThreeBlock
open SphericalParisiLabeledUnheldComparison SphericalParisiLabeledOriginalEndpoint
open SphericalParisiLabeledTrialEndpoint SphericalParisiCommonGaussianTrial
open GaussianCompactFeatureComparison GaussianSpinInterpolation
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def trialPressure {N k : ℕ} [NeZero k] (μ : Measure (UnitSphere N)) (β a0 a : ℝ) : ℝ :=
  ∫ G,logPartition (μ.prod (labelLaw k)) (trialLinear β a0 a) G
    ∂SYK.standardGaussianMeasureOnEuclidean (TrialCoordinate N k)

theorem actual_trial_log_partition_integrable {N k : ℕ} [NeZero k]
    (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ] (β a0 a : ℝ) :
    Integrable (logPartition (μ.prod (labelLaw k)) (trialLinear β a0 a))
      (SYK.standardGaussianMeasureOnEuclidean (TrialCoordinate N k)) := by
  obtain ⟨C,hC,hbound⟩ := trialLinear_bounded (N := N) (k := k) β a0 a
  simpa only [one_smul] using logPartition_radial_gaussian_integrable (μ.prod (labelLaw k)) _
    (trialLinear_continuous β a0 a).measurable hC (.of_forall hbound) (1 : ℝ)

theorem actual_trial_common_row_gaussian_law (N k : ℕ) :
    HasLaw (sumJoin (ι := Fin N) (κ := Fin k × Fin N))
      (SYK.standardGaussianMeasureOnEuclidean (TrialCoordinate N k)) (commonRowLaw N k) := by
  refine ⟨sumJoin.continuous.measurable.aemeasurable,?_⟩
  unfold commonRowLaw
  rw [show stdGaussian (EuclideanSpace ℝ (Fin N))=
    SYK.standardGaussianMeasureOnEuclidean (Fin N) by
      rw [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian],
    ← sumSplit_gaussian_map,Measure.map_map sumJoin.continuous.measurable sumSplit.continuous.measurable]
  rw [show sumJoin ∘ (sumSplit (ι := Fin N) (κ := Fin k × Fin N))=id by
    funext G;exact sumJoin_sumSplit G,Measure.map_id]

/-- True finite trial pressure determinant bound, with the exact finite
label entropy cost and the actual common-field varianceNa0. -/
theorem actual_trial_pressure_quadratic_upper {N k : ℕ} [NeZero k]
    (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ] {β a0 a m b : ℝ}
    (hβ : 0 ≤ β) (ha0 : 0 ≤ a0) (ha : 0 ≤ a) (hm : 0 < m) (hm1 : m ≤ 1)
    (hb : 0 < b) (hmargin : 0 < b-(m*(β*Real.sqrt (N : ℝ)))*a) :
    trialPressure (k := k) μ β a0 a ≤
      -((N : ℝ)/2)*Real.log (1-(m*(β*Real.sqrt (N : ℝ)))*a/b)/m+
        (β*Real.sqrt (N : ℝ))*b/2+
        (β*Real.sqrt (N : ℝ))*a0*(N : ℝ)/(2*(b-(m*(β*Real.sqrt (N : ℝ)))*a))+
        (1-m)*Real.log (k : ℝ)/m := by
  have hEll : 0 ≤ β*Real.sqrt (N : ℝ) := mul_nonneg hβ (Real.sqrt_nonneg _)
  have hk : 0 < k := NeZero.pos k
  have hi := actual_trial_log_partition_integrable (k := k) μ β a0 a
  have hLaw := actual_trial_common_row_gaussian_law N k
  have hNorm := actual_common_row_integrable (N := N) hk ha0 ha hEll hm hm1 hb hmargin
  have H := integral_mono (hLaw.integrable_comp hi) hNorm
    (fun p => actual_trial_log_partition_le_norm_rows μ hβ a0 a p.1 p.2)
  have hExpect := hLaw.integral_comp hi.aestronglyMeasurable
  change (∫ p,logPartition (μ.prod (labelLaw k)) (trialLinear β a0 a) (sumJoin p) ∂commonRowLaw N k) ≤ _ at H
  simp only [Function.comp_def] at hExpect
  rw [hExpect] at H
  exact H.trans (actual_common_row_quadratic_upper hk ha0 ha hEll hm hm1 hb hmargin)

end
end SlowEquilibration.SphericalParisiLabeledTrialPressure
