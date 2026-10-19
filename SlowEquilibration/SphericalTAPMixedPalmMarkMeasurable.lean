-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedEnergyPalmAnnealedIntegrable

@[expose] public section

/-! The actual determinant-weighted original band partition, integrated
against the mixed coefficient posterior, is Borel in the radial score. -/

namespace SlowEquilibration.SphericalTAPMixedPalmMarkMeasurable
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalSequentialRegression
open WholeFieldRegression
open IntrinsicHessianLaw
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPCriticalBandSectionBridge
set_option autoImplicit false

theorem mixed_markPalm_band_ratio_measurable
    (d : ℕ) (μ : FiniteMixture) (Q β e q b : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) :
    Measurable (fun k : ℝ =>
      (∫ J, intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b)))
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
      (∫ J, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k)))) := by
  let obs := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
    u (tangentFrame u hu)
  let κ := coefficientKernel obs
  let target := fun k : ℝ => jointScoreTarget (d+1)
    (((d+2:ℕ):ℝ) • scorePairEquiv (e,k))
  have hscore : Measurable (fun k : ℝ => scorePairEquiv (e,k)) :=
    scorePairEquiv.measurable.comp (measurable_const.prodMk measurable_id)
  have hscaled : Measurable (fun k : ℝ =>
      (((d+2:ℕ):ℝ)) • scorePairEquiv (e,k)) :=
    (measurable_const : Measurable (fun _ : ℝ => (((d+2:ℕ):ℝ)))).smul hscore
  have htarget : Measurable target :=
    (jointScoreTarget_continuous (d+1)).measurable.comp hscaled
  have hD : Measurable (intrinsicDet μ Q u) := by
    unfold intrinsicDet
    have hm := (SphericalMarkedWindows.intrinsicDet_measurable
      (centerCoefficients (mixtureCoefficients μ) Q) u hu).ennreal_toReal
    convert hm using 1
    ext J
    exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
  have hP : Measurable (fun J : Disorder (d+2) μ.maxDegree =>
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b)))) :=
    sourceBandPartition_measurable (d+1) μ u _ measurableSet_Icc β
  have hnum : Measurable (fun k : ℝ =>
      ∫ J, intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b))) ∂κ (target k)) :=
    ((hD.mul hP).stronglyMeasurable.integral_kernel (κ := κ)).measurable.comp htarget
  have hden : Measurable (fun k : ℝ =>
      ∫ J, intrinsicDet μ Q u J ∂κ (target k)) :=
    (hD.stronglyMeasurable.integral_kernel (κ := κ)).measurable.comp htarget
  have hmain := hnum.div hden
  convert hmain using 1
  ext k
  rfl

end
end SlowEquilibration.SphericalTAPMixedPalmMarkMeasurable
