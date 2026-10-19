-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedLowSumIntegral
public import SlowEquilibration.SphericalTAPCriticalLightCountTransfer

@[expose] public section

/-! The genuine unbounded partition mark in the mixed below-window sum is
Borel and fits the original full-field marked Kac--Rice formula. -/

namespace SlowEquilibration.SphericalTAPMixedLowSumMarkedKR
noncomputable section
open MeasureTheory Set SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalTAPCriticalBandSectionBridge
open SphericalSequentialRegression IntrinsicHessianLaw SphereHessian
open scoped ENNReal
set_option autoImplicit false

def sourceMixedBandMark (d : ℕ) (μ : FiniteMixture)
    (β q b : ℝ) (J : Disorder (d+2) μ.maxDegree)
    (u : Vector (d+2)) : ℝ≥0∞ :=
  ENNReal.ofReal (partitionOn β (field (mixtureCoefficients μ) J)
    (overlapRegion u (Icc (q-b) (q+b))))

theorem sourceMixedBandMark_measurable (d : ℕ) (μ : FiniteMixture)
    (β q b : ℝ) :
    Measurable (fun z : Disorder (d+2) μ.maxDegree × Vector (d+2) =>
      sourceMixedBandMark d μ β q b z.1 z.2) := by
  simpa only [sourceMixedBandMark,overlapRestrictedPartition,overlapRegion]
    using (overlapRestrictedPartition_measurable
      (N := d+2) (mixtureCoefficients μ) β measurableSet_Icc).ennreal_ofReal

/-- Expected original partition sum over actual critical points in a
physical-energy/radial rectangle, with no bounded-mark restriction. -/
theorem actual_mixed_band_sum_marked_kacRice
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (β q b E₁ E₂ L R : ℝ) :
    let K := physicalEnergyWindow (d+2) (Icc E₁ E₂) (Ioo L R)
    (∫⁻ J, actualScoreWindowCount (d+1)
      (centerCoefficients (mixtureCoefficients μ) Q) K
        (sourceMixedBandMark d μ β q b) J
        ∂disorderLaw (d+2) μ.maxDegree) =
      sphereKRPrefactor (d+1) μ Q *
        ∫⁻ u, mixedWindowIntensity (d+1) μ Q K
          (sourceMixedBandMark d μ β q b) u ∂sphereLaw (d+2) := by
  let K := physicalEnergyWindow (d+2) (Icc E₁ E₂) (Ioo L R)
  have hK : MeasurableSet K :=
    rectangularScoreWindow_measurable _ _
      (measurableSet_Icc.preimage (measurable_const_mul _)) measurableSet_Ioo
  exact (actual_mixed_score_window_kacRice (d+1) (by omega) μ hQ hnp
    K hK (sourceMixedBandMark d μ β q b)
    (sourceMixedBandMark_measurable d μ β q b)).2

/-- A score-dependent bound on each genuine conditioned determinant-weighted
mark transfers through marked Kac--Rice without replacing the mark by a
bounded truncation. The score weight may retain its full energy dependence. -/
theorem actual_mixed_marked_count_le_score_weight
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (psi : Disorder (d+2) μ.maxDegree → Vector (d+2) → ℝ≥0∞)
    (hpsi : Measurable fun z : Disorder (d+2) μ.maxDegree × Vector (d+2) =>
      psi z.1 z.2)
    (w : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (hPalm : ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
      (z : EuclideanSpace ℝ (Fin 2)), z ∈ K →
      (∫⁻ J, ENNReal.ofReal |(intrinsicHessian
        (field (centerCoefficients (mixtureCoefficients μ) Q) J) u).det| *
        psi J u
        ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q)
          u hu z) ≤
      w z * ENNReal.ofReal
        (GOEPhysicalPotential.physicalMean d (d+2) (Q^2*μ.xi2 Q) (z 1))) :
    (∫⁻ J, actualScoreWindowCount (d+1)
      (centerCoefficients (mixtureCoefficients μ) Q) K psi J
        ∂disorderLaw (d+2) μ.maxDegree) ≤
      sphereKRPrefactor (d+1) μ Q *
        ∫⁻ z in K, physicalScorePdf (d+2) μ Q z *
          (w z * ENNReal.ofReal
            (GOEPhysicalPotential.physicalMean d (d+2) (Q^2*μ.xi2 Q) (z 1))) := by
  let B : ℝ≥0∞ := ∫⁻ z in K, physicalScorePdf (d+2) μ Q z *
    (w z * ENNReal.ofReal
      (GOEPhysicalPotential.physicalMean d (d+2) (Q^2*μ.xi2 Q) (z 1)))
  rw [(actual_mixed_score_window_kacRice (d+1) (by omega) μ hQ hnp
    K hK psi hpsi).2]
  have houter : (∫⁻ u, mixedWindowIntensity (d+1) μ Q K psi u
      ∂sphereLaw (d+2)) ≤ B := by
    calc
      _ ≤ ∫⁻ _u : Vector (d+2), B ∂sphereLaw (d+2) := by
        apply lintegral_mono_ae
        filter_upwards [sphereLaw_support (by omega : 1 ≤ d+2)] with u hu
        rw [mixedWindowIntensity, dite_eq_left hu]
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hK] with z hz
        simpa only [show d+1+1=d+2 by omega] using
          mul_le_mul_right (hPalm u hu z hz)
            (physicalScorePdf (d+2) μ Q z)
      _ = B := by simp
  simpa only [mul_comm] using
    mul_le_mul_left houter (sphereKRPrefactor (d+1) μ Q)

end
end SlowEquilibration.SphericalTAPMixedLowSumMarkedKR
