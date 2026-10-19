-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedMarkedPalmRadial

@[expose] public section

/-! The source energy-Palm expectation controls the expected sum of the
genuine unbounded original-field band partition at all critical centers. -/

namespace SlowEquilibration.SphericalTAPMixedMarkedEnergyPalmBound
noncomputable section
open MeasureTheory Set SphericalModel SphericalGaussianJet
open SphericalSequentialRegression
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPMixedLowSumMarkedKR
open SphericalTAPMixedMarkedPhysicalEnergyDisintegration
open SphericalTAPMixedMarkedPalmIntegrand
open SphericalTAPMixedMarkedPalmRadial
open SphericalTAPMixedPalmSourceUpper
open SphericalTAPCriticalEnergyPalmAverage
open SourceMixedAllCriticalIntensityEnvelope
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- An upper bound for the exact energy-Palm band expectation at every
physical center and energy transfers through marked Kac--Rice to the
original critical-point sum. All dependence on the radial mark is integrated
against the original all-critical density before the bound is applied. -/
theorem actual_mixed_band_sum_le_energy_palm_envelope
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (β q b E₁ E₂ L R : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R)
    (B : ℝ → ℝ)
    (hCondInt : ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
      ∀ H ∈ Icc E₁ E₂, ∀ k ∈ Ioo L R,
        Integrable (fun J : Disorder (d+2) μ.maxDegree =>
          intrinsicDet μ Q u J *
            partitionOn β (field (mixtureCoefficients μ) J)
              (overlapRegion u (Icc (q-b) (q+b))))
          (mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k))))
    (hRatioInt : ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
      ∀ H ∈ Icc E₁ E₂,
        IntegrableOn (fun k =>
          ((∫ J, intrinsicDet μ Q u J *
            partitionOn β (field (mixtureCoefficients μ) J)
              (overlapRegion u (Icc (q-b) (q+b)))
            ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k))) /
          (∫ J, intrinsicDet μ Q u J
            ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k)))) *
          sourceAllCriticalRadialWeight d μ Q (H/(d+2:ℕ)) k)
          (Ioo L R))
    (hPalm : ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
      ∀ H ∈ Icc E₁ E₂,
        sourceMixedEnergyPalmBandExpectation d μ Q β (H/(d+2:ℕ))
          L R q b u hu ≤ B H) :
    (∫⁻ J, actualScoreWindowCount (d+1)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (d+2) (Icc E₁ E₂) (Ioo L R))
      (sourceMixedBandMark d μ β q b) J
      ∂disorderLaw (d+2) μ.maxDegree) ≤
    ∫⁻ H in Icc E₁ E₂,
      ENNReal.ofReal
        (sourceAllCriticalPhysicalEnergyDensity d μ Q L R H * B H) := by
  have hPrefFin : sphereKRPrefactor (d+1) μ Q ≠ ⊤ :=
    sphereKRPrefactor_ne_top (d+1) μ Q
  rw [actual_mixed_band_sum_physical_energy_kacRice
    d μ hQ hnp β q b E₁ E₂ L R]
  rw [←lintegral_const_mul' _ _ hPrefFin]
  let T : ℝ≥0∞ := ∫⁻ H in Icc E₁ E₂,
    ENNReal.ofReal (sourceAllCriticalPhysicalEnergyDensity d μ Q L R H * B H)
  calc
    (∫⁻ u, sphereKRPrefactor (d+1) μ Q *
        sourceMixedBandPhysicalEnergyIntensity d μ Q β q b
          (Icc E₁ E₂) (Ioo L R) u ∂sphereLaw (d+2)) ≤
        ∫⁻ _u : Vector (d+2), T ∂sphereLaw (d+2) := by
      apply lintegral_mono_ae
      filter_upwards [sphereLaw_support (by omega : 1 ≤ d+2)] with u hu
      rw [sourceMixedBandPhysicalEnergyIntensity, dite_eq_left hu]
      rw [←lintegral_const_mul' _ _ hPrefFin]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with H hH
      rw [←lintegral_const_mul' _ _ hPrefFin]
      have hRadial := physical_marked_radial_integral_eq_energy_palm
        d μ hQ hnp β H L R q b hEdge hLR u hu (hRatioInt u hu H hH)
      have hNum :
          (∫⁻ k in Ioo L R,
            sphereKRPrefactor (d+1) μ Q *
              (ENNReal.ofReal (((d+2:ℕ):ℝ))⁻¹ *
                (physicalScorePdf (d+2) μ Q
                  (scorePairEquiv (H/(d+2:ℕ),k)) *
                  ∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) *
                    sourceMixedBandMark d μ β q b J u
                    ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k))))) =
          ENNReal.ofReal
            (sourceAllCriticalPhysicalEnergyDensity d μ Q L R H *
              sourceMixedEnergyPalmBandExpectation d μ Q β (H/(d+2:ℕ))
                L R q b u hu) := by
        calc
          _ = ∫⁻ k in Ioo L R,
              mixedCriticalPhysicalIntensity d μ Q H k *
                ENNReal.ofReal
                  ((∫ J, intrinsicDet μ Q u J *
                      partitionOn β (field (mixtureCoefficients μ) J)
                        (overlapRegion u (Icc (q-b) (q+b)))
                      ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k))) /
                    (∫ J, intrinsicDet μ Q u J
                      ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k)))) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
            exact physical_marked_density_eq_intensity_mul_palm_ratio
              d μ hQ hnp β q b H k (hEdge.trans hk.1) u hu
              (hCondInt u hu H hH k hk)
          _ = _ := hRadial
      rw [hNum]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (hPalm u hu H hH)
          (sourceAllCriticalPhysicalEnergyDensity_nonneg d μ hQ hnp L R H))
    _ = T := by simp

end
end SlowEquilibration.SphericalTAPMixedMarkedEnergyPalmBound
