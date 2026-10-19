-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedLowSumMarkedKR
public import SlowEquilibration.SphericalTAPCriticalEnergyPalmIntensity

@[expose] public section

/-! The literal physical all-critical energy density times the source
energy-Palm band expectation is the unnormalized determinant-weighted radial
numerator. This is the density identity used by source Corollary 12.17. -/

namespace SlowEquilibration.SphericalTAPMixedPalmDensityDisintegration
noncomputable section
open MeasureTheory Set SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPMixedPalmSourceUpper SphericalTAPMixedPhysicalRadialBridge
set_option autoImplicit false

theorem physical_allcritical_density_mul_bandPalm_eq_radial_numerator
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (β e L R q b : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) :
    (sourcePhysicalRadialFactor d μ Q *
      ∫ k in Ioo L R, sourceAllCriticalRadialWeight d μ Q e k) *
      sourceMixedEnergyPalmBandExpectation d μ Q β e L R q b u hu =
    sourcePhysicalRadialFactor d μ Q *
      ∫ k in Ioo L R,
        ((∫ J, intrinsicDet μ Q u J *
          partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u (Icc (q-b) (q+b)))
          ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
        (∫ J, intrinsicDet μ Q u J
          ∂mixedLaw μ Q u hu (scorePairEquiv (e,k)))) *
          sourceAllCriticalRadialWeight d μ Q e k := by
  let W := sourceAllCriticalRadialWeight d μ Q e
  let G := fun k : ℝ =>
    ((∫ J, intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b)))
      ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
    (∫ J, intrinsicDet μ Q u J
      ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))))
  have hZ : 0 < ∫ k in Ioo L R, W k :=
    sourceAllCriticalRadialWeight_integral_pos d μ hQ e hEdge hLR
  have hLaw : (∫ k, G k ∂sourceAllCriticalRadialLaw d μ Q e L R) =
      (∫ k in Ioo L R, G k*W k) /
        (∫ k in Ioo L R, W k) :=
    NormalizedRadialMeasure.law_integral
      (sourceAllCriticalRadialWeight_measurable d μ Q e)
      (sourceAllCriticalRadialWeight_nonneg d μ Q e) hZ G
  change (sourcePhysicalRadialFactor d μ Q *
      ∫ k in Ioo L R, W k) *
      (∫ k, G k ∂sourceAllCriticalRadialLaw d μ Q e L R) =
    sourcePhysicalRadialFactor d μ Q *
      ∫ k in Ioo L R, G k*W k
  rw [hLaw]
  field_simp [hZ.ne']

end
end SlowEquilibration.SphericalTAPMixedPalmDensityDisintegration
