-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalFixedBandPalmLower
public import SlowEquilibration.SphericalMarkedRawRadialNormalization

@[expose] public section

/-! The source 12.20 energy-Palm radial mixing weight is exactly the
all-critical one-point Kac--Rice density after removing the factor common
to all radial marks. -/

namespace SlowEquilibration.SphericalTAPCriticalEnergyPalmIntensity
noncomputable section
open MeasureTheory Set
open SphericalMarkedWindows SphericalTAPCriticalEnergyPalmAverage
open SphericalSequentialRegression GOEPhysicalPotential
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- In physical energy coordinates, the original all-critical radial
intensity is the source all-critical Palm weight times the common Kac--Rice
factor. This uses the unrestricted absolute determinant mean, never the
local-maximum determinant mean. -/
theorem mixedCriticalPhysicalIntensity_eq_sourceAllCriticalRadialWeight
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (e k : ℝ) :
    (mixedCriticalPhysicalIntensity d μ Q (((d+2:ℕ):ℝ)*e) k).toReal =
      sourcePhysicalRadialFactor d μ Q *
        sourceAllCriticalRadialWeight d μ Q e k := by
  have hN : 0 < (((d+2:ℕ):ℝ)) := by positivity
  have hD := sourceScoreDenominator_pos μ hQ hnp
  unfold mixedCriticalPhysicalIntensity mixedCriticalIntensity physicalScorePdf
  simp only [mul_div_cancel_left₀ _ hN.ne',ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hN.le)]
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  change (((d+2:ℕ):ℝ))⁻¹ *
      ((sphereKRPrefactor (d+1) μ Q).toReal *
        (ENNReal.ofReal (((d+2:ℕ):ℝ)/sourceScoreDenominator μ Q*
          Real.exp (-((d+2:ℕ):ℝ)/2*
            scoreQuadratic μ Q (scorePairEquiv (e,k))))).toReal *
        (ENNReal.ofReal (physicalMean d (d+2)
          (Q^2*μ.xi2 Q) k)).toReal) = _
  rw [ENNReal.toReal_ofReal (by positivity :
    0 ≤ (((d+2:ℕ):ℝ))/sourceScoreDenominator μ Q*
      Real.exp (-((d+2:ℕ):ℝ)/2*
        scoreQuadratic μ Q (scorePairEquiv (e,k))))]
  rw [ENNReal.toReal_ofReal (show 0 ≤ physicalMean d (d+2)
      (Q^2*μ.xi2 Q) k by
    unfold physicalMean
    exact integral_nonneg (fun _ => abs_nonneg _))]
  unfold sourcePhysicalRadialFactor sourceAllCriticalRadialWeight
  rw [show -((d+2:ℕ):ℝ)/2 * scoreQuadratic μ Q (scorePairEquiv (e,k)) =
      -((d+2:ℕ):ℝ) * scoreQuadratic μ Q (scorePairEquiv (e,k))/2 by ring]
  field_simp

/-- The radial law obtained by normalizing the actual physical
all-critical Kac--Rice energy intensity. -/
def sourcePhysicalAllCriticalRadialLaw (d : ℕ) (μ : FiniteMixture)
    (Q E L R : ℝ) : Measure ℝ :=
  NormalizedRadialMeasure.law
    (fun k => (mixedCriticalPhysicalIntensity d μ Q E k).toReal) (Ioo L R)

/-- The Palm radial mixing law is exactly the normalized original
all-critical Kac--Rice intensity at physical energy `N e`. -/
theorem sourcePhysicalAllCriticalRadialLaw_eq_sourceAllCriticalRadialLaw
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (e L R : ℝ) :
    sourcePhysicalAllCriticalRadialLaw d μ Q (((d+2:ℕ):ℝ)*e) L R =
      sourceAllCriticalRadialLaw d μ Q e L R := by
  have hfactor : 0 < sourcePhysicalRadialFactor d μ Q :=
    sourcePhysicalRadialFactor_pos d μ hQ hnp
  have hnorm :
      (∫ k in Ioo L R,
        (mixedCriticalPhysicalIntensity d μ Q (((d+2:ℕ):ℝ)*e) k).toReal) =
        sourcePhysicalRadialFactor d μ Q *
          (∫ k in Ioo L R,sourceAllCriticalRadialWeight d μ Q e k) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _
      (mixedCriticalPhysicalIntensity_eq_sourceAllCriticalRadialWeight
        d μ hQ hnp e))
  unfold sourcePhysicalAllCriticalRadialLaw sourceAllCriticalRadialLaw
    NormalizedRadialMeasure.law
  congr 1
  funext k
  change ENNReal.ofReal
      ((mixedCriticalPhysicalIntensity d μ Q (((d+2:ℕ):ℝ)*e) k).toReal /
        (∫ v in Ioo L R,
          (mixedCriticalPhysicalIntensity d μ Q (((d+2:ℕ):ℝ)*e) v).toReal)) =
      ENNReal.ofReal (sourceAllCriticalRadialWeight d μ Q e k /
        (∫ v in Ioo L R,sourceAllCriticalRadialWeight d μ Q e v))
  rw [mixedCriticalPhysicalIntensity_eq_sourceAllCriticalRadialWeight
      d μ hQ hnp e k,hnorm]
  rw [mul_div_mul_left _ _ hfactor.ne']

end
end SlowEquilibration.SphericalTAPCriticalEnergyPalmIntensity
