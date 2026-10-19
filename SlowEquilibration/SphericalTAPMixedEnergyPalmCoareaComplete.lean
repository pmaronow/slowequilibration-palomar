-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmRatioIntegrable

@[expose] public section

/-! Exact mixed energy-Palm physical coarea ratio. Both radial integrability
conditions are derived from the genuine all-critical radial probability law. -/

namespace SlowEquilibration.SphericalTAPMixedEnergyPalmCoareaComplete
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPMixedPalmSourceUpper SphericalTAPMixedSourceLaplaceRatio
open SphericalTAPMixedPhysicalRadialLower
open SphericalTAPMixedBandExponent
open SphericalTAPMixedEnergyPalmCoareaRatio
open SphericalTAPMixedEnergyPalmAnnealedIntegrable
open SphericalTAPMixedPalmRatioIntegrable
set_option autoImplicit false

theorem mixed_energy_palm_coarea_ratio_of_fixed_marks
    (d : ℕ) (hd : 1 ≤ d) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (β e L R q b C : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hLR : L < R) (hb : 0 < b) (hC : 0 ≤ C)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (0:ℝ) 1)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hmark : ∀ k ∈ Ioo L R,
      (∫ J, intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b)))
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
      (∫ J, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      C*(latitudeNormalization (d+1)).toReal *
        (∫ a in Icc (q-b) (q+b),
          (Real.sqrt (1-a^2))^(d-1) *
            Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume)) :
    sourceMixedEnergyPalmBandExpectation d μ Q β e L R q b u hu ≤
      C*(latitudeNormalization (d+1)).toReal *
        (sourceMixedJointLaplace d μ β Q e L R q b /
          sourceMixedRadialLaplace d μ Q e L R) := by
  exact mixed_energy_palm_coarea_ratio d hd μ hQ β e L R q b C
    hEdge hLR hb hband u hu
    (mixed_markPalm_band_ratio_integrable_of_bound
      d μ hQ β e L R q b C hEdge hLR hC u hu hmark)
    (mixed_annealed_latitude_integrable_palm
      d μ hQ β e L R q b hEdge hLR)
    hmark

end
end SlowEquilibration.SphericalTAPMixedEnergyPalmCoareaComplete
