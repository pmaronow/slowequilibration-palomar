-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmMarkMeasurable

@[expose] public section

/-! A fixed-mark physical coarea bound makes the original mixed Palm ratio
integrable over its genuine all-critical radial law. -/

namespace SlowEquilibration.SphericalTAPMixedPalmRatioIntegrable
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPMixedBandExponent
open SphericalTAPMixedEnergyPalmAnnealedIntegrable
open SphericalTAPMixedPalmMarkMeasurable
set_option autoImplicit false

theorem mixed_markPalm_band_ratio_integrable_of_bound
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (β e L R q b C : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R)
    (hC : 0 ≤ C)
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
    Integrable (fun k : ℝ =>
      (∫ J, intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b)))
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
      (∫ J, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))))
      (sourceAllCriticalRadialLaw d μ Q e L R) := by
  let ρ := sourceAllCriticalRadialLaw d μ Q e L R
  let M := fun k : ℝ =>
    (∫ J, intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b)))
      ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
    (∫ J, intrinsicDet μ Q u J
      ∂mixedLaw μ Q u hu (scorePairEquiv (e,k)))
  let G := fun k : ℝ => ∫ a in Icc (q-b) (q+b),
    (Real.sqrt (1-a^2))^(d-1) *
      Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume
  have hMMeas : Measurable M :=
    mixed_markPalm_band_ratio_measurable d μ Q β e q b u hu
  have hGInt : Integrable G ρ :=
    mixed_annealed_latitude_integrable_palm d μ hQ β e L R q b hEdge hLR
  have hG0 (k : ℝ) : 0 ≤ G k := by
    exact integral_nonneg fun a => mul_nonneg
      (pow_nonneg (Real.sqrt_nonneg _) _) (Real.exp_pos _).le
  have hM0 (k : ℝ) : 0 ≤ M k := by
    apply div_nonneg
    · exact integral_nonneg fun J => mul_nonneg
        (abs_nonneg _) (partitionOn_nonneg β _ _)
    · exact integral_nonneg fun J => abs_nonneg _
  have hF0 (k : ℝ) :
      0 ≤ C*(latitudeNormalization (d+1)).toReal*G k := by
    exact mul_nonneg (mul_nonneg hC ENNReal.toReal_nonneg) (hG0 k)
  have hFInt : Integrable
      (fun k => C*(latitudeNormalization (d+1)).toReal*G k) ρ :=
    hGInt.const_mul _
  have hMInt : Integrable M ρ := by
    apply Integrable.mono' hFInt hMMeas.aestronglyMeasurable
    filter_upwards [sourceAllCriticalRadialLaw_ae_mem d μ Q e L R] with k hk
    rw [Real.norm_of_nonneg (hM0 k)]
    exact hmark k hk
  exact hMInt

end
end SlowEquilibration.SphericalTAPMixedPalmRatioIntegrable
