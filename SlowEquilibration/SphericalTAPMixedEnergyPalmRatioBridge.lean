-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmSourceUpper

@[expose] public section

/-! The exact radial Palm averaging step after physical coarea. The one
explicit measure-theoretic premise identifies the radial numerator with the
joint source Laplace integral; its pointwise density identity is already
proved in `SphericalTAPMixedPalmDensityIdentity`. -/

namespace SlowEquilibration.SphericalTAPMixedEnergyPalmRatioBridge
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPMixedPalmSourceUpper SphericalTAPMixedSourceLaplaceRatio
open SphericalTAPMixedPhysicalRadialLower SphericalTAPMixedPhysicalRadialBridge
open SphericalTAPMixedBandExponent
open NormalizedRadialMeasure
set_option autoImplicit false

theorem mixed_energy_palm_coarea_ratio_of_fixed_marks
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (β e L R q b C : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) :
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
    Integrable M ρ → Integrable G ρ →
    (∀ k ∈ Ioo L R, M k ≤
      C*(latitudeNormalization (d+1)).toReal*G k) →
    (∫ k in Ioo L R, G k*sourceAllCriticalRadialWeight d μ Q e k) =
      Real.exp (((d+2:ℕ):ℝ)*(Real.log (Q*μ.xi1 Q)/2-1/2)) *
        sourceMixedJointLaplace d μ β Q e L R q b →
    sourceMixedEnergyPalmBandExpectation d μ Q β e L R q b u hu ≤
      C*(latitudeNormalization (d+1)).toReal *
        (sourceMixedJointLaplace d μ β Q e L R q b /
          sourceMixedRadialLaplace d μ Q e L R) := by
  dsimp only
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
  intro hMInt hGInt hmark hNum
  let T : ℝ := Real.exp (((d+2:ℕ):ℝ)*
    (Real.log (Q*μ.xi1 Q)/2-1/2))
  let W := sourceAllCriticalRadialWeight d μ Q e
  let I := sourceMixedRadialLaplace d μ Q e L R
  let J := sourceMixedJointLaplace d μ β Q e L R q b
  have hT : 0 < T := Real.exp_pos _
  have hDen : 0 < ∫ k in Ioo L R, W k :=
    sourceAllCriticalRadialWeight_integral_pos d μ hQ e hEdge hLR
  have hDenEq : (∫ k in Ioo L R, W k) = T*I :=
    sourceAllCriticalRadialWeight_integral_eq_chi d μ hQ e L R
  have hMono : (∫ k, M k ∂ρ) ≤
      ∫ k, C*(latitudeNormalization (d+1)).toReal*G k ∂ρ := by
    apply integral_mono_ae hMInt (hGInt.const_mul _)
    filter_upwards [sourceAllCriticalRadialLaw_ae_mem d μ Q e L R] with k hk
    exact hmark k hk
  have hNorm : (∫ k, G k ∂ρ) =
      (∫ k in Ioo L R, G k*W k) / (∫ k in Ioo L R, W k) := by
    exact NormalizedRadialMeasure.law_integral
      (sourceAllCriticalRadialWeight_measurable d μ Q e)
      (sourceAllCriticalRadialWeight_nonneg d μ Q e) hDen G
  have hRatio : (∫ k, G k ∂ρ) = J/I := by
    rw [hNorm,hNum,hDenEq]
    exact mul_div_mul_left _ _ hT.ne'
  change (∫ k, M k ∂ρ) ≤ C*(latitudeNormalization (d+1)).toReal*(J/I)
  calc
    _ ≤ ∫ k, C*(latitudeNormalization (d+1)).toReal*G k ∂ρ := hMono
    _ = C*(latitudeNormalization (d+1)).toReal*(∫ k,G k ∂ρ) :=
      integral_const_mul _ _
    _ = _ := by rw [hRatio]

end
end SlowEquilibration.SphericalTAPMixedEnergyPalmRatioBridge
