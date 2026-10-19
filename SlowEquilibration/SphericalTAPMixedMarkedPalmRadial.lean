-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedMarkedPalmIntegrand

@[expose] public section

/-! The actual mixed all-critical radial intensity integrates the
determinant-weighted fixed-mark partition into the source energy-Palm law. -/

namespace SlowEquilibration.SphericalTAPMixedMarkedPalmRadial
noncomputable section
open MeasureTheory Set SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPCriticalEnergyPalmIntensity
open SphericalTAPMixedPalmSourceUpper
open SphericalTAPMixedPalmDensityDisintegration
open SphericalTAPMixedMarkedPalmIntegrand
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- Radial integration of the exact physical marked intensity equals the
physical all-critical energy density times the literal energy-Palm band
expectation. The integrability assumption is the fixed-mark ratio estimate
provided by the source quadratic-bank theorem. -/
theorem physical_marked_radial_integral_eq_energy_palm
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (β H L R q b : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hRatioInt : IntegrableOn (fun k =>
      ((∫ J, intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b)))
        ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k))) /
      (∫ J, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k)))) *
      sourceAllCriticalRadialWeight d μ Q (H/(d+2:ℕ)) k) (Ioo L R)) :
    (∫⁻ k in Ioo L R,
      mixedCriticalPhysicalIntensity d μ Q H k *
        ENNReal.ofReal
          ((∫ J, intrinsicDet μ Q u J *
            partitionOn β (field (mixtureCoefficients μ) J)
              (overlapRegion u (Icc (q-b) (q+b)))
            ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k))) /
          (∫ J, intrinsicDet μ Q u J
            ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k))))) =
      ENNReal.ofReal
        (SourceMixedAllCriticalIntensityEnvelope.sourceAllCriticalPhysicalEnergyDensity
          d μ Q L R H *
          sourceMixedEnergyPalmBandExpectation d μ Q β (H/(d+2:ℕ))
            L R q b u hu) := by
  let e := H/(d+2:ℕ)
  let W := sourceAllCriticalRadialWeight d μ Q e
  let G := fun k : ℝ =>
    ((∫ J, intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b)))
      ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
    (∫ J, intrinsicDet μ Q u J
      ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))))
  let F := sourcePhysicalRadialFactor d μ Q
  have hF : 0 ≤ F := (sourcePhysicalRadialFactor_pos d μ hQ hnp).le
  have hW (k : ℝ) : 0 ≤ W k :=
    sourceAllCriticalRadialWeight_nonneg d μ Q e k
  have hG (k : ℝ) (hk : k ∈ Ioo L R) : 0 ≤ G k := by
    have hb : 0 < Q^2*μ.xi2 Q :=
      mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
    have hDen : 0 < ∫ J, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k)) := by
      rw [determinant_mean_eq_of_law
        (mixed_intrinsicDet_hasLaw μ hQ hnp u hu (scorePairEquiv (e,k)))]
      simp [scorePairEquiv_apply]
      exact GOEPhysicalNormalizedMoments.physicalMean_pos d 1 hb
        (hEdge.trans hk.1)
    exact div_nonneg
      (integral_nonneg (fun J => mul_nonneg (abs_nonneg _)
        (integral_nonneg (fun _ => (Real.exp_pos _).le)))) hDen.le
  have hScore (k : ℝ) :
      mixedCriticalPhysicalIntensity d μ Q H k =
        ENNReal.ofReal (F*W k) := by
    have hdim : (((d+2:ℕ):ℝ))*e = H := by
      dsimp [e]
      field_simp
    have hh := mixedCriticalPhysicalIntensity_eq_sourceAllCriticalRadialWeight
      d μ hQ hnp e k
    have hne := SourceMixedAllCriticalIntensityEnvelope.mixedCriticalPhysicalIntensity_ne_top
      d μ Q (((d+2:ℕ):ℝ)*e) k
    rw [← hdim]
    calc
      mixedCriticalPhysicalIntensity d μ Q (((d+2:ℕ):ℝ)*e) k =
          ENNReal.ofReal
            (mixedCriticalPhysicalIntensity d μ Q (((d+2:ℕ):ℝ)*e) k).toReal :=
        (ENNReal.ofReal_toReal hne).symm
      _ = ENNReal.ofReal (F*W k) := congrArg ENNReal.ofReal hh
  have hInt : IntegrableOn (fun k => G k*W k) (Ioo L R) := hRatioInt
  have hRadial : (∫⁻ k in Ioo L R, ENNReal.ofReal (G k*W k)) =
      ENNReal.ofReal (∫ k in Ioo L R, G k*W k) := by
    exact (ofReal_integral_eq_lintegral_ofReal hInt
      (ae_restrict_of_forall_mem measurableSet_Ioo
        (fun k hk => mul_nonneg (hG k hk) (hW k)))).symm
  have hPalm := physical_allcritical_density_mul_bandPalm_eq_radial_numerator
    d μ hQ β e L R q b hEdge hLR u hu
  change (F*(∫ k in Ioo L R,W k)) *
      sourceMixedEnergyPalmBandExpectation d μ Q β e L R q b u hu =
      F * ∫ k in Ioo L R, G k*W k at hPalm
  calc
    (∫⁻ k in Ioo L R,
      mixedCriticalPhysicalIntensity d μ Q H k * ENNReal.ofReal (G k)) =
        ∫⁻ k in Ioo L R, ENNReal.ofReal F *
          ENNReal.ofReal (G k*W k) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
      rw [hScore k,ENNReal.ofReal_mul hF,
        ENNReal.ofReal_mul (hG k hk)]
      ac_rfl
    _ = ENNReal.ofReal F *
        ENNReal.ofReal (∫ k in Ioo L R, G k*W k) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hRadial]
    _ = ENNReal.ofReal
        (SourceMixedAllCriticalIntensityEnvelope.sourceAllCriticalPhysicalEnergyDensity
          d μ Q L R H *
          sourceMixedEnergyPalmBandExpectation d μ Q β e L R q b u hu) := by
      rw [← ENNReal.ofReal_mul hF]
      rw [← hPalm]
      rfl

end
end SlowEquilibration.SphericalTAPMixedMarkedPalmRadial
