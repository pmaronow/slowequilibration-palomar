-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedMarkedPhysicalEnergyDisintegration

@[expose] public section

/-! Identification of the actual marked Kac--Rice integrand with its
all-critical physical intensity and determinant-weighted Palm ratio. -/

namespace SlowEquilibration.SphericalTAPMixedMarkedPalmIntegrand
noncomputable section
open MeasureTheory Set SphericalModel SphericalGaussianJet
open SphericalMarkedWindows SphericalSequentialRegression
open ConditionedDeterminantMoments GOEPhysicalPotential
open GOEPhysicalNormalizedMoments
open SphericalTAPMixedLowSumMarkedKR
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- At a radial score above the GOE edge, the unnormalized marked
conditional Kac--Rice density is exactly the all-critical intensity times
the true determinant-weighted whole-field Palm expectation. -/
theorem physical_marked_density_eq_intensity_mul_palm_ratio
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (β q b H k : ℝ)
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hInt : Integrable (fun J : Disorder (d+2) μ.maxDegree =>
      intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b))))
      (mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k)))) :
    sphereKRPrefactor (d+1) μ Q *
      (ENNReal.ofReal (((d+2:ℕ):ℝ))⁻¹ *
        (physicalScorePdf (d+2) μ Q
          (scorePairEquiv (H/(d+2:ℕ),k)) *
          ∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) *
            sourceMixedBandMark d μ β q b J u
            ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k)))) =
    mixedCriticalPhysicalIntensity d μ Q H k *
      ENNReal.ofReal
        ((∫ J, intrinsicDet μ Q u J *
            partitionOn β (field (mixtureCoefficients μ) J)
              (overlapRegion u (Icc (q-b) (q+b)))
            ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k))) /
          (∫ J, intrinsicDet μ Q u J
            ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k)))) := by
  let P := mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k))
  let D := intrinsicDet μ Q u
  let Z := fun J : Disorder (d+2) μ.maxDegree =>
    partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u (Icc (q-b) (q+b)))
  let num := ∫ J, D J*Z J ∂P
  let den := ∫ J, D J ∂P
  have hD (J : Disorder (d+2) μ.maxDegree) : 0 ≤ D J := abs_nonneg _
  have hZ (J : Disorder (d+2) μ.maxDegree) : 0 ≤ Z J := by
    dsimp [Z]
    exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hnum : 0 ≤ num := integral_nonneg (fun J => mul_nonneg (hD J) (hZ J))
  have hdeneq : den = physicalMean d (d+2) (Q^2*μ.xi2 Q) k := by
    dsimp [den,P,D]
    rw [determinant_mean_eq_of_law
      (mixed_intrinsicDet_hasLaw μ hQ hnp u hu
        (scorePairEquiv (H/(d+2:ℕ),k)))]
    simp [scorePairEquiv_apply]
  have hb : 0 < Q^2*μ.xi2 Q :=
    mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hden : 0 < den := by
    rw [hdeneq]
    exact physicalMean_pos d 1 hb hk
  have hprod : den*(num/den)=num := mul_div_cancel₀ num hden.ne'
  change Integrable (fun J => D J * Z J) P at hInt
  have hli :
      (∫⁻ J, ENNReal.ofReal (D J) * ENNReal.ofReal (Z J) ∂P) =
        ENNReal.ofReal num := by
    calc
      _ = ∫⁻ J, ENNReal.ofReal (D J * Z J) ∂P := by
        apply lintegral_congr
        intro J
        exact (ENNReal.ofReal_mul (hD J)).symm
      _ = ENNReal.ofReal num :=
        (ofReal_integral_eq_lintegral_ofReal hInt
          (.of_forall (fun J => mul_nonneg (hD J) (hZ J)))).symm
  have hcrit : mixedCriticalPhysicalIntensity d μ Q H k =
      ENNReal.ofReal (((d+2:ℕ):ℝ))⁻¹ *
        (sphereKRPrefactor (d+1) μ Q *
          physicalScorePdf (d+2) μ Q
            (scorePairEquiv (H/(d+2:ℕ),k)) *
          ENNReal.ofReal den) := by
    rw [hdeneq]
    unfold mixedCriticalPhysicalIntensity mixedCriticalIntensity
    simp [scorePairEquiv_apply]
  have hnumfactor : ENNReal.ofReal num =
      ENNReal.ofReal den * ENNReal.ofReal (num/den) := by
    rw [← ENNReal.ofReal_mul hden.le,hprod]
  change sphereKRPrefactor (d+1) μ Q *
    (ENNReal.ofReal (((d+2:ℕ):ℝ))⁻¹ *
      (physicalScorePdf (d+2) μ Q (scorePairEquiv (H/(d+2:ℕ),k)) *
        ∫⁻ J, ENNReal.ofReal (D J) * ENNReal.ofReal (Z J) ∂P)) =
    mixedCriticalPhysicalIntensity d μ Q H k * ENNReal.ofReal (num/den)
  rw [hli,hnumfactor,hcrit]
  ac_rfl

end
end SlowEquilibration.SphericalTAPMixedMarkedPalmIntegrand
