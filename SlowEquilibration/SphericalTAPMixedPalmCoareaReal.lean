-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedQuadraticSectionBridge

@[expose] public section

/-! Real-valued fixed-mark version of the exact physical Palm coarea
inequality, with integrability exposed so the Lean Bochner integral cannot
silently default to zero. -/

namespace SlowEquilibration.SphericalTAPMixedPalmCoareaReal
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPMixedPalmCoarea
open scoped ENNReal
set_option autoImplicit false

theorem mixed_weighted_band_integral_le_sections
    (d : ℕ) (hd : 1 ≤ d) (μ : FiniteMixture) (Q β e k : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    {q b : ℝ} (hb : 0 ≤ b) (hbelow : -1 < q-b) (habove : q+b < 1)
    (B : ℝ → ℝ)
    (hBint : IntegrableOn B (Icc (q-b) (q+b)))
    (hB0 : ∀ a ∈ Icc (q-b) (q+b), 0 ≤ B a)
    (hsection : ∀ a ∈ Icc (q-b) (q+b),
      (∫⁻ J, ENNReal.ofReal
        (intrinsicDet μ Q u J *
          latitudeDensityPartition (d+1) β
            (field (mixtureCoefficients μ) J) u a)
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
          ENNReal.ofReal (B a)) :
    Integrable (fun J => intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b))))
      (mixedLaw μ Q u hu (scorePairEquiv (e,k))) ∧
    (∫ J, intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b)))
      ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      (latitudeNormalization (d+1)).toReal *
        ∫ a in Icc (q-b) (q+b), B a ∂volume := by
  let ν := mixedLaw μ Q u hu (scorePairEquiv (e,k))
  let A := Icc (q-b) (q+b)
  let Z := fun J : Disorder (d+2) μ.maxDegree =>
    intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u A)
  have hZ0 : ∀ J, 0 ≤ Z J := by
    intro J
    exact mul_nonneg (abs_nonneg _) (partitionOn_nonneg β _ _)
  have hZmeas : Measurable Z := by
    have hD : Measurable (intrinsicDet μ Q u) := by
      unfold intrinsicDet
      have hm := (SphericalMarkedWindows.intrinsicDet_measurable
        (SphericalGaussianJet.centerCoefficients
          (mixtureCoefficients μ) Q) u hu).ennreal_toReal
      convert hm using 1
      ext J
      exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
    exact hD.mul (SphericalTAPCriticalBandSectionBridge.sourceBandPartition_measurable
      (d+1) μ u A measurableSet_Icc β)
  have hBae : ∀ᵐ a ∂volume.restrict A, 0 ≤ B a := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    exact hB0 a ha
  have hBrepr : ENNReal.ofReal (∫ a in A, B a ∂volume) =
      ∫⁻ a in A, ENNReal.ofReal (B a) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hBint hBae
  have hraw := mixed_weighted_band_lintegral_le_sections
    d hd μ Q β e k u hu hb hbelow habove
    (fun a => ENNReal.ofReal (B a)) hsection
  rw [← hBrepr] at hraw
  have hfinite : latitudeNormalization (d+1) *
      ENNReal.ofReal (∫ a in Icc (q-b) (q+b), B a ∂volume) ≠ ⊤ :=
    ENNReal.mul_ne_top (latitudeNormalization_ne_top _) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfinite hraw
  have hZfinite : (∫⁻ J, ENNReal.ofReal (Z J) ∂ν) < ⊤ :=
    lt_of_le_of_lt hraw (lt_top_iff_ne_top.mpr hfinite)
  have hZint : Integrable Z ν :=
    ⟨hZmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (.of_forall hZ0)).mpr hZfinite⟩
  have hZrepr : ENNReal.ofReal (∫ J, Z J ∂ν) =
      ∫⁻ J, ENNReal.ofReal (Z J) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal hZint (.of_forall hZ0)
  rw [← hZrepr] at hreal
  have hNZ : 0 ≤ ∫ J, Z J ∂ν := integral_nonneg_of_ae (.of_forall hZ0)
  have hNB : 0 ≤ ∫ a in A, B a ∂volume := integral_nonneg_of_ae hBae
  rw [ENNReal.toReal_ofReal hNZ,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hNB] at hreal
  exact ⟨hZint,by simpa only [Z,ν,A] using hreal⟩

end
end SlowEquilibration.SphericalTAPMixedPalmCoareaReal
