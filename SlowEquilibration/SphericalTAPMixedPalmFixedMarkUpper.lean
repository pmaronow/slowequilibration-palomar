-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmCoareaReal

@[expose] public section

/-! Source-faithful fixed-mark reduction of the physical Palm band to the
printed determinant–quadratic latitude section estimate. -/

namespace SlowEquilibration.SphericalTAPMixedPalmFixedMarkUpper
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPMixedBandExponent SphericalTAPMixedLatitudeSmooth
open SphericalTAPMixedPalmCoareaReal
open SphericalTAPMixedQuadraticSectionBridge GOEPhysicalPotential
set_option autoImplicit false

/-- The actual physical determinant-weighted band expectation is bounded
by the manuscript's annealed latitude integral, and is integrable, once the
printed quadratic-correlation estimate holds at each latitude. -/
theorem mixed_fixed_mark_physical_band_upper_of_quadratic_sections
    (d : ℕ) (hd : 1 ≤ d) (μ : FiniteMixture)
    (Q β e k C : ℝ) (hC : 0 ≤ C)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    {q b : ℝ} (hb : 0 ≤ b) (hbelow : -1 < q-b) (habove : q+b < 1)
    (hquad : ∀ a ∈ Icc (q-b) (q+b),
      (∫⁻ J, ENNReal.ofReal
        (intrinsicDet μ Q u J *
          partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
            (field (mixtureCoefficients μ) J))
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      ENNReal.ofReal (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a))) :
    let B := fun a : ℝ => (Real.sqrt (1-a^2))^(d-1) *
      (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a))
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
  dsimp only
  let B := fun a : ℝ => (Real.sqrt (1-a^2))^(d-1) *
    (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
      Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a))
  have hBcont : Continuous B := by
    have hm := (sourceMixedMean_smooth μ Q e k).continuous
    have hv := (sourceMixedVariance_smooth μ Q).continuous
    dsimp [B,sourceMixedXi]
    fun_prop
  have hBint : IntegrableOn B (Icc (q-b) (q+b)) :=
    hBcont.continuousOn.integrableOn_compact isCompact_Icc
  have hdN : 0 ≤ physicalMean d (d+2) (Q^2*μ.xi2 Q) k := by
    unfold physicalMean
    exact integral_nonneg (fun _ => abs_nonneg _)
  have hB0 : ∀ a ∈ Icc (q-b) (q+b), 0 ≤ B a := by
    intro a _
    dsimp [B]
    positivity
  have hsection : ∀ a ∈ Icc (q-b) (q+b),
      (∫⁻ J, ENNReal.ofReal
        (intrinsicDet μ Q u J *
          latitudeDensityPartition (d+1) β
            (field (mixtureCoefficients μ) J) u a)
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      ENNReal.ofReal (B a) := by
    intro a ha
    exact mixed_quadratic_section_to_coarea_density
      d μ Q β e k a C u hu (hquad a ha)
  exact mixed_weighted_band_integral_le_sections
    d hd μ Q β e k u hu hb hbelow habove
    B hBint hB0 hsection

end
end SlowEquilibration.SphericalTAPMixedPalmFixedMarkUpper
