-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmSourceUpper

@[expose] public section

/-! The exact handoff from the source's determinant–quadratic latitude
section to the physical coarea density.  The only statistical premise is
the printed determinant-weighted angular expectation bound. -/

namespace SlowEquilibration.SphericalTAPMixedQuadraticSectionBridge
noncomputable section
open MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPMixedPalmLatitudeMeasurable SphericalTAPMixedBandExponent
open GOEPhysicalPotential
open scoped ENNReal
set_option autoImplicit false

/-- Multiplying the genuine determinant–latitude expectation by the exact
physical Jacobian retains the printed bound with no hidden normalization. -/
theorem mixed_quadratic_section_to_coarea_density
    (d : ℕ) (μ : FiniteMixture) (Q β e k a C : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hquad :
      (∫⁻ J, ENNReal.ofReal
        (intrinsicDet μ Q u J *
          partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
            (field (mixtureCoefficients μ) J))
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      ENNReal.ofReal (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a))) :
    (∫⁻ J, ENNReal.ofReal
      (intrinsicDet μ Q u J *
        latitudeDensityPartition (d+1) β
          (field (mixtureCoefficients μ) J) u a)
      ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      ENNReal.ofReal ((Real.sqrt (1-a^2))^(d-1) *
        (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
          Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a))) := by
  let W : ℝ := (Real.sqrt (1-a^2))^(d-1)
  let F := fun J : Disorder (d+2) μ.maxDegree =>
    intrinsicDet μ Q u J *
      partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
        (field (mixtureCoefficients μ) J)
  have hW : 0 ≤ W := pow_nonneg (Real.sqrt_nonneg _) _
  have hFm : Measurable (fun J => ENNReal.ofReal (F J)) := by
    have hP : Measurable (fun J : Disorder (d+2) μ.maxDegree =>
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
          (field (mixtureCoefficients μ) J)) :=
      (mixed_latitude_partition_joint_measurable d μ u β).comp
        (measurable_id.prodMk measurable_const)
    have hD : Measurable (intrinsicDet μ Q u) := by
      unfold intrinsicDet
      have hm := (SphericalMarkedWindows.intrinsicDet_measurable
        (centerCoefficients (mixtureCoefficients μ) Q) u hu).ennreal_toReal
      convert hm using 1
      ext J
      exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
    exact (hD.mul hP).ennreal_ofReal
  have hpoint (J : Disorder (d+2) μ.maxDegree) :
      intrinsicDet μ Q u J *
        latitudeDensityPartition (d+1) β
          (field (mixtureCoefficients μ) J) u a = W*F J := by
    unfold latitudeDensityPartition F W
    simp only [show d+1-2=d-1 by omega]
    ring
  simp_rw [hpoint, ENNReal.ofReal_mul hW]
  rw [lintegral_const_mul _ hFm]
  rw [ENNReal.ofReal_mul hW]
  gcongr

end
end SlowEquilibration.SphericalTAPMixedQuadraticSectionBridge
