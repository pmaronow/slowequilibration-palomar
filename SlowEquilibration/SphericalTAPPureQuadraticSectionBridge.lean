-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPurePalmCoareaReal
public import SlowEquilibration.SphericalTAPMixedPalmLatitudeMeasurable
public import SlowEquilibration.SphericalTAPCriticalPureLatitudeVariance

@[expose] public section

/-! The exact handoff from the source's determinant–quadratic latitude
section to the physical coarea density.  The only statistical premise is
the printed determinant-weighted angular expectation bound. -/

namespace SlowEquilibration.SphericalTAPPureQuadraticSectionBridge
noncomputable section
open MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPMixedPalmLatitudeMeasurable SphericalTAPCriticalPureLatitudeVariance
open GOEPhysicalPotential
open scoped ENNReal
set_option autoImplicit false

/-- Multiplying the genuine determinant–latitude expectation by the exact
physical Jacobian retains the printed bound with no hidden normalization. -/
theorem pure_quadratic_section_to_coarea_density
    (d : ℕ) (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q β e a C : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hquad : let μ := FiniteMixture.pure p hp alpha halpha

      (∫⁻ J, ENNReal.ofReal
        (intrinsicDet μ Q u J *
          partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
            (field (mixtureCoefficients μ) J))
        ∂pureLaw p hp alpha halpha Q u hu e) ≤
      ENNReal.ofReal (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
        Real.exp (((d+2:ℕ):ℝ)*(β*e*(a/Real.sqrt Q)^p+β^2/2*sourcePureLatitudeVariance p alpha a)))) :
    let μ := FiniteMixture.pure p hp alpha halpha
    (∫⁻ J, ENNReal.ofReal
      (intrinsicDet μ Q u J *
        latitudeDensityPartition (d+1) β
          (field (mixtureCoefficients μ) J) u a)
      ∂pureLaw p hp alpha halpha Q u hu e) ≤
      ENNReal.ofReal ((Real.sqrt (1-a^2))^(d-1) *
        (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
          Real.exp (((d+2:ℕ):ℝ)*(β*e*(a/Real.sqrt Q)^p+β^2/2*sourcePureLatitudeVariance p alpha a)))) := by
  dsimp only at hquad ⊢
  let μ := FiniteMixture.pure p hp alpha halpha
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
  change (∫⁻ J, ENNReal.ofReal
      (intrinsicDet μ Q u J *
        latitudeDensityPartition (d+1) β
          (field (mixtureCoefficients μ) J) u a)
      ∂pureLaw p hp alpha halpha Q u hu e) ≤
    ENNReal.ofReal (W * (C * physicalMean d (d+2)
      (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
        Real.exp (((d+2:ℕ):ℝ)*
          (β*e*(a/Real.sqrt Q)^p+β^2/2*sourcePureLatitudeVariance p alpha a))))
  simp_rw [hpoint, ENNReal.ofReal_mul hW]
  rw [lintegral_const_mul _ hFm]
  gcongr

end
end SlowEquilibration.SphericalTAPPureQuadraticSectionBridge
