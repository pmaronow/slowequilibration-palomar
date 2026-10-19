-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedBandScaleIdentity
public import SlowEquilibration.SphericalTAPCriticalEnergyPalmAverage
public import SlowEquilibration.SphericalTAPLatitudeLIntegralChange

@[expose] public section

/-! Joint Borel regularity of the literal latitude section under the
critical-point posterior.  This is the Tonelli input for the physical Palm
band expectation. -/

namespace SlowEquilibration.SphericalTAPMixedPalmLatitudeMeasurable
noncomputable section
open MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
set_option autoImplicit false

/-- The actual original-field angular partition is jointly measurable in
the tensor disorder and physical latitude. -/
theorem mixed_latitude_partition_joint_measurable
    (d : ℕ) (μ : FiniteMixture) (u : Vector (d+2)) (β : ℝ) :
    Measurable (fun z : Disorder (d+2) μ.maxDegree × ℝ =>
      partitionAgainst (latitudeLaw u (latitudeFrameAt u) z.2) β
        (field (mixtureCoefficients μ) z.1)) := by
  let n := d+1
  let e := latitudeFrameAt u
  have hpoint : Continuous (fun z :
      (Disorder (d+2) μ.maxDegree × ℝ) × Vector (d+1) =>
      Real.exp (β*field (mixtureCoefficients μ) z.1.1
        (latitudeMap u e z.1.2 z.2))) := by
    have hf := field_jointContinuous (N := d+2) (mixtureCoefficients μ)
    unfold latitudeMap
    fun_prop
  have hm := hpoint.stronglyMeasurable.integral_prod_right'
    (ν := sphereLaw n) |>.measurable
  convert hm using 1
  funext z
  exact latitudePartition_eq_sphereIntegral
    (mixtureCoefficients μ) β z.1 u e z.2

/-- The literal determinant times latitude density is jointly measurable,
including the coarea Jacobian weight. -/
theorem mixed_determinant_latitude_density_joint_measurable
    (d : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) (β : ℝ) :
    Measurable (fun z : Disorder (d+2) μ.maxDegree × ℝ =>
      intrinsicDet μ Q u z.1 *
        latitudeDensityPartition (d+1) β
          (field (mixtureCoefficients μ) z.1) u z.2) := by
  have hD : Measurable (intrinsicDet μ Q u) := by
    unfold intrinsicDet
    have hm := (SphericalMarkedWindows.intrinsicDet_measurable
      (centerCoefficients (mixtureCoefficients μ) Q) u hu).ennreal_toReal
    convert hm using 1
    ext J
    exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
  have hsection := mixed_latitude_partition_joint_measurable d μ u β
  unfold latitudeDensityPartition
  fun_prop

end
end SlowEquilibration.SphericalTAPMixedPalmLatitudeMeasurable
