-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalWienerRotationFiltration
public import SlowEquilibration.SphericalWienerRotationPathLaw
public import SlowEquilibration.SphericalRotatedNoiseIntegrability

/-! The canonical orthogonal path sampler is filtered for the actual
null-augmented Wiener filtration, and yields a genuine rotated driver
there whenever its measure-preserving law has been established. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open MeasureTheory ProbabilityTheory StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics
open SphericalAging.BrownianDriverPullback
open SphericalModel SphericalWienerRotation
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 900000

variable {N : ℕ}

theorem rotateWiener_measurePreserving
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    MeasurePreserving (rotateWiener U)
      (VectorBrownian.law N) (VectorBrownian.law N) :=
  ⟨rotateWiener_measurable U,
    SphericalWienerRotationPathLaw.rotateWiener_law U⟩

theorem rotateWiener_natural_pullback_filtration
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    BrownianDriverPullback.filtration (VectorBrownian.filtration N)
      (rotateWiener_measurable U) = VectorBrownian.filtration N := by
  apply Filtration.ext
  funext t
  exact rotateWiener_filtration_eq U t

theorem castBrownianDriver_coordinate
    {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {F G : Filtration ℝ≥0 m} (hFG : F = G)
    (D : BrownianDriver N P F) (j : Fin N) (t : ℝ≥0) (ω : Ω) :
    (hFG ▸ D).coordinate j t ω = D.coordinate j t ω := by
  cases hFG
  rfl

theorem rotateWiener_augmented_filtered
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (hφ : MeasurePreserving (rotateWiener U)
      (VectorBrownian.law N) (VectorBrownian.law N))
    (t : ℝ≥0) :
    @Measurable _ _
      (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) t)
      (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) t)
      (rotateWiener U) := by
  have hraw := BrownianDriverPullback.augmented_filtered
    (F := VectorBrownian.filtration N) hφ t
  rw [rotateWiener_natural_pullback_filtration U] at hraw
  exact hraw

def rotatedCanonicalDriver
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (hφ : MeasurePreserving (rotateWiener U)
      (VectorBrownian.law N) (VectorBrownian.law N)) :
    BrownianDriver N (VectorBrownian.law N)
      (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)) :=
  NullAugmentation.driver
    ((rotateWiener_natural_pullback_filtration U) ▸
      BrownianDriverPullback.driver (VectorBrownian.driver N) hφ)

theorem rotatedCanonicalDriver_coordinate
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (hφ : MeasurePreserving (rotateWiener U)
      (VectorBrownian.law N) (VectorBrownian.law N))
    (j : Fin N) (t : ℝ≥0) (ω : VectorBrownian.Space N) :
    (rotatedCanonicalDriver U hφ).coordinate j t ω =
      (VectorBrownian.driver N).coordinate j t (rotateWiener U ω) := by
  unfold rotatedCanonicalDriver
  exact castBrownianDriver_coordinate (rotateWiener_natural_pullback_filtration U)
    (BrownianDriverPullback.driver (VectorBrownian.driver N) hφ) j t ω

theorem rotatedCanonicalDriver_coordinate_mix
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (hφ : MeasurePreserving (rotateWiener U)
      (VectorBrownian.law N) (VectorBrownian.law N))
    (j : Fin N) (t : ℝ≥0) (ω : VectorBrownian.Space N) :
    (rotatedCanonicalDriver U hφ).coordinate j t ω =
      ∑ i : Fin N, (U (basisVector i)) j *
        (NullAugmentation.driver (VectorBrownian.driver N)).coordinate i t ω := by
  rw [rotatedCanonicalDriver_coordinate U hφ]
  change (rotateWiener U ω) j t = _
  rw [rotateWiener_eval,rotated_coordinate_sum]
  rfl

end SlowEquilibration.SphericalRotationCovariance
