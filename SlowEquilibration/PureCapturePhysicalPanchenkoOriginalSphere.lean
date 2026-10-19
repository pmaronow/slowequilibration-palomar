-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPanchenkoActualDeviation

/-! The shell-subtype form of the two-stage energy deviation is exactly the
manuscript's original spherical Gibbs expectation for each tensor disorder. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoOriginalSphere

open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalShellGG
open PureCapturePhysicalPanchenkoActualDeviation
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem physical_shell_deviation_eq_original_sphere
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    meanAbsoluteEnergyDeviation (shellLaw N)
      (shellLinear (mixtureCoefficients μ)) (fun _ => true) β =
    ∫ g : EuclideanDisorder N μ.maxDegree,
      (∫ x : Vector N,
        |field (mixtureCoefficients μ) (unpackDisorder g) x -
          meanScore (shellLaw N)
            (shellLinear (mixtureCoefficients μ)) (fun _ => true) β|
          ∂gibbsLaw N β
            (field (mixtureCoefficients μ) (unpackDisorder g)))
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree) := by
  let c := mixtureCoefficients μ
  let L := shellLinear (N := N) c
  let e := meanScore (shellLaw N) L (fun _ => true) β
  unfold meanAbsoluteEnergyDeviation
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  have hop : parameterOperator (fun _ : Coordinate N μ.maxDegree => true) β g =
      β • g := by
    ext i
    simp [parameterOperator, coordinateMask, diagonal_apply]
  have hmap :
      (gibbsMeasure (shellLaw N) L
        (parameterOperator (fun _ => true) β g)).map
          (Subtype.val : Shell N → Vector N) =
        gibbsLaw N β (field c (unpackDisorder g)) := by
    have heq : gibbsMeasure (shellLaw N) L
        (parameterOperator (fun _ => true) β g) =
        gibbsMeasure (shellLaw N)
          (parameterLinear L (fun _ => true) β) g := by
      apply gibbsMeasure_congr_field
      exact .of_forall fun v => by
        simp only [L, parameterLinear, ContinuousLinearMap.comp_apply]
    rw [heq]
    simpa only [L, c] using shellGibbsLaw_map hN μ β g
  have hf : Measurable (fun x : Vector N =>
      |field c (unpackDisorder g) x-e|) :=
    ((field_contDiff c (unpackDisorder g)).continuous.measurable.sub_const e).abs
  change (∫ v : Shell N,
      |L v (coordinateMask (fun _ => true) true g)-e|
        ∂gibbsMeasure (shellLaw N) L
          (parameterOperator (fun _ => true) β g)) =
    ∫ x : Vector N, |field c (unpackDisorder g) x-e|
      ∂gibbsLaw N β (field c (unpackDisorder g))
  rw [← hmap, integral_map measurable_subtype_coe.aemeasurable
    hf.aestronglyMeasurable]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  have hmask : coordinateMask (fun _ : Coordinate N μ.maxDegree => true)
      true g = g := by
    ext i
    simp [coordinateMask, diagonal_apply]
  rw [hmask]
  exact congrArg (fun t : ℝ => |t-e|) (sphereLinear_apply c v.val g)

end SlowEquilibration.PureCapturePhysicalPanchenkoOriginalSphere
