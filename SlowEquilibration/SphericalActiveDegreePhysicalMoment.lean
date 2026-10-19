-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalActiveDegreePhysicalPressure
public import SlowEquilibration.SphericalPureProbePhysicalPressureResponse

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreePhysicalMoment

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalActiveDegreeKernel
open SphericalActiveDegreePhysicalPressure
open SphericalPureProbePhysicalMomentTransfer
open PureCapturePhysicalPairPowerIdentity
open PureCapturePhysicalFullOverlapArray
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging GaussianPerturbationResponse
open GaussianSelectedReplicaTrace
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem activeDegree_one_pairPower_eq_physical
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) (p : Degree μ.maxDegree) :
    (∫ g : EuclideanDisorder (n+2) μ.maxDegree,
      (∫ z : Vector (n+2) × Vector (n+2), (overlap z.1 z.2)^p.val.val
        ∂(gibbsMeasure (sphereLaw (n+2))
          (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
            (activeDegreeLabel p) 1) g).prod
          (gibbsMeasure (sphereLaw (n+2))
            (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
              (activeDegreeLabel p) 1) g))
      ∂SYK.standardGaussianMeasureOnEuclidean _) =
      ∫ c, (c 0 1)^p.val.val ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)) := by
  let F : Disorder (n+2) μ.maxDegree → ℝ := fun J =>
    ∫ z : Vector (n+2) × Vector (n+2), (overlap z.1 z.2)^p.val.val
      ∂(gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)).prod
        (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J))
  have hF := (physical_pairPower_disorder_measurable_bounded (N := n+2)
    (by omega) μ β p.val.val).1
  have hdis := unpackDisorder_hasLaw (n+2) μ.maxDegree
  have hint := hdis.integral_comp hF.aestronglyMeasurable
  calc
    _ = ∫ g : EuclideanDisorder (n+2) μ.maxDegree,
          F (unpackDisorder g) ∂SYK.standardGaussianMeasureOnEuclidean _ := by
      apply integral_congr_ae
      exact .of_forall fun g => by
        change (∫ z : Vector (n+2) × Vector (n+2),
          (overlap z.1 z.2)^p.val.val
            ∂(gibbsMeasure (sphereLaw (n+2))
              (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
                (activeDegreeLabel p) 1) g).prod
              (gibbsMeasure (sphereLaw (n+2))
                (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
                  (activeDegreeLabel p) 1) g)) = F (unpackDisorder g)
        rw [activeDegreeGibbs_one_eq_original]
    _ = ∫ J, F J ∂disorderLaw (n+2) μ.maxDegree := by
      simpa only [Function.comp_def] using hint
    _ = _ := (physicalPairPower_eq_disorderIntegral μ β n p.val.val).symm

end SlowEquilibration.SphericalActiveDegreePhysicalMoment
