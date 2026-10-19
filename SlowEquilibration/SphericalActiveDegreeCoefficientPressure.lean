-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalActiveDegreeScaledField

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreeCoefficientPressure

open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalActiveDegreeKernel
open SphericalActiveDegreePhysicalPressure SphericalActiveDegreeScaledField
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The active-degree parameter pressure is the ordinary spherical Gaussian
pressure of the coefficient family with c_p replaced by c_p s². The identity
holds at every finite dimension and for every nonnegative amplitude. -/
theorem activeDegreePressure_eq_scaledCoefficientPressure
    {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (p : Degree μ.maxDegree) (s : ℝ) (hs : 0 ≤ s) :
    activeDegreePressure N μ β p s =
      averagedLogPartition (sphereLaw N)
        (sphereLinear (scaleCoefficients (mixtureCoefficients μ) p s)) β /
          (N : ℝ) := by
  unfold activeDegreePressure parameterMean parameterLogPartition
    averagedLogPartition
  congr 1
  apply integral_congr_ae
  exact .of_forall fun g => by
    unfold GaussianSpinInterpolation.logPartition
      GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
    dsimp only
    congr 1
    apply integral_congr_ae
    exact .of_forall fun x => by
      dsimp only
      simp only [one_mul]
      change Real.exp
        (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
          (activeDegreeLabel p) s x g) =
          Real.exp (sphereLinear (scaleCoefficients (mixtureCoefficients μ) p s) x
            (β • g))
      rw [activeDegree_parameterLinear_eq_scaled
        (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) β p s hs x g]
      simp only [activeDegreeLinear,scaledLinear,smul_apply,map_smul,smul_eq_mul]

end SlowEquilibration.SphericalActiveDegreeCoefficientPressure
