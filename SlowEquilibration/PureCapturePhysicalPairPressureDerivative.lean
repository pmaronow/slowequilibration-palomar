-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPairPressureIdentity

/-! The finite-volume Gibbs pair covariance is the fluctuation term in
the temperature derivative of the quenched pressure. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPairPressureDerivative

open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalPairPressureIdentity
open PureCapturePhysicalFullOverlapArray
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem physicalPairCovarianceMean_eq_gaussianReplicaCovariance
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) :
    (∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
      (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))) =
    ∫ g : EuclideanDisorder (n+2) μ.maxDegree,
      replicaCovariance (mixtureCoefficients μ) β g
        ∂SYK.standardGaussianMeasureOnEuclidean
          (Coordinate (n+2) μ.maxDegree) := by
  rw [physicalPairCovarianceMean_eq_disorderIntegral]
  have hi := replicaCovariance_gaussian_integrable
    (N := n+2) (P := μ.maxDegree) (by omega)
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) β
  have h := (euclideanDisorder_hasLaw (n+2) μ.maxDegree).integral_comp
    hi.aestronglyMeasurable
  rw [← h]
  apply integral_congr_ae
  exact .of_forall fun J => by
    simp only [Function.comp_apply, replicaCovariance, covariancePolynomial_mixture,
      unpack_euclideanDisorder]

theorem quenchedPressure_deriv_eq_physicalPairCovarianceMean
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) :
    deriv (quenchedPressure (n+2) μ) β =
      β * (μ.xi 1 -
        ∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
          (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))) := by
  rw [quenchedPressure_deriv_replicaCovariance (by omega) μ β]
  rw [physicalPairCovarianceMean_eq_gaussianReplicaCovariance]

end SlowEquilibration.PureCapturePhysicalPairPressureDerivative
