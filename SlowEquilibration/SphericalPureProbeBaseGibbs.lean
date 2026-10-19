-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureProbeFiniteResponse
public import SlowEquilibration.GaussianFeatureEndpoints

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalPureProbeBaseGibbs

open Set MeasureTheory ProbabilityTheory
open SphericalModel GaussianFeatureDirac
open GaussianSpinComparison GaussianSpinInterpolation
open GaussianPerturbationParameter GaussianPerturbationSelfAveraging
open SphericalPureProbeSelectedKernel SphericalPureProbeFiniteResponse
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The zero-amplitude held pure-spin bank leaves exactly the source
spherical Hamiltonian on the original Gaussian coordinates. -/
theorem sourcePureProbeLinear_zero_eq_original
    {N p : ℕ} (hp : 2 ≤ p) (μ : FiniteMixture) (β : ℝ)
    (w : EuclideanSpace ℝ
      (ThreeCoordinate N (Coordinate N μ.maxDegree)
        (Coordinate N (pureProbe p hp).maxDegree)))
    (x : Vector N) :
    sourcePureProbeLinear N p hp μ β x
        (parameterOperator heldLabel 0 w) =
      sphereLinear (mixtureCoefficients μ) x
        (β • SphericalModel.projectGaussian Sum.inl (threeLeft w)) := by
  unfold sourcePureProbeLinear
  rw [threeLinear_parameter]
  simp only [zero_mul,add_zero]
  rw [twoLinear_rotation_zero]
  rfl

/-- Pointwise equality of the enlarged-bank zero-probe Gibbs law with
the original physical Gibbs law after projection of the Gaussian bank. -/
theorem sourcePureProbeGibbs_eq_original
    {N p : ℕ} (hp : 2 ≤ p) (μ : FiniteMixture) (β : ℝ)
    (w : EuclideanSpace ℝ
      (ThreeCoordinate N (Coordinate N μ.maxDegree)
        (Coordinate N (pureProbe p hp).maxDegree))) :
    sourcePureProbeGibbs N p hp μ β w =
      gibbsLaw N β (field (mixtureCoefficients μ)
        (unpackDisorder (SphericalModel.projectGaussian Sum.inl (threeLeft w)))) := by
  let g : EuclideanDisorder N μ.maxDegree :=
    SphericalModel.projectGaussian Sum.inl (threeLeft w)
  have heq (x : Vector N) :
      (parameterLinear (sourcePureProbeLinear N p hp μ β) heldLabel 0 x) w =
        sphereLinear (mixtureCoefficients μ) x (β • g) := by
    change sourcePureProbeLinear N p hp μ β x
      (parameterOperator heldLabel 0 w) = _
    exact sourcePureProbeLinear_zero_eq_original hp μ β w x
  have hmeasure : sourcePureProbeGibbs N p hp μ β w =
      gibbsMeasure (sphereLaw N) (sphereLinear (mixtureCoefficients μ)) (β • g) := by
    unfold sourcePureProbeGibbs gibbsMeasure
    congr 1
    funext x
    congr 1
    unfold GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
    simp_rw [heq]
  rw [hmeasure, gaussianGibbs_eq_gibbsLaw]

end SlowEquilibration.SphericalPureProbeBaseGibbs
