-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSelectedReplicaTrace
public import SlowEquilibration.GaussianFeatureHeldPressure
public import SlowEquilibration.SphericalGaussianInterpolation

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalPureProbeSelectedKernel

open Set MeasureTheory ProbabilityTheory
open SphericalModel GaussianFeatureDirac GaussianSelectedReplicaTrace
open GaussianSpinComparison
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def pureProbe (p : ℕ) (hp : 2 ≤ p) : FiniteMixture :=
  FiniteMixture.pure p hp 1 (by norm_num)

def pureProbeFeature (N p : ℕ) (hp : 2 ≤ p) (β : ℝ) :
    Vector N → EuclideanSpace ℝ (Coordinate N (pureProbe p hp).maxDegree) :=
  fun x => β • fieldFeature (mixtureCoefficients (pureProbe p hp)) x

theorem pureProbeFeature_gram {N p : ℕ} (hN : 1 ≤ N) (hp : 2 ≤ p)
    (β : ℝ) (x y : Vector N) :
    inner ℝ (pureProbeFeature N p hp β x) (pureProbeFeature N p hp β y) =
      β^2*(N : ℝ)*(overlap x y)^p := by
  unfold pureProbeFeature
  rw [real_inner_smul_left, real_inner_smul_right,
    fieldFeature_inner_gram hN (mixtureCoefficients (pureProbe p hp))
      (mixtureCoefficients_nonnegative (pureProbe p hp)) x y,
    covariancePolynomial_mixture]
  rw [show (pureProbe p hp).xi (overlap x y) = (overlap x y)^p by
    simpa only [pureProbe,one_mul] using
      FiniteMixture.pure_xi p hp 1 (by norm_num) (overlap x y)]
  ring

/-- The held-bank selected kernel is exactly the Gram form of its feature
map, under any three-block rotation angle. -/
theorem three_selectedKernel_eq_featureGram
    {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Vector N → EuclideanSpace ℝ ι) (β k : ℝ)
    (W : Vector N → EuclideanSpace ℝ κ) (θ : ℝ)
    (x y : Vector N) :
    selectedKernel
      (GaussianThreeBlockComparison.rotatedLinear
        (threeLinear A β k W) threeLabel θ)
      heldLabel x y = inner ℝ (W x) (W y) := by
  unfold selectedKernel selectedWeight
  simp only [Fintype.sum_sum_type,heldLabel,Bool.false_eq_true,ite_false,ite_true,
    zero_mul, one_mul, Finset.sum_const_zero, zero_add]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [GaussianSpinComparison.coordinateObservable, RCLike.inner_apply,
    conj_trivial]
  rw [GaussianThreeBlockComparison.rotatedLinear_single,
    GaussianThreeBlockComparison.rotatedLinear_single]
  simp [GaussianThreeBlockComparison.rotationCoefficient,threeLabel,
    three_coordinate,threeFeature]
  ring

/-- A pure `p`-spin held bank has the exact physical overlap-power
covariance, including its diagonal value on the spherical state space. -/
theorem pureProbe_selectedKernel_eq_overlapPower
    {N p : ℕ} (hN : 1 ≤ N) (hp : 2 ≤ p)
    (μ : FiniteMixture) (β : ℝ) (x y : Vector N) :
    selectedKernel
      (GaussianThreeBlockComparison.rotatedLinear
        (threeLinear (fieldFeature (mixtureCoefficients μ)) β 0
          (pureProbeFeature N p hp β)) threeLabel 0)
      heldLabel x y = β^2*(N : ℝ)*(overlap x y)^p := by
  rw [three_selectedKernel_eq_featureGram]
  exact pureProbeFeature_gram hN hp β x y

end SlowEquilibration.SphericalPureProbeSelectedKernel
