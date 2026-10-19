-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureProbeSelectedKernel
public import SlowEquilibration.GaussianVarianceTraceContinuity

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalPureProbeFiniteResponse

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel GaussianFeatureDirac
open GaussianSpinComparison GaussianSpinInterpolation
open GaussianPerturbationParameter GaussianPerturbationSelfAveraging
open GaussianPerturbationResponse GaussianSelectedReplicaTrace
open SphericalPureProbeSelectedKernel
open GaussianVarianceTraceContinuity
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def sourcePureProbeLinear (N p : ℕ) (hp : 2 ≤ p)
    (μ : FiniteMixture) (β : ℝ) :=
  GaussianThreeBlockComparison.rotatedLinear
    (threeLinear (fieldFeature (mixtureCoefficients μ)) β 0
      (pureProbeFeature N p hp β)) threeLabel 0

def sourcePureProbeGibbs (N p : ℕ) (hp : 2 ≤ p)
    (μ : FiniteMixture) (β : ℝ)
    (w : EuclideanSpace ℝ
      (ThreeCoordinate N (Coordinate N μ.maxDegree)
        (Coordinate N (pureProbe p hp).maxDegree))) : Measure (Vector N) :=
  gibbsMeasure (sphereLaw N)
    (parameterLinear (sourcePureProbeLinear N p hp μ β) heldLabel 0) w

/-- At zero held amplitude, the actual finite selected variance trace is
`β² N` times one minus the two-replica overlap-power moment under the
corresponding original-field Gibbs law on the enlarged Gaussian bank. -/
theorem pureProbe_varianceTrace_eq_replicaPower
    {N p : ℕ} (hN : 1 ≤ N) (hp : 2 ≤ p)
    (μ : FiniteMixture) (β : ℝ)
    (w : EuclideanSpace ℝ
      (ThreeCoordinate N (Coordinate N μ.maxDegree)
        (Coordinate N (pureProbe p hp).maxDegree))) :
    varianceTrace (sphereLaw N) (sourcePureProbeLinear N p hp μ β)
      heldLabel 0 w =
      β^2*(N : ℝ)*(1-
        ∫ z : Vector N × Vector N, (overlap z.1 z.2)^p
          ∂(sourcePureProbeGibbs N p hp μ β w).prod
            (sourcePureProbeGibbs N p hp μ β w)) := by
  let A : Vector N → EuclideanSpace ℝ (Coordinate N μ.maxDegree) :=
    fieldFeature (mixtureCoefficients μ)
  let W := pureProbeFeature N p hp β
  let L := sourcePureProbeLinear N p hp μ β
  let G := sourcePureProbeGibbs N p hp μ β w
  have hA : Continuous A := fieldFeature_continuous _
  have hW : Continuous W := (fieldFeature_continuous _).const_smul β
  obtain ⟨B,hB,hBound⟩ := exists_threeLinear_sphere_bound A hA β 0 W hW
  have hL : Measurable L := GaussianThreeBlockComparison.rotatedLinear_measurable _
    (threeLinear_continuous A hA β 0 W hW).measurable threeLabel 0
  have hb0 : ∀ᵐ x ∂sphereLaw N, ‖threeLinear A β 0 W x‖ ≤ B :=
    (sphereLaw_support hN).mono fun x hx => hBound x hx
  have hb : ∀ᵐ x ∂sphereLaw N, ‖L x‖ ≤ B :=
    GaussianThreeBlockComparison.rotatedLinear_bound (sphereLaw N)
      (threeLinear A β 0 W) hB hb0 threeLabel 0
  have hG : IsProbabilityMeasure G := gibbsMeasure_probability (sphereLaw N)
    (parameterLinear L heldLabel 0)
    (parameterLinear_measurable L hL heldLabel 0)
    (parameterLinear_bound (sphereLaw N) L hB hb heldLabel 0) w
  have : IsProbabilityMeasure G := hG
  have hsupport : ∀ᵐ x ∂G, ‖x‖^2=(N : ℝ) :=
    (sphereLaw_support hN).filter_mono
      (gibbsMeasure_absolutelyContinuous (sphereLaw N)
        (parameterLinear L heldLabel 0) w).ae_le
  have hkernel (x y : Vector N) :
      selectedKernel L heldLabel x y = β^2*(N : ℝ)*(overlap x y)^p :=
    pureProbe_selectedKernel_eq_overlapPower hN hp μ β x y
  have hdiag : (∫ x, selectedKernel L heldLabel x x ∂G) = β^2*(N : ℝ) := by
    rw [integral_congr_ae (hsupport.mono (fun x hx => by
      rw [hkernel, overlap_self (by omega) x hx]))]
    simp
  have hpair :
      (∫ z : Vector N × Vector N, selectedKernel L heldLabel z.1 z.2 ∂G.prod G) =
        β^2*(N : ℝ)*(∫ z : Vector N × Vector N,
          (overlap z.1 z.2)^p ∂G.prod G) := by
    simp_rw [hkernel]
    rw [integral_const_mul]
  have ht := varianceTrace_eq_selectedKernel (sphereLaw N) L hL hB hb heldLabel 0 w
  change varianceTrace (sphereLaw N) L heldLabel 0 w =
    β^2*(N : ℝ)*(1-∫ z : Vector N × Vector N,
      (overlap z.1 z.2)^p ∂G.prod G)
  rw [ht]
  change (∫ x, selectedKernel L heldLabel x x ∂G) -
    (∫ z : Vector N × Vector N, selectedKernel L heldLabel z.1 z.2 ∂G.prod G) = _
  rw [hdiag,hpair]
  ring

end SlowEquilibration.SphericalPureProbeFiniteResponse
