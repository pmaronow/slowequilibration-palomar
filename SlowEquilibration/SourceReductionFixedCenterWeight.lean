-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionClosedPathUnionGraph

/-! The literal fixed-center cap-hit probability is Borel jointly in the
original tensor disorder and the physical spherical center. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionFixedCenterWeight
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel
open SphericalKacRiceHittingSource SphericalFieldKernels
open SphericalRotationCovariance
open scoped NNReal ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- Manuscript `θ(H,u)` on original tensor coordinates. -/
def actualFixedCenterPathHitProbability (hN : 2 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) (a : ℝ)
    (J : Disorder N μ.maxDegree) (u : PhysicalSphere N) : ℝ :=
  pathPointWeight hN μ β T (overlapSupEvent T a) (fieldMap μ J,u)

theorem actualFixedCenterPathHitProbability_eq (hN : 2 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) (a : ℝ)
    (J : Disorder N μ.maxDegree) (u : PhysicalSphere N) :
    actualFixedCenterPathHitProbability hN μ β T a J u =
      (uniformRealPathKernel hN μ β T (fieldMap μ J)).real
        {p | (p,u) ∈ overlapSupEvent T a} :=
  pathPointWeight_eq hN μ β T (overlapSupEvent T a) _

theorem actualFixedCenterPathHitProbability_measurable (hN : 2 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) (a : ℝ) :
    Measurable (fun z : Disorder N μ.maxDegree × PhysicalSphere N =>
      actualFixedCenterPathHitProbability hN μ β T a z.1 z.2) := by
  have h := overlapSupWeight_measurable (N := N) hN μ β T a
  have hmap : Measurable (fun z : Disorder N μ.maxDegree × PhysicalSphere N =>
      (fieldMap μ z.1,z.2)) :=
    ((fieldMap (N := N) μ).measurable.comp measurable_fst).prodMk measurable_snd
  exact h.comp hmap

theorem actualFixedCenterPathHitProbability_mem_unit (hN : 2 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) (a : ℝ)
    (J : Disorder N μ.maxDegree) (u : PhysicalSphere N) :
    actualFixedCenterPathHitProbability hN μ β T a J u ∈ Icc (0 : ℝ) 1 := by
  unfold actualFixedCenterPathHitProbability
  exact pathPointWeight_mem_unit hN μ β T _ _

end
end SlowEquilibration.SourceReductionFixedCenterWeight
