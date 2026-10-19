-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceReductionCPPathBound

/-! Borel measurability of the original diffusion's critical-center path-hit
union for the open radial interval used by source first moments. The open
window is exhausted by countably many closed radial windows. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceReductionOpenWindowPathMeasurable
open Set MeasureTheory ProbabilityTheory SphericalModel
open SphericalRotationCovariance SphericalFieldKernels
open SphericalKacRiceHittingSource SphericalRealTimePathKernel
open SourceReductionClosedBandGraph SourceReductionClosedPathUnionGraph
open scoped NNReal ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 600000

variable {N : ℕ}

private theorem open_interval_closed_exhaustion (L R : ℝ) :
    Ioo L R = ⋃ j : ℕ,
      Icc (L+1/((j:ℝ)+1)) (R-1/((j:ℝ)+1)) := by
  ext k
  constructor
  · intro hk
    obtain ⟨j,hj⟩ := exists_nat_one_div_lt
      (lt_min (sub_pos.mpr hk.1) (sub_pos.mpr hk.2))
    refine Set.mem_iUnion.mpr ⟨j,?_⟩
    have h₁ := (lt_min_iff.mp hj).1
    have h₂ := (lt_min_iff.mp hj).2
    exact ⟨by linarith, by linarith⟩
  · intro hk
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hk
    have hp : 0 < 1/((j:ℝ)+1) := by positivity
    exact ⟨by linarith [hj.1], by linarith [hj.2]⟩

private theorem windowCenterGraph_iUnion (μ : FiniteMixture)
    (Q m M : ℝ) (V : ℕ → Set ℝ) :
    windowCenterGraph (N := N) μ Q m M (⋃ j, V j) =
      ⋃ j, windowCenterGraph μ Q m M (V j) := by
  ext z
  unfold windowCenterGraph
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iUnion]
  aesop

private theorem closedPathHitUnionGraph_iUnion (μ : FiniteMixture)
    (Q m M a : ℝ) (V : ℕ → Set ℝ) (T : ℝ≥0) :
    closedPathHitUnionGraph (N := N) μ Q m M a (⋃ j, V j) T =
      ⋃ j, closedPathHitUnionGraph μ Q m M a (V j) T := by
  ext z
  change (∃ u : PhysicalSphere N,
    (z.1,u.1) ∈ windowCenterGraph μ Q m M (⋃ j, V j) ∧
    (z.2,u) ∈ overlapSupEvent T a) ↔ _
  rw [windowCenterGraph_iUnion]
  constructor
  · rintro ⟨u,hu,hb⟩
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hu
    exact Set.mem_iUnion.mpr ⟨j,⟨u,hj,hb⟩⟩
  · intro hz
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
    obtain ⟨u,hu,hb⟩ := hj
    exact ⟨u,Set.mem_iUnion.mpr ⟨j,hu⟩,hb⟩

theorem closedPathHitUnionGraph_openWindow_measurable (μ : FiniteMixture)
    (Q m M a L R : ℝ) (T : ℝ≥0) :
    MeasurableSet
      (closedPathHitUnionGraph (N := N) μ Q m M a (Ioo L R) T) := by
  rw [open_interval_closed_exhaustion L R,
    closedPathHitUnionGraph_iUnion]
  exact MeasurableSet.iUnion fun j =>
    (closedPathHitUnionGraph_isClosed (N := N) μ Q m M a
      isClosed_Icc T).measurableSet

theorem actualWindowPathHitProbability_openWindow_measurable
    (hN : 2 ≤ N) (μ : FiniteMixture) (Q m M a β L R : ℝ)
    (T : ℝ≥0) :
    Measurable
      (actualWindowPathHitProbability hN μ Q m M a β (Ioo L R) T) := by
  let κ : Kernel (Disorder N μ.maxDegree) (RealSpherePath N T) :=
    (uniformRealPathKernel hN μ β T).comap (fieldMap μ)
      (fieldMap (N := N) μ).measurable
  change Measurable (fun J => (κ J).real
    (Prod.mk J ⁻¹' closedPathHitUnionGraph μ Q m M a (Ioo L R) T))
  exact (Kernel.measurable_kernel_prodMk_left (κ := κ)
    (closedPathHitUnionGraph_openWindow_measurable μ Q m M a L R T)).ennreal_toReal

theorem actualWindowPathHitProbability_mem_unit
    (hN : 2 ≤ N) (μ : FiniteMixture) (Q m M a β : ℝ)
    (U : Set ℝ) (T : ℝ≥0) (J : Disorder N μ.maxDegree) :
    actualWindowPathHitProbability hN μ Q m M a β U T J ∈ Icc 0 1 := by
  exact ⟨measureReal_nonneg,measureReal_le_one⟩

end SlowEquilibration.SourceReductionOpenWindowPathMeasurable
