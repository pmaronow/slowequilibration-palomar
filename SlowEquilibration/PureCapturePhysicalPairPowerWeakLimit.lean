-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPairMeanWeakLimit

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureCapturePhysicalPairPowerWeakLimit

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalAsymptoticScoreLimits PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalFullArrayCubeSupport PureCapturePhysicalPairMeanWeakLimit
open scoped Topology BoundedContinuousFunction

set_option autoImplicit false
set_option maxHeartbeats 1200000

def clippedPairPower (p : ℕ) : FullOverlapCoordinates 2 →ᵇ ℝ := by
  let f : FullOverlapCoordinates 2 → ℝ := fun z => clipOverlap (z 0 1) ^ p
  have hcont : Continuous f := by
    exact (clipOverlap_continuous.comp
      ((continuous_apply (1 : Fin 2)).comp (continuous_apply (0 : Fin 2)))).pow p
  have hbound (z : FullOverlapCoordinates 2) : |f z| ≤ 1 := by
    dsimp [f]
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr (clipOverlap_mem_Icc _))
  refine ⟨⟨f, hcont⟩, ⟨2, ?_⟩⟩
  intro z w
  rw [Real.dist_eq]
  exact (abs_sub _ _).trans (by linarith [hbound z, hbound w])

theorem clippedPairPower_integral_eq
    (ν : Measure (FullOverlapCoordinates 2))
    (hcube : ∀ᵐ z ∂ν, z ∈ fullOverlapCube 2) (p : ℕ) :
    (∫ z, clippedPairPower p z ∂ν) = ∫ z, (z 0 1) ^ p ∂ν := by
  apply integral_congr_ae
  filter_upwards [hcube] with z hz
  change clipOverlap (z 0 1) ^ p = (z 0 1) ^ p
  rw [clipOverlap_eq_of_mem_Icc (hz 0 (mem_univ _) 1 (mem_univ _))]

/-- Every physical pair-power moment limit is the corresponding moment of
every full-array weak limit, using the actual compact overlap support. -/
theorem asymptoticPairPower_eq_of_physical_tendsto
    (μ : FiniteMixture) (β L : ℝ) (p : ℕ)
    (hmean : Tendsto (fun n : ℕ =>
      ∫ z, (z 0 1) ^ p ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 L))
    {z : FullOverlapLawArray}
    (hz : z ∈ physicalFullAsymptoticLimitSet μ β) :
    (∫ w, (w 0 1) ^ p ∂(z 2 : Measure (FullOverlapCoordinates 2))) = L := by
  obtain ⟨s, hs, hfull⟩ :=
    ((mem_tailClusterSet_iff_mapClusterPt _ _).1 hz).tendsto_subseq
  have hm : Tendsto
      (fun j => physicalFullOverlapLaw (n := s j) (m := 2) μ β)
      atTop (𝓝 (z 2)) := ((continuous_apply 2).tendsto z).comp hfull
  have hweak := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hm)
    (clippedPairPower p)
  have hphysical (n : ℕ) := clippedPairPower_integral_eq
    (physicalFullOverlapLaw (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))
    (physicalFullOverlapLaw_cube_ae μ β) p
  have hlimit := clippedPairPower_integral_eq (z 2 : Measure (FullOverlapCoordinates 2))
    ((physicalFullAsymptoticLimitSet_cube μ β hz) 2) p
  have hweak' : Tendsto (fun j =>
      ∫ w, (w 0 1) ^ p ∂(physicalFullOverlapLaw
        (n := s j) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 (∫ w, (w 0 1) ^ p ∂(z 2 : Measure (FullOverlapCoordinates 2)))) := by
    simpa only [hphysical, hlimit] using hweak
  exact tendsto_nhds_unique hweak' (hmean.comp hs.tendsto_atTop)

end SlowEquilibration.PureCapturePhysicalPairPowerWeakLimit
