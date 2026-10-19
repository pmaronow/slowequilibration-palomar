-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFullArrayCubeSupport
public import SlowEquilibration.DirectingPhysicalNorm

/-! Weak-limit transfer of the true physical pair covariance mean.
The covariance polynomial is clipped outside the overlap cube to make
one globally bounded continuous test; clipping does not alter any of the
physical or limiting integrals. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPairMeanWeakLimit

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalAsymptoticScoreLimits
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalFullArrayCubeSupport
open SlowEquilibration.DirectingPhysical
open scoped Topology BigOperators BoundedContinuousFunction

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def clipOverlap (r : ℝ) : ℝ := max (-1) (min 1 r)

theorem clipOverlap_mem_Icc (r : ℝ) : clipOverlap r ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clipOverlap_eq_of_mem_Icc {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    clipOverlap r = r := by
  simp [clipOverlap, min_eq_right hr.2, max_eq_right hr.1]

theorem clipOverlap_continuous : Continuous clipOverlap :=
  continuous_const.max (continuous_const.min continuous_id)

def clippedPairCovariance (μ : FiniteMixture) :
    FullOverlapCoordinates 2 →ᵇ ℝ := by
  let f : FullOverlapCoordinates 2 → ℝ :=
    fun c => μ.xi (clipOverlap (c 0 1))
  have hξ : Continuous μ.xi := continuous_iff_continuousAt.mpr fun r =>
    (μ.hasDerivAt_xi r).continuousAt
  have hcont : Continuous f := by
    exact hξ.comp (clipOverlap_continuous.comp
      ((continuous_apply (1 : Fin 2)).comp (continuous_apply (0 : Fin 2))))
  have hbound (c : FullOverlapCoordinates 2) : |f c| ≤ μ.xi 1 := by
    exact finiteMixture_xi_abs_le μ (by norm_num)
      (abs_le.mpr (clipOverlap_mem_Icc (c 0 1)))
  refine ⟨⟨f, hcont⟩, ⟨2 * μ.xi 1, ?_⟩⟩
  intro c d
  rw [Real.dist_eq]
  calc
    |f c - f d| ≤ |f c| + |f d| := abs_sub _ _
    _ ≤ μ.xi 1 + μ.xi 1 := add_le_add (hbound c) (hbound d)
    _ = 2 * μ.xi 1 := by ring

theorem clippedPairCovariance_eq_on_cube
    (μ : FiniteMixture) {c : FullOverlapCoordinates 2}
    (hc : c ∈ fullOverlapCube 2) :
    clippedPairCovariance μ c = μ.xi (c 0 1) := by
  change μ.xi (clipOverlap (c 0 1)) = μ.xi (c 0 1)
  rw [clipOverlap_eq_of_mem_Icc (hc 0 (mem_univ _) 1 (mem_univ _))]

theorem physicalPairCovarianceMean_eq_clipped
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) :
    (∫ c, clippedPairCovariance μ c ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))) =
      ∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)) := by
  apply integral_congr_ae
  exact (physicalFullOverlapLaw_cube_ae μ β).mono
    (fun c hc => clippedPairCovariance_eq_on_cube μ hc)

theorem asymptoticPairCovarianceMean_eq_clipped
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    (∫ c, clippedPairCovariance μ c ∂(x 2 : Measure (FullOverlapCoordinates 2))) =
      ∫ c, μ.xi (c 0 1) ∂(x 2 : Measure (FullOverlapCoordinates 2)) := by
  apply integral_congr_ae
  exact ((physicalFullAsymptoticLimitSet_cube μ β hx) 2).mono
    (fun c hc => clippedPairCovariance_eq_on_cube μ hc)

/-- If the actual annealed two-replica covariance mean has a full-sequence
limit, that value is the covariance mean of every asymptotic full-array
limit. This is the weak-limit part of the pair-mean input to Theorem 6.3. -/
theorem asymptoticPairCovarianceMean_eq_of_physical_tendsto
    (μ : FiniteMixture) (β L : ℝ)
    (hmean : Tendsto (fun n : ℕ =>
      ∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 L))
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    (∫ c, μ.xi (c 0 1) ∂(x 2 : Measure (FullOverlapCoordinates 2))) = L := by
  obtain ⟨s, hs, hfull⟩ :=
    ((mem_tailClusterSet_iff_mapClusterPt _ _).1 hx).tendsto_subseq
  have hm : Tendsto
      (fun j => physicalFullOverlapLaw (n := s j) (m := 2) μ β)
      atTop (𝓝 (x 2)) :=
    ((continuous_apply 2).tendsto x).comp hfull
  have hweak := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hm)
    (clippedPairCovariance μ)
  have hweak' : Tendsto (fun j =>
      ∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
        (n := s j) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 (∫ c, μ.xi (c 0 1) ∂(x 2 : Measure (FullOverlapCoordinates 2)))) := by
    simpa only [physicalPairCovarianceMean_eq_clipped,
      asymptoticPairCovarianceMean_eq_clipped μ β hx] using hweak
  exact tendsto_nhds_unique hweak' (hmean.comp hs.tendsto_atTop)

end SlowEquilibration.PureCapturePhysicalPairMeanWeakLimit
