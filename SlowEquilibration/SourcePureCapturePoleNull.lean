-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalModel
public import SlowEquilibration.SphericalLatitudeLaplace
public import SlowEquilibration.SphericalGibbsMass
public import Mathlib.Tactic

/-! Pole-null identities for Borel cap partition marks, proved from the actual spherical latitude coarea formula. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapturePoleNull
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The actual latitude disintegration is supported strictly between the
two poles. This applies to any Borel latitude set and any continuous field. -/
theorem partitionOn_overlap_inter_open_unit {n : ℕ} (hn : 2 ≤ n)
    (β : ℝ) {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A) :
    partitionOn β H (overlapRegion u A) =
      partitionOn β H (overlapRegion u (A ∩ Ioo (-1 : ℝ) 1)) := by
  have he : ENNReal.ofReal (partitionOn β H (overlapRegion u A)) =
      ENNReal.ofReal
        (partitionOn β H (overlapRegion u (A ∩ Ioo (-1 : ℝ) 1))) := by
    rw [partitionOn_latitude_coarea hn β hH u hu hA,
      partitionOn_latitude_coarea hn β hH u hu (hA.inter measurableSet_Ioo)]
    congr 1
    apply lintegral_congr
    intro r
    by_cases hr : (r : ℝ) < 2
    · have hrmem : r ∈ {s : Ioi (0 : ℝ) | (s : ℝ) < 2} := hr
      have hq := radialLatitude_mem ⟨r.property, hr⟩
      simp only [Set.indicator_of_mem hrmem]
      by_cases hmem : radialLatitude r ∈ A
      · simp only [Set.indicator_of_mem hmem,
          Set.indicator_of_mem (show radialLatitude r ∈ A ∩ Ioo (-1 : ℝ) 1
            from ⟨hmem, hq⟩)]
      · have hnot : radialLatitude r ∉ A ∩ Ioo (-1 : ℝ) 1 :=
          fun h => hmem h.1
        simp only [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hnot]
    · have hrnot : r ∉ {s : Ioi (0 : ℝ) | (s : ℝ) < 2} := hr
      simp only [Set.indicator_of_notMem hrnot]
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (partitionOn_nonneg β H _)] using hr

/-- In particular, the closed cap used in the physical coarse cover and
the half-open cap used in the Kac--Rice mark have equal partition mass. -/
theorem partitionOn_closed_cap_eq_half_open {n : ℕ} (hn : 2 ≤ n)
    (β : ℝ) {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1 : ℕ) : ℝ)) (a : ℝ) :
    partitionOn β H (overlapRegion u (Ici a)) =
      partitionOn β H (overlapRegion u (Ico a 1)) := by
  rw [partitionOn_overlap_inter_open_unit hn β hH u hu measurableSet_Ici,
    partitionOn_overlap_inter_open_unit hn β hH u hu measurableSet_Ico]
  congr 1
  ext q
  simp only [overlapRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ico, Set.mem_Ioo]
  tauto

/-- Removing any Borel microscopic interval preserves this pole-null
identity. No connectedness assumption is imposed on the remaining set. -/
theorem partitionOn_closed_cap_difference_eq_half_open {n : ℕ}
    (hn : 2 ≤ n) (β : ℝ) {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1 : ℕ) : ℝ))
    (a : ℝ) {I : Set ℝ} (hI : MeasurableSet I) :
    partitionOn β H (overlapRegion u (Ici a \ I)) =
      partitionOn β H (overlapRegion u (Ico a 1 \ I)) := by
  rw [partitionOn_overlap_inter_open_unit hn β hH u hu (measurableSet_Ici.diff hI),
    partitionOn_overlap_inter_open_unit hn β hH u hu (measurableSet_Ico.diff hI)]
  congr 1
  ext q
  simp only [overlapRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_Ici, Set.mem_Ico, Set.mem_Ioo]
  tauto


end
end SlowEquilibration.SourcePureCapturePoleNull
