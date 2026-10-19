-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceSourceCutoffHitInclusion
public import Mathlib.MeasureTheory.Measure.Real

/-! Probability transfer for the source true/cutoff cap coupling, requiring
only the localized pathwise-uniqueness conclusion as a separate premise. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance

open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

theorem cap_hit_probability_le_cut_add_gradient
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (r s rCut : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    {a α : ℝ} (haα : a < α)
    (hr : ∀ᵐ ω ∂P, Continuous (fun t => r t ω))
    (hAgree : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      (∀ v : ℝ≥0, v < t → |r v ω| < α ∧ |s v ω| < α) →
        r t ω = rCut t ω) :
    P.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ a ≤ |r t ω|} ≤
      P.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ a ≤ |rCut t ω|}+
      P.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ α ≤ |s t ω|} := by
  let A : Set Ω := {ω | ∃ t : ℝ≥0, t ≤ T ∧ a ≤ |r t ω|}
  let B : Set Ω := {ω | ∃ t : ℝ≥0, t ≤ T ∧ a ≤ |rCut t ω|}
  let C : Set Ω := {ω | ∃ t : ℝ≥0, t ≤ T ∧ α ≤ |s t ω|}
  have hInc : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ B ∪ C := by
    filter_upwards [hr,hAgree] with ω hcont hagree hhit
    exact cap_hit_of_preexit_agreement (fun t => r t ω) (fun t => s t ω)
      (fun t => rCut t ω) hcont T haα (hagree) hhit
  have hEq : A =ᵐ[P] A ∩ (B ∪ C) := by
    filter_upwards [hInc] with ω hω
    apply propext
    exact ⟨fun h => ⟨h,hω h⟩,fun h => h.1⟩
  calc
    P.real A = P.real (A ∩ (B ∪ C)) := measureReal_congr hEq
    _ ≤ P.real (B ∪ C) := measureReal_mono inter_subset_right
    _ ≤ P.real B + P.real C := measureReal_union_le B C

end SlowEquilibration.ConditionedEntrance
