-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceSourceCutoffInterior
public import Mathlib.Topology.Order.Compact

/-! The deterministic cap-hit inclusion used after local pathwise uniqueness
has coupled the true and smoothly truncated source trajectories. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance

open Set
open scoped NNReal
set_option autoImplicit false

/-- If two radial paths agree up to the first exit of the true path from
the radial and gradient cutoff interior, then a true cap hit forces either
a truncated cap hit or a true gradient-cutoff hit. This includes an initial
cap hit at time zero. -/
theorem cap_hit_of_preexit_agreement
    (r s rCut : ℝ≥0 → ℝ) (hr : Continuous r)
    (T : ℝ≥0) {a α : ℝ} (haα : a < α)
    (hAgree : ∀ t : ℝ≥0, t ≤ T →
      (∀ v : ℝ≥0, v < t → |r v| < α ∧ |s v| < α) → r t = rCut t)
    (hHit : ∃ t : ℝ≥0, t ≤ T ∧ a ≤ |r t|) :
    (∃ t : ℝ≥0, t ≤ T ∧ a ≤ |rCut t|) ∨
      (∃ t : ℝ≥0, t ≤ T ∧ α ≤ |s t|) := by
  by_contra hbad
  have hNoCut : ¬∃ t : ℝ≥0, t ≤ T ∧ a ≤ |rCut t| := fun h => hbad (Or.inl h)
  have hNoGrad : ¬∃ t : ℝ≥0, t ≤ T ∧ α ≤ |s t| := fun h => hbad (Or.inr h)
  let S : Set ℝ≥0 := Icc 0 T ∩ {t | a ≤ |r t|}
  have hclosed : IsClosed {t : ℝ≥0 | a ≤ |r t|} :=
    isClosed_Ici.preimage hr.abs
  have hcompact : IsCompact S := isCompact_Icc.inter_right hclosed
  have hnonempty : S.Nonempty := by
    obtain ⟨t,htT,hta⟩ := hHit
    exact ⟨t,⟨⟨zero_le,htT⟩,hta⟩⟩
  obtain ⟨t₀,ht₀,hleast⟩ := hcompact.exists_isLeast hnonempty
  have ht₀T : t₀ ≤ T := ht₀.1.2
  have ht₀a : a ≤ |r t₀| := ht₀.2
  have hbefore (v : ℝ≥0) (hv : v < t₀) :
      |r v| < α ∧ |s v| < α := by
    have hvT : v ≤ T := (le_of_lt hv).trans ht₀T
    have hvr : |r v| < a := by
      by_contra hn
      have hmem : v ∈ S := ⟨⟨zero_le,hvT⟩,le_of_not_gt hn⟩
      exact (not_lt_of_ge (hleast hmem)) hv
    have hvs : |s v| < α := by
      by_contra hn
      exact hNoGrad ⟨v,hvT,le_of_not_gt hn⟩
    exact ⟨hvr.trans haα,hvs⟩
  have heq := hAgree t₀ ht₀T hbefore
  exact hNoCut ⟨t₀,ht₀T,by rw [← heq]; exact ht₀a⟩

end SlowEquilibration.ConditionedEntrance
