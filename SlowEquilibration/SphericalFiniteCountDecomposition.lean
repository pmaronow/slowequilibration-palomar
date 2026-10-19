-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalNegativeNeighborCount

/-! The deterministic square-count split from manuscript `mp-count`.
All pairs are literal finite fibers of a spherical family; the diagonal
and strongly negative overlaps are counted explicitly. -/
@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open scoped BigOperators RealInnerProductSpace
local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 500000

/-- For a finite spherical family with small upper pair overlaps, its
square count is bounded by the actual central ordered-pair count plus the
source diagonal/negative-neighbor linear term. This includes antipodals. -/
theorem spherical_square_count_le_central_pairs_add {N : ℕ} (hN : 1 ≤ N)
    {ι : Type*} (s : Finset ι) (v : ι → Vector N)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε < δ^2)
    (hv : ∀ i ∈ s, ‖v i‖^2 = (N:ℝ))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → overlap (v i) (v j) ≤ ε) :
    (s.card:ℝ)^2 ≤
      (∑ i ∈ s, ((s.filter fun j => j ≠ i ∧ |overlap (v i) (v j)| < δ).card:ℝ)) +
      (1+(1-ε)/(δ^2-ε))*(s.card:ℝ) := by
  classical
  let A : ι → Finset ι := fun i => s.filter fun j => j ≠ i ∧ |overlap (v i) (v j)| < δ
  let B : ι → Finset ι := fun i => s.filter fun j => j ≠ i ∧ overlap (v i) (v j) ≤ -δ
  have hεδ : ε < δ := by nlinarith
  have hrow : ∀ i ∈ s,(s.card:ℝ) ≤ (A i).card+(B i).card+1 := by
    intro i hi
    have hcover : s ⊆ insert i (A i ∪ B i) := by
      intro j hj
      by_cases hji : j=i
      · exact Finset.mem_insert.mpr (Or.inl hji)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        by_cases hc : |overlap (v i) (v j)| < δ
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hj,hji,hc⟩))
        · have hlarge : δ ≤ |overlap (v i) (v j)| := le_of_not_gt hc
          have hr := hpair i hi j hj (Ne.symm hji)
          have hneg : overlap (v i) (v j) ≤ -δ := by
            rcases le_abs.mp hlarge with hpos | hneg
            · linarith
            · linarith
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hj,hji,hneg⟩))
    have hcard : s.card ≤ (A i).card+(B i).card+1 :=
      (Finset.card_le_card hcover).trans
        ((Finset.card_insert_le i _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) 1))
    exact_mod_cast hcard
  have hnegative : (∑ i ∈ s, ((B i).card:ℝ)) ≤
      ((1-ε)/(δ^2-ε))*(s.card:ℝ) :=
    spherical_ordered_negative_neighbor_count_le hN s v hδ hδ1 hε hv hpair
  calc
    _ = ∑ _i ∈ s,(s.card:ℝ) := by simp [pow_two,nsmul_eq_mul]
    _ ≤ ∑ i ∈ s,((A i).card+(B i).card+(1:ℝ)) := Finset.sum_le_sum hrow
    _ = (∑ i ∈ s,((A i).card:ℝ))+(∑ i ∈ s,((B i).card:ℝ))+(s.card:ℝ) := by
      simp [Finset.sum_add_distrib,nsmul_eq_mul]
    _ ≤ _ := by dsimp only [A]; nlinarith [hnegative]

end
end SlowEquilibration.SphericalModel
