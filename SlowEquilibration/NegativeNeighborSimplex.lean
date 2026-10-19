-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic

/-! The deterministic negative-neighbor bound used in manuscript
Lemma `mp-gram`. It follows from the squared norm of the sum of the actual
neighbor vectors and imposes no lower bound on pairwise inner products. -/
@[expose] public section
namespace SlowEquilibration.NegativeNeighborSimplex
noncomputable section
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 600000

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A genuine finite cap version of the simplex bound. Antipodal vectors
are allowed and counted by the same estimate. -/
theorem negative_family_card_le (s : Finset ι) (v : ι → H) (z : H)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε < δ^2)
    (hz : ‖z‖ = 1) (hv : ∀ i ∈ s, ‖v i‖ = 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) ≤ ε)
    (hneg : ∀ i ∈ s, inner ℝ z (v i) ≤ -δ) :
    (s.card:ℝ) ≤ (1-ε)/(δ^2-ε) := by
  classical
  let k : ℝ := s.card
  let w : H := ∑ i ∈ s,v i
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hgap : 0 < δ^2-ε := by linarith
  have hε1 : ε < 1 := by nlinarith
  have hrow : ∀ i ∈ s,
      (∑ j ∈ s,inner ℝ (v i) (v j)) ≤ k*ε+(1-ε) := by
    intro i hi
    calc
      _ ≤ ∑ j ∈ s, if i=j then (1:ℝ) else ε := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i=j
        · subst j
          simp [hv i hi]
        · simpa only [ite_eq_right hij] using hpair i hi j hj hij
      _ = ∑ j ∈ s, (ε+(if j=i then (1-ε) else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i=j
        · subst j
          simp
        · simp [hij,Ne.symm hij]
      _ = _ := by simp [Finset.sum_add_distrib,hi,k]
  have hupper : ‖w‖^2 ≤ k*(k*ε+(1-ε)) := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp only [w]
    rw [sum_inner]
    simp_rw [inner_sum]
    calc
      _ ≤ ∑ _i ∈ s,(k*ε+(1-ε)) := Finset.sum_le_sum hrow
      _ = _ := by simp [k]; ring
  have hinner : inner ℝ z w ≤ -(k*δ) := by
    dsimp only [w]
    rw [inner_sum]
    calc
      _ ≤ ∑ _i ∈ s,-δ := Finset.sum_le_sum hneg
      _ = _ := by simp [k]
  have habs : |inner ℝ z w| ≤ ‖w‖ := by
    simpa only [hz,one_mul] using abs_real_inner_le_norm z w
  have hlower : k*δ ≤ ‖w‖ := by
    have hm := (abs_le.mp habs).1
    linarith
  have hsquare : (k*δ)^2 ≤ ‖w‖^2 :=
    (sq_le_sq₀ (mul_nonneg hk hδ.le) (norm_nonneg _)).mpr hlower
  apply (le_div_iff₀ hgap).mpr
  change k*(δ^2-ε) ≤ 1-ε
  by_cases hk0 : k=0
  · rw [hk0,zero_mul]
    linarith
  · have hkp : 0<k := lt_of_le_of_ne hk (Ne.symm hk0)
    have hmul : k*(k*(δ^2-ε)-(1-ε)) ≤ 0 := by nlinarith [hupper,hsquare]
    have hnon : k*(δ^2-ε)-(1-ε) ≤ 0 :=
      nonpos_of_mul_nonpos_right hmul hkp
    linarith

/-- Exact source neighbor count in a finite family of unit vectors. -/
theorem negative_neighbors_card_le (s : Finset ι) (v : ι → H)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε < δ^2)
    (hv : ∀ i ∈ s, ‖v i‖ = 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) ≤ ε)
    (i : ι) (hi : i ∈ s) :
    ((s.filter fun j => j ≠ i ∧ inner ℝ (v i) (v j) ≤ -δ).card:ℝ) ≤
      (1-ε)/(δ^2-ε) := by
  classical
  apply negative_family_card_le _ v (v i) hδ hδ1 hε (hv i hi)
  · intro j hj
    exact hv j (Finset.mem_filter.mp hj).1
  · intro j hj l hl hne
    exact hpair j (Finset.mem_filter.mp hj).1 l (Finset.mem_filter.mp hl).1 hne
  · intro j hj
    exact (Finset.mem_filter.mp hj).2.2

/-- Literal ordered negative-neighbor count, expressed by summing its
finite fibers, is bounded linearly in the number of retained points. -/
theorem ordered_negative_neighbor_count_le (s : Finset ι) (v : ι → H)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε < δ^2)
    (hv : ∀ i ∈ s, ‖v i‖ = 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) ≤ ε) :
    (∑ i ∈ s, ((s.filter fun j => j ≠ i ∧ inner ℝ (v i) (v j) ≤ -δ).card:ℝ)) ≤
      ((1-ε)/(δ^2-ε))*(s.card:ℝ) := by
  classical
  calc
    _ ≤ ∑ _i ∈ s,((1-ε)/(δ^2-ε)) := Finset.sum_le_sum fun i hi =>
      negative_neighbors_card_le s v hδ hδ1 hε hv hpair i hi
    _ = _ := by simp [mul_comm]

end
end SlowEquilibration.NegativeNeighborSimplex
