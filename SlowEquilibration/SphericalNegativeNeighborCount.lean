-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NegativeNeighborSimplex
public import SlowEquilibration.SphericalBarycenter

/-! The source finite retained-point negative-neighbor bound, applied to
the literal radius-sqrt(N) sphere and its actual normalized overlap. -/
@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open SphericalBarycenter SphericalForm SphericalAging.HardSphereDynamics
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

theorem spherical_negative_neighbors_card_le {N : ℕ} (hN : 1 ≤ N)
    {ι : Type*} (s : Finset ι) (v : ι → Vector N)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε < δ^2)
    (hv : ∀ i ∈ s, ‖v i‖^2 = (N:ℝ))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → overlap (v i) (v j) ≤ ε)
    (i : ι) (hi : i ∈ s) :
    ((s.filter fun j => j ≠ i ∧ overlap (v i) (v j) ≤ -δ).card:ℝ) ≤
      (1-ε)/(δ^2-ε) := by
  have hunit : ∀ j ∈ s, ‖spin (v j)‖ = 1 := fun j hj =>
    spin_norm hN (v j) ((onSphere_iff_norm_sq (v j)).mpr (hv j hj))
  have hp : ∀ j ∈ s, ∀ l ∈ s, j ≠ l →
      inner ℝ (spin (v j)) (spin (v l)) ≤ ε := by
    intro j hj l hl hne
    rw [spin_inner hN]
    exact hpair j hj l hl hne
  simpa only [spin_inner hN] using
    NegativeNeighborSimplex.negative_neighbors_card_le s (fun j => spin (v j))
      hδ hδ1 hε hunit hp i hi

/-- The literal ordered strongly negative overlap count is linear in the
actual finite spherical family's size, with exact source constant. -/
theorem spherical_ordered_negative_neighbor_count_le {N : ℕ} (hN : 1 ≤ N)
    {ι : Type*} (s : Finset ι) (v : ι → Vector N)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε < δ^2)
    (hv : ∀ i ∈ s, ‖v i‖^2 = (N:ℝ))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → overlap (v i) (v j) ≤ ε) :
    (∑ i ∈ s, ((s.filter fun j => j ≠ i ∧ overlap (v i) (v j) ≤ -δ).card:ℝ)) ≤
      ((1-ε)/(δ^2-ε))*(s.card:ℝ) := by
  classical
  calc
    _ ≤ ∑ _i ∈ s,((1-ε)/(δ^2-ε)) := Finset.sum_le_sum fun i hi =>
      spherical_negative_neighbors_card_le hN s v hδ hδ1 hε hv hpair i hi
    _ = _ := by simp [mul_comm]

end
end SlowEquilibration.SphericalModel
