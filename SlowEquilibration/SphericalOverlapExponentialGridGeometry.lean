-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOverlapExponentialGridLaw

/-! Deterministic grid geometry for bounded cap exposure. Actual shifted-cell
probabilities from the genuine physical flow are combined by a finite union. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalOverlapExponential
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics SphericalC1Dynamics
open scoped NNReal ENNReal ContDiff InnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def gridSize (H T : ℝ≥0) : ℕ := ⌈(H : ℝ) / (T : ℝ)⌉₊ + 1
def gridStart (T : ℝ≥0) (j : ℕ) : ℝ≥0 := (j : ℝ≥0) * T

def badGrid {Ω : Type*} (r : ℝ≥0 → Ω → ℝ) (H T : ℝ≥0) (δ : ℝ) : Set Ω :=
  {omega | ∃ j : Fin (gridSize H T),∃ v : ℝ≥0,v ≤ T ∧
    δ < |r (gridStart T j.val + v) omega - r (gridStart T j.val) omega|}

lemma grid_cell_of_time (H T : ℝ≥0) (hT : 0 < T) (t : ℝ≥0) (ht : t ≤ H) :
    ∃ j : Fin (gridSize H T),∃ v : ℝ≥0,v ≤ T ∧ gridStart T j.val + v = t ∧ gridStart T j.val ≤ H := by
  have hTr : (0 : ℝ) < T := hT
  let j := ⌊(t : ℝ) / (T : ℝ)⌋₊
  have hj : j ≤ ⌈(H : ℝ) / (T : ℝ)⌉₊ :=
    (Nat.floor_mono (div_le_div_of_nonneg_right (show (t : ℝ) ≤ H from ht) hTr.le)).trans (Nat.floor_le_ceil _)
  have hleftR : (j : ℝ) * (T : ℝ) ≤ (t : ℝ) :=
    (le_div_iff₀ hTr).mp (Nat.floor_le (div_nonneg t.coe_nonneg hTr.le))
  have hrightR : (t : ℝ) < ((j : ℝ) + 1) * (T : ℝ) :=
    (div_lt_iff₀ hTr).mp (Nat.lt_floor_add_one ((t : ℝ) / (T : ℝ)))
  have hleft : gridStart T j ≤ t := by
    exact_mod_cast hleftR
  let v := t - gridStart T j
  have hv : v ≤ T := by
    apply NNReal.coe_le_coe.mp
    dsimp [v]
    rw [NNReal.coe_sub hleft]
    simp only [gridStart,NNReal.coe_mul,NNReal.coe_natCast]
    linarith
  refine ⟨⟨j,by dsimp [gridSize]; omega⟩,v,hv,add_tsub_cancel_of_le hleft,hleft.trans ht⟩

lemma good_grid_cell_bound {Ω : Type*} (r : ℝ≥0 → Ω → ℝ) (H T : ℝ≥0) (δ : ℝ)
    (omega : Ω) (hgood : omega ∉ badGrid r H T δ) (j : Fin (gridSize H T))
    (v : ℝ≥0) (hv : v ≤ T) :
    |r (gridStart T j.val + v) omega - r (gridStart T j.val) omega| ≤ δ := by
  by_contra hn
  exact hgood ⟨j,v,hv,lt_of_not_ge hn⟩

/-- A cap hit anywhere before H creates a full grid-cell exposure interval.
The cell may extend beyond the hit; it always ends by H+T. -/
theorem grid_hit_has_residence (r : ℝ≥0 → ℝ) (H T : ℝ≥0) (hT : 0 < T)
    {α : ℝ} (_hα : 0 < α)
    (hgood : ∀ j : Fin (gridSize H T),∀ v : ℝ≥0,v ≤ T →
      |r (gridStart T j.val + v) - r (gridStart T j.val)| ≤ α / 12)
    (hhit : ∃ t : ℝ≥0,t ≤ H ∧ α / 2 ≤ |r t|) :
    ∃ j : Fin (gridSize H T),gridStart T j.val ≤ H ∧
      ∀ v : ℝ≥0,v ≤ T → α / 3 ≤ |r (gridStart T j.val + v)| := by
  obtain ⟨t,ht,hcap⟩ := hhit
  obtain ⟨j,v,hv,he,hj⟩ := grid_cell_of_time H T hT t ht
  have hd := hgood j v hv
  rw [he] at hd
  have htri := abs_add_le (r t - r (gridStart T j.val)) (r (gridStart T j.val))
  rw [sub_add_cancel] at htri
  have hstart : 5 * α / 12 ≤ |r (gridStart T j.val)| := by linarith
  refine ⟨j,hj,?_⟩
  intro w hw
  have hdw := hgood j w hw
  have htriw := abs_add_le (r (gridStart T j.val) - r (gridStart T j.val + w)) (r (gridStart T j.val + w))
  rw [sub_add_cancel,abs_sub_comm] at htriw
  linarith

lemma gridSize_upper (H T : ℝ≥0) : (gridSize H T : ℝ) ≤ (H : ℝ) / (T : ℝ) + 2 := by
  have hh := (Nat.ceil_lt_add_one (div_nonneg H.coe_nonneg T.coe_nonneg)).le
  simp only [gridSize,Nat.cast_add,Nat.cast_one]
  linarith

variable {N : ℕ}

/-- Actual physical grid failure probability: each cell is controlled by
true future-Wiener law, and only a finite deterministic union is taken. -/
theorem badGrid_probability (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) {δ : ℝ} (hδ : 0 < δ)
    (H T : ℝ≥0) (hT : 0 < T) (hshort : 4 * (1 + β * C) * (T : ℝ) ≤ δ) :
    (VectorBrownian.law N).real (badGrid (fun t omega => overlapValue u (process β g hg x t omega)) H T δ) ≤
      (gridSize H T : ℝ) * 2 * Real.exp (-(N : ℝ) * δ ^ 2 / (16 * (T : ℝ))) := by
  let A : Fin (gridSize H T) → Set (VectorBrownian.Space N) := fun j =>
    {omega | ∃ v : ℝ≥0,v ≤ T ∧ δ <
      |overlapValue u (process β g hg x (gridStart T j.val + v) omega) -
        overlapValue u (process β g hg x (gridStart T j.val) omega)|}
  have he : badGrid (fun t omega => overlapValue u (process β g hg x t omega)) H T δ = ⋃ j,A j := by
    ext omega
    simp only [badGrid,A,mem_ofPred_eq,mem_iUnion]
  rw [he]
  calc
    _ ≤ ∑ j : Fin (gridSize H T),(VectorBrownian.law N).real (A j) := measureReal_iUnion_fintype_le A
    _ ≤ ∑ _j : Fin (gridSize H T),2 * Real.exp (-(N : ℝ) * δ ^ 2 / (16 * (T : ℝ))) :=
      Finset.sum_le_sum (fun j _ => shifted_overlap_absolute_short_window_tail hN hβ hC g hg hgrad u x hu hx hδ
        (gridStart T j.val) T hT hshort)
    _ = _ := by simp; ring

theorem joint_badGrid_probability (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) {δ : ℝ} (hδ : 0 < δ)
    (H T : ℝ≥0) (hT : 0 < T) (hshort : 4 * (1 + β * C) * (T : ℝ) ≤ δ) :
    (VectorBrownian.law N).real (badGrid (fun t omega => overlapValue u (jointPhysicalProcess β g hg x t omega)) H T δ) ≤
      (gridSize H T : ℝ) * 2 * Real.exp (-(N : ℝ) * δ ^ 2 / (16 * (T : ℝ))) := by
  have he : badGrid (fun t omega => overlapValue u (jointPhysicalProcess β g hg x t omega)) H T δ =ᵐ[VectorBrownian.law N]
      badGrid (fun t omega => overlapValue u (process β g hg x t omega)) H T δ := by
    filter_upwards [jointPhysicalProcess_ae_actual β g hg x] with omega homega
    simp only [badGrid,mem_ofPred_eq]
    simp_rw [homega]
  rw [measureReal_congr he]
  exact badGrid_probability hN hβ hC g hg hgrad u x hu hx hδ H T hT hshort

end SlowEquilibration.SphericalOverlapExponential
