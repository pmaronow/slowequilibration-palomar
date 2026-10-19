-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib

@[expose] public section

namespace SlowEquilibration.PositiveWeightOrdering

open Set Function Order Filter
open scoped Topology

/-- A countably infinite family of positive weights with finite positive
superlevels can be enumerated in decreasing order, including multiplicities.
The ordering is constructed from the weights and an injective natural label. -/
theorem exists_antitone_enumeration {ι : Type*} [Countable ι] [Infinite ι]
    (w : ι → ℝ) (hpos : ∀ i, 0 < w i)
    (hfinite : ∀ c > 0, {i | c ≤ w i}.Finite) :
    ∃ e : ℕ ≃ ι, Antitone (fun n => w (e n)) := by
  classical
  obtain ⟨code, hcode⟩ := exists_injective_nat ι
  let key : ι → ℝ ×ₗ ℕ := fun i => toLex (-w i, code i)
  have hkey : Injective key := by
    intro i j hij
    apply hcode
    exact congrArg (fun p => (ofLex p).2) hij
  let : LinearOrder ι := LinearOrder.lift' key hkey
  have horder (i j : ι) (hij : i ≤ j) : w j ≤ w i := by
    change toLex (-w i, code i) ≤ toLex (-w j, code j) at hij
    rw [Prod.Lex.toLex_le_toLex] at hij
    rcases hij with hh | ⟨hh, _⟩ <;> linarith
  have hIic (i : ι) : (Iic i).Finite :=
    (hfinite (w i) (hpos i)).subset (fun j hj => horder j i hj)
  let : LocallyFiniteOrder ι := LocallyFiniteOrder.ofFiniteIcc
    (fun a b => (hIic b).subset (fun j hj => hj.2))
  let i0 : ι := Classical.choice inferInstance
  let s := (hIic i0).toFinset
  have hsn : s.Nonempty := ⟨i0, by simp [s]⟩
  let m := s.min' hsn
  have hmi0 : m ≤ i0 := Finset.min'_le s i0 (by simp [s])
  have hmj (j : ι) : m ≤ j := by
    by_cases hji : j ≤ i0
    · exact Finset.min'_le s j (by simpa [s] using hji)
    · exact hmi0.trans (le_of_not_ge hji)
  let : OrderBot ι := {bot := m, bot_le := hmj}
  let : NoMaxOrder ι := ⟨by
    intro i
    by_contra hn
    have hall : ∀ j : ι, j ≤ i := by
      intro j
      exact le_of_not_gt (fun hj => hn ⟨j, hj⟩)
    have hfin : (univ : Set ι).Finite := (hIic i).subset (fun j _ => hall j)
    exact Set.infinite_univ hfin⟩
  let : SuccOrder ι := LinearLocallyFiniteOrder.succOrder ι
  let : PredOrder ι := LinearLocallyFiniteOrder.predOrder ι
  let e : ℕ ≃ ι := (orderIsoNatOfLinearSuccPredArch (ι := ι)).symm.toEquiv
  refine ⟨e, ?_⟩
  intro i j hij
  exact horder _ _ ((orderIsoNatOfLinearSuccPredArch (ι := ι)).symm.monotone hij)

/-- Any injective enumeration of positive weights with finite superlevels
converges to zero. This conclusion does not assume an ordering. -/
theorem tendsto_zero_of_finite_superlevels {ι : Type*} (w : ι → ℝ)
    (hpos : ∀ i, 0 < w i) (hfinite : ∀ c > 0, {i | c ≤ w i}.Finite)
    (e : ℕ → ι) (he : Injective e) : Tendsto (fun n => w (e n)) atTop (𝓝 (0:ℝ)) := by
  have ht : Tendsto w cofinite (𝓝 (0:ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(hfinite ε hε).eventually_cofinite_notMem] with i hi
    rw [Real.dist_eq, sub_zero, abs_of_pos (hpos i)]
    exact lt_of_not_ge hi
  exact ht.comp (by simpa only [Nat.cofinite_eq_atTop] using he.tendsto_cofinite)

/-- The reciprocal-minus-one generator weights are nondecreasing whenever
the positive resolvent weights are nonincreasing. -/
theorem generator_weights_monotone {ι : Type*} [Preorder ι] (w : ι → ℝ)
    (hpos : ∀ i, 0 < w i) (hanti : Antitone w) : Monotone (fun i => (w i)⁻¹-1) := by
  intro i j hij
  have hi := (inv_le_inv₀ (hpos i) (hpos j)).mpr (hanti hij)
  exact sub_le_sub_right hi 1

/-- A positive resolvent-weight sequence converging to zero gives actual
generator weights diverging to positive infinity. -/
theorem generator_weights_tendsto_atTop (w : ℕ → ℝ) (hpos : ∀ n, 0 < w n)
    (ht : Tendsto w atTop (𝓝 (0:ℝ))) :
    Tendsto (fun n => (w n)⁻¹-1) atTop atTop := by
  have hgt : Tendsto w atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hpos⟩
  simpa only [sub_eq_add_neg] using! tendsto_atTop_add_const_right atTop (-1)
    hgt.inv_tendsto_nhdsGT_zero

end SlowEquilibration.PositiveWeightOrdering
