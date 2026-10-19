-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FiniteWickPairings
public import Mathlib.Data.List.NodupEquivFin

/-! Every genuine labeled Wick pairing gives an actual permutation of
original tensor slots: first unpaired labels, then the left/right pair slots.
The permutation is constructed from its exact no-duplicate covering list. -/

@[expose] public section
namespace SlowEquilibration.FiniteWickPairings
noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {κ : Type} [DecidableEq κ]

def splitPairingLabels (L : List (κ×κ)) : List κ := L.map Prod.fst++L.map Prod.snd

omit [DecidableEq κ] in
theorem splitPairingLabels_perm (L : List (κ×κ)) :
    (splitPairingLabels L).Perm (pairingLabels L) := by
  induction L with
  | nil => simp [splitPairingLabels,pairingLabels]
  | cons a L ih =>
    change (a.1::(L.map Prod.fst++a.2::L.map Prod.snd)).Perm
      (a.1::a.2::pairingLabels L)
    exact (List.perm_middle.cons a.1).trans ((ih.cons a.2).cons a.1)

theorem splitPairingLabels_toFinset {I : Finset κ} {L : List (κ×κ)} (hL : ValidPairing I L) :
    (splitPairingLabels L).toFinset=I :=
  (List.toFinset_eq_of_perm _ _ (splitPairingLabels_perm L)).trans hL.2

theorem splitPairingLabels_nodup {I : Finset κ} {L : List (κ×κ)} (hL : ValidPairing I L) :
    (splitPairingLabels L).Nodup := (splitPairingLabels_perm L).nodup_iff.mpr hL.1

def pairingOrderList {p : ℕ} (I : Finset (Fin p)) (L : List (Fin p×Fin p)) : List (Fin p) :=
  (Finset.univ\I).toList++splitPairingLabels L

/-- The actual order list covers every original degree slot. -/
theorem pairingOrderList_toFinset {p : ℕ} {I : Finset (Fin p)} {L : List (Fin p×Fin p)}
    (hL : ValidPairing I L) : (pairingOrderList I L).toFinset=Finset.univ := by
  rw [pairingOrderList,List.toFinset_append,Finset.toList_toFinset,splitPairingLabels_toFinset hL]
  ext k
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
  exact iff_true_intro (Classical.em (k∈I)).symm

/-- Original unpaired and paired slots are disjoint, with no repeated labels. -/
theorem pairingOrderList_nodup {p : ℕ} {I : Finset (Fin p)} {L : List (Fin p×Fin p)}
    (hL : ValidPairing I L) : (pairingOrderList I L).Nodup := by
  unfold pairingOrderList
  apply List.nodup_append.mpr
  refine ⟨Finset.nodup_toList _,splitPairingLabels_nodup hL,?_⟩
  intro a ha b hb hab
  subst b
  have hnot : a∉I := (Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)).2
  have hmem : a∈I := by
    rw [←splitPairingLabels_toFinset hL]
    exact List.mem_toFinset.mpr hb
  exact hnot hmem

theorem pairingOrderList_length {p : ℕ} {I : Finset (Fin p)} {L : List (Fin p×Fin p)}
    (hL : ValidPairing I L) : (pairingOrderList I L).length=p := by
  rw [←List.toFinset_card_of_nodup (pairingOrderList_nodup hL),pairingOrderList_toFinset hL]
  simp

theorem pairingOrderList_length_blocks {p : ℕ} (I : Finset (Fin p)) (L : List (Fin p×Fin p)) :
    (pairingOrderList I L).length=(Finset.univ\I).card+L.length+L.length := by
  simp [pairingOrderList,splitPairingLabels,List.length_append,Nat.add_assoc]

/-- Degree decomposes into the actual unpaired slots and both labels of every pair. -/
theorem valid_pairing_degree {p : ℕ} {I : Finset (Fin p)} {L : List (Fin p×Fin p)}
    (hL : ValidPairing I L) : (Finset.univ\I).card+L.length+L.length=p := by
  rw [←pairingOrderList_length_blocks,pairingOrderList_length hL]

/-- The genuine labeled contraction fixes an actual permutation, not a
postulated matching of the original coefficient law. -/
def pairingSlotPermutation {p : ℕ} (I : Finset (Fin p)) (L : List (Fin p×Fin p))
    (hL : ValidPairing I L) : Equiv.Perm (Fin p) :=
  (finCongr (pairingOrderList_length hL)).symm.trans
    (List.Nodup.getEquivOfForallMemList (pairingOrderList I L) (pairingOrderList_nodup hL)
      (fun k => List.mem_toFinset.mp (by rw [pairingOrderList_toFinset hL]; exact Finset.mem_univ k)))

/-- All generated Wick contractions therefore have a literal original-slot order. -/
theorem generated_pairingOrderList_length {p : ℕ} (I : Finset (Fin p)) (L : List (Fin p×Fin p))
    (hL : L∈labeledWickPairings I) : (pairingOrderList I L).length=p :=
  pairingOrderList_length (labeledWickPairings_valid I L hL)

end
end SlowEquilibration.FiniteWickPairings
