-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FiniteWickPairingOrder
public import SlowEquilibration.PairedTensorProjectionFeatures

/-! Genuine Wick labels identify exactly the free and paired slots in
actual ordered projected tensor coefficient features. -/

@[expose] public section
namespace SlowEquilibration.FiniteWickPairings
noncomputable section
open SphericalAging.FiniteModel PairedTensorProjectionFeatures SphericalProjectionMatrixFeature
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def unpairedSlot {p : ℕ} (S : Finset (Fin p)) (k : Fin (Finset.univ\S).card) : Fin p :=
  (Finset.univ\S).toList.get ⟨k.val,by simp⟩

def pairingBlockEquiv {p : ℕ} (S : Finset (Fin p)) (L : List (Fin p×Fin p))
    (hL : ValidPairing S L) : Fin ((Finset.univ\S).card+L.length+L.length)≃Fin p :=
  (finCongr (pairingOrderList_length_blocks S L)).symm.trans
    (List.Nodup.getEquivOfForallMemList (pairingOrderList S L) (pairingOrderList_nodup hL)
      (fun k => List.mem_toFinset.mp (by rw [pairingOrderList_toFinset hL]; exact Finset.mem_univ k)))

theorem pairingBlockEquiv_free {p : ℕ} (S : Finset (Fin p)) (L : List (Fin p×Fin p))
    (hL : ValidPairing S L) (k : Fin (Finset.univ\S).card) :
    pairingBlockEquiv S L hL (freeSlot (Finset.univ\S).card L.length k)=unpairedSlot S k := by
  change (pairingOrderList S L).get ⟨k.val,_⟩=(Finset.univ\S).toList.get ⟨k.val,_⟩
  simp only [pairingOrderList,List.get_eq_getElem]
  rw [List.getElem_append_left (by simp)]

theorem pairingBlockEquiv_left {p : ℕ} (S : Finset (Fin p)) (L : List (Fin p×Fin p))
    (hL : ValidPairing S L) (k : Fin L.length) :
    pairingBlockEquiv S L hL (leftPairSlot (Finset.univ\S).card L.length k)=(L.get k).1 := by
  have hs : (Finset.univ\S).toList.length=(Finset.univ\S).card := by simp
  change (pairingOrderList S L).get ⟨(Finset.univ\S).card+k.val,_⟩=(L.get k).1
  simp only [pairingOrderList,splitPairingLabels,List.get_eq_getElem]
  rw [List.getElem_append_right (by rw [hs];omega)]
  simp only [hs,Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simp),List.getElem_map]

theorem pairingBlockEquiv_right {p : ℕ} (S : Finset (Fin p)) (L : List (Fin p×Fin p))
    (hL : ValidPairing S L) (k : Fin L.length) :
    pairingBlockEquiv S L hL (rightPairSlot (Finset.univ\S).card L.length k)=(L.get k).2 := by
  have hs : (Finset.univ\S).toList.length=(Finset.univ\S).card := by simp
  change (pairingOrderList S L).get ⟨(Finset.univ\S).card+L.length+k.val,_⟩=(L.get k).2
  simp only [pairingOrderList,splitPairingLabels,List.get_eq_getElem]
  rw [List.getElem_append_right (by rw [hs];omega)]
  simp only [hs,show (Finset.univ\S).card+L.length+k.val-(Finset.univ\S).card=L.length+k.val by omega]
  rw [List.getElem_append_right (by simp only [List.length_map];omega)]
  simp only [List.length_map,Nat.add_sub_cancel_left,List.getElem_map]

theorem prod_unpairedSlot {p : ℕ} (S : Finset (Fin p)) (f : Fin p→ℝ) :
    (∏ k : Fin (Finset.univ\S).card,f (unpairedSlot S k))=∏ k∈Finset.univ\S,f k := by
  have hs : (Finset.univ\S).toList.length=(Finset.univ\S).card := by simp
  calc
    _=∏ k : Fin (Finset.univ\S).toList.length,f ((Finset.univ\S).toList[k.val]) :=
      Fintype.prod_equiv (finCongr hs).symm _ _ (fun k => rfl)
    _=((Finset.univ\S).toList.map f).prod := Fin.prod_univ_fun_getElem _ _
    _=_ := Finset.prod_map_toList _ _

theorem prod_pairingWeight {p : ℕ} (L : List (Fin p×Fin p)) (C : Fin p→Fin p→ℝ) :
    (∏ k : Fin L.length,C (L.get k).1 (L.get k).2)=pairingWeight C L := by
  exact Fin.prod_univ_fun_getElem L (fun a => C a.1 a.2)

/-- Exact original-slot realization of each genuine Wick coefficient contraction. -/
theorem pairedTensorFeature_pairingBlockEquiv {N p : ℕ} (S : Finset (Fin p))
    (L : List (Fin p×Fin p)) (hL : ValidPairing S L) (x : Vector N) (I : TensorIndex N p) :
    pairedTensorFeature N (Finset.univ\S).card L.length x (I ∘ pairingBlockEquiv S L hL)=
      (∏ k∈Finset.univ\S,x (I k))*
        pairingWeight (fun a b => projectionMatrixFeature x (I a,I b)) L := by
  simp only [pairedTensorFeature,Function.comp_apply]
  simp_rw [pairingBlockEquiv_free,pairingBlockEquiv_left,pairingBlockEquiv_right]
  rw [prod_unpairedSlot S (fun k => x (I k)),
    prod_pairingWeight L (fun a b => projectionMatrixFeature x (I a,I b))]

end
end SlowEquilibration.FiniteWickPairings
