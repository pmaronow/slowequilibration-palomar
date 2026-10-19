-- SPDX-License-Identifier: Apache-2.0
module

public import FourPapersCommon.GaussianCovarianceWickSum
public import Mathlib.Data.List.ToFinsupp

/-! Actual finite labeled Wick pairings. The recursively enumerated list
retains multiplicity, and every generated contraction uses each original
label exactly once. -/

@[expose] public section
namespace SlowEquilibration.FiniteWickPairings
noncomputable section
open FourPapersCommon
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {κ : Type} [DecidableEq κ]

def labeledWickPairings (I : Finset κ) : List (List (κ×κ)) :=
  if hI : I.Nonempty then
    ((I.erase hI.choose).toList).flatMap (fun j =>
      (labeledWickPairings ((I.erase hI.choose).erase j)).map (fun L => (j,hI.choose)::L))
  else [[]]
termination_by I.card
decreasing_by
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hI.choose_spec)

def pairingWeight (C : κ→κ→ℝ) (L : List (κ×κ)) : ℝ :=
  (L.map (fun a => C a.1 a.2)).prod

def pairingLabels (L : List (κ×κ)) : List κ := L.flatMap (fun a => [a.1,a.2])

def ValidPairing (I : Finset κ) (L : List (κ×κ)) : Prop :=
  (pairingLabels L).Nodup ∧ (pairingLabels L).toFinset=I

/-- Literal finite Wick polynomial equals its generated labeled pair contractions. -/
theorem covarianceWickSum_eq_pairings (C : κ→κ→ℝ) (I : Finset κ) :
    covarianceWickSum C I=((labeledWickPairings I).map (pairingWeight C)).sum := by
  induction I using Finset.strongInductionOn
  rename_i I ih
  by_cases hI : I.Nonempty
  · rw [covarianceWickSum,labeledWickPairings,dite_eq_left hI,dite_eq_left hI]
    rw [List.map_flatMap,List.flatMap_def,List.sum_flatten]
    simp only [List.map_map,Function.comp_def,pairingWeight,List.map_cons,List.prod_cons]
    rw [Finset.sum_map_toList]
    apply Finset.sum_congr rfl
    intro j hj
    have hsub : ((I.erase hI.choose).erase j)⊂I :=
      Finset.ssubset_iff_subset_ne.mpr ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _),by
        intro hEq
        have hh : hI.choose∈(I.erase hI.choose).erase j := hEq.symm ▸ hI.choose_spec
        exact (Finset.notMem_erase hI.choose I) (Finset.mem_of_mem_erase hh)⟩
    rw [ih _ hsub]
    simp only [pairingWeight,←List.sum_map_mul_left]
  · rw [covarianceWickSum,labeledWickPairings,dite_eq_right hI,dite_eq_right hI]
    simp [pairingWeight]

/-- Actual pairing labels contain two distinct original slots per pair. -/
theorem labeledWickPairings_valid (I : Finset κ) (L : List (κ×κ))
    (hL : L∈labeledWickPairings I) : ValidPairing I L := by
  induction I using Finset.strongInductionOn generalizing L
  rename_i I ih
  by_cases hI : I.Nonempty
  · rw [labeledWickPairings,dite_eq_left hI] at hL
    obtain ⟨j,hj,hL⟩ := List.mem_flatMap.mp hL
    have hj := Finset.mem_toList.mp hj
    obtain ⟨L',hL',heL⟩ := List.mem_map.mp hL
    subst L
    have hsub : ((I.erase hI.choose).erase j)⊂I :=
      Finset.ssubset_iff_subset_ne.mpr ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _),by
        intro hEq
        have hh : hI.choose∈(I.erase hI.choose).erase j := hEq.symm ▸ hI.choose_spec
        exact (Finset.notMem_erase hI.choose I) (Finset.mem_of_mem_erase hh)⟩
    obtain ⟨hn,he⟩ := ih _ hsub _ hL'
    have hi : hI.choose∈I := hI.choose_spec
    have hji : j≠hI.choose := (Finset.mem_erase.mp hj).1
    have hjI : j∈I := (Finset.mem_erase.mp hj).2
    have hnoti : hI.choose∉pairingLabels L' := by
      intro hx
      have hm : hI.choose∈((I.erase hI.choose).erase j) := by rw [←he]; exact List.mem_toFinset.mpr hx
      exact Finset.notMem_erase _ _ ((Finset.mem_erase.mp hm).2)
    have hnotj : j∉pairingLabels L' := by
      intro hx
      have hm : j∈((I.erase hI.choose).erase j) := by rw [←he]; exact List.mem_toFinset.mpr hx
      exact Finset.notMem_erase _ _ hm
    constructor
    · change (j::hI.choose::pairingLabels L').Nodup
      apply List.nodup_cons.mpr
      refine ⟨?_,List.nodup_cons.mpr ⟨hnoti,hn⟩⟩
      simpa only [List.mem_cons,not_or] using And.intro hji hnotj
    · change (j::hI.choose::pairingLabels L').toFinset=I
      simp only [List.toFinset_cons]
      rw [he]
      ext k
      simp only [Finset.mem_insert,Finset.mem_erase]
      constructor
      · intro hk
        rcases hk with hk|hk|hk
        · exact hk ▸ hjI
        · exact hk ▸ hi
        · exact hk.2.2
      · intro hk
        by_cases hkj : k=j
        · exact Or.inl hkj
        by_cases hki : k=hI.choose
        · exact Or.inr (Or.inl hki)
        exact Or.inr (Or.inr ⟨hkj,hki,hk⟩)
  · rw [labeledWickPairings,dite_eq_right hI] at hL
    have he : L=[] := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hL
    subst L
    have hIe : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simp [ValidPairing,pairingLabels,hIe]

omit [DecidableEq κ] in
theorem pairingLabels_length (L : List (κ×κ)) : (pairingLabels L).length=2*L.length := by
  induction L with
  | nil => simp [pairingLabels]
  | cons a L ih => simp only [pairingLabels,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *; omega

/-- Every genuine Wick contraction has precisely half as many pairs as labels. -/
theorem labeledWickPairings_card (I : Finset κ) (L : List (κ×κ))
    (hL : L∈labeledWickPairings I) : 2*L.length=I.card := by
  obtain ⟨hn,he⟩ := labeledWickPairings_valid I L hL
  rw [←pairingLabels_length,←he]
  exact List.toFinset_card_of_nodup hn |>.symm

end
end SlowEquilibration.FiniteWickPairings
