-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionPhysicalLexOrder
public import SlowEquilibration.SourceReductionFinitePathUnionBound
public import Mathlib.Data.Finset.Sort
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-! Each exact-cardinality fiber has a Borel graph of lexicographically
sorted tuples. The disorder projection is injective, preparing a genuine
Borel enumeration through Lusin--Souslin. -/

namespace SlowEquilibration.SourceReductionSortedCenterTuples
noncomputable section
open Set MeasureTheory SphericalModel SphericalRotationCovariance
open SourceReductionClosedBandGraph SourceReductionFinitePathUnionBound
open SourceReductionSeparatedCenterTuples SourceReductionFiniteFiberBorel
open SourceReductionFiberCardinalityBorel SourceReductionPhysicalLexOrder
open SphericalAging.HardSphereDynamics PairConditionalDeterminantMoments
open scoped Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false

variable {N : ℕ}

def sortedWindowTupleGraph (μ : FiniteMixture) (Q m M : ℝ)
    (U : Set ℝ) (k : ℕ) :
    Set (Disorder N μ.maxDegree × (Fin k → PhysicalSphere N)) :=
  {z | (windowCenters μ Q m M U z.1).encard = (k:ℕ∞) ∧
    (∀ i, (z.1,(z.2 i).1) ∈ windowCenterGraph μ Q m M U) ∧
    ∀ i j : Fin k, i < j → physicalLexBefore (z.2 i) (z.2 j)}

theorem sortedWindowTupleGraph_measurableSet (μ : FiniteMixture)
    (Q m M : ℝ) {U : Set ℝ} (hU : IsClosed U) (k : ℕ) :
    MeasurableSet (sortedWindowTupleGraph (N := N) μ Q m M U k) := by
  have hCard : MeasurableSet {z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) |
      (windowCenters μ Q m M U z.1).encard = (k:ℕ∞)} :=
    ((windowCenters_encard_measurable μ Q m M hU).comp measurable_fst)
      (measurableSet_singleton _)
  have hCenter : MeasurableSet
      {z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) |
        ∀ i, (z.1,(z.2 i).1) ∈ windowCenterGraph μ Q m M U} := by
    have hEq : {z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) |
        ∀ i, (z.1,(z.2 i).1) ∈ windowCenterGraph μ Q m M U} =
        separatedWindowTupleGraph μ Q m M U k 0 := by
      ext z
      simp [separatedWindowTupleGraph,dist_nonneg]
    rw [hEq]
    exact (separatedWindowTupleGraph_isClosed μ Q m M hU k 0).measurableSet
  have hSort : MeasurableSet
      {z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) |
        ∀ i j : Fin k, i < j → physicalLexBefore (z.2 i) (z.2 j)} := by
    have hS : MeasurableSet (⋂ i : Fin k, ⋂ j : Fin k,
        {z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) |
          i < j → physicalLexBefore (z.2 i) (z.2 j)}) := by
      apply MeasurableSet.iInter
      intro i
      apply MeasurableSet.iInter
      intro j
      by_cases hij : i < j
      · have hc : Continuous (fun z : Disorder N μ.maxDegree ×
            (Fin k → PhysicalSphere N) => (z.2 i,z.2 j)) := by fun_prop
        simpa [hij] using physicalLexBefore_measurableSet.preimage hc.measurable
      · simp [hij]
    simpa only [Set.iInter_ofPred] using hS
  have hEq : sortedWindowTupleGraph (N := N) μ Q m M U k =
    ({z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) |
      (windowCenters μ Q m M U z.1).encard = (k:ℕ∞)} ∩
      {z | ∀ i, (z.1,(z.2 i).1) ∈ windowCenterGraph μ Q m M U} ∩
      {z | ∀ i j : Fin k, i < j → physicalLexBefore (z.2 i) (z.2 j)}) := by
    ext z
    simp only [sortedWindowTupleGraph,Set.mem_ofPred_eq,Set.mem_inter_iff,and_assoc]
  rw [hEq]
  exact (hCard.inter hCenter).inter hSort

theorem physicalWindowCenters_encard_eq (μ : FiniteMixture)
    (Q m M : ℝ) (U : Set ℝ) (J : Disorder N μ.maxDegree) :
    (physicalWindowCenters μ Q m M U J).encard =
      (windowCenters μ Q m M U J).encard := by
  let s := physicalWindowCenters μ Q m M U J
  have himg : (fun u : PhysicalSphere N => u.1) '' s =
      windowCenters μ Q m M U J := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact hu
    · intro hx
      have hwin : (J,x) ∈ windowCenterGraph μ Q m M U := hx
      have hsphere : OnSphere x := by
        unfold windowCenterGraph at hwin
        exact (onSphere_iff_norm_sq x).mpr hwin.1.1.1
      exact ⟨⟨x,hsphere⟩,hx,rfl⟩
  calc
    s.encard = ((fun u : PhysicalSphere N => u.1) '' s).encard :=
      (Subtype.val_injective.encard_image s).symm
    _ = _ := by rw [himg]

theorem sortedWindowTupleGraph_fst_injOn (μ : FiniteMixture)
    (Q m M : ℝ) (U : Set ℝ) (k : ℕ) :
    Set.InjOn Prod.fst (sortedWindowTupleGraph (N := N) μ Q m M U k) := by
  letI := physicalLexOrder N
  intro z hz w hw heq
  cases z with
  | mk J v =>
    cases w with
    | mk J' t =>
      dsimp only at heq
      subst J'
      have hsCard : (physicalWindowCenters μ Q m M U J).encard = (k:ℕ∞) := by
        rw [physicalWindowCenters_encard_eq]
        exact hz.1
      have hfinite : (physicalWindowCenters μ Q m M U J).Finite :=
        Set.finite_of_encard_eq_coe hsCard
      have hvMono : StrictMono v := by
        intro i j hij
        exact (physicalLexBefore_iff_lt (v i) (v j)).mp (hz.2.2 i j hij)
      have htMono : StrictMono t := by
        intro i j hij
        exact (physicalLexBefore_iff_lt (t i) (t j)).mp (hw.2.2 i j hij)
      have hvSub : Set.range v ⊆ physicalWindowCenters μ Q m M U J := by
        rintro u ⟨i,rfl⟩
        exact hz.2.1 i
      have htSub : Set.range t ⊆ physicalWindowCenters μ Q m M U J := by
        rintro u ⟨i,rfl⟩
        exact hw.2.1 i
      have hvCard : (Set.range v).encard = (k:ℕ∞) := by
        rw [hvMono.injective.encard_range]
        simp
      have htCard : (Set.range t).encard = (k:ℕ∞) := by
        rw [htMono.injective.encard_range]
        simp
      have hvRange : Set.range v = physicalWindowCenters μ Q m M U J :=
        (Set.finite_range v).eq_of_subset_of_encard_le hvSub
          (by rw [hsCard,hvCard])
      have htRange : Set.range t = physicalWindowCenters μ Q m M U J :=
        (Set.finite_range t).eq_of_subset_of_encard_le htSub
          (by rw [hsCard,htCard])
      have hvt : v=t :=
        (hvMono.range_inj_of_wellFoundedLT htMono).mp (hvRange.trans htRange.symm)
      subst t
      rfl

theorem exists_sortedWindowTuple_of_encard_eq (μ : FiniteMixture)
    (Q m M : ℝ) (U : Set ℝ) (k : ℕ)
    (J : Disorder N μ.maxDegree)
    (hcard : (windowCenters μ Q m M U J).encard = (k:ℕ∞)) :
    ∃ v : Fin k → PhysicalSphere N,
      (J,v) ∈ sortedWindowTupleGraph μ Q m M U k := by
  letI := physicalLexOrder N
  let s := physicalWindowCenters μ Q m M U J
  have hsCard : s.encard = (k:ℕ∞) := by
    rw [physicalWindowCenters_encard_eq]
    exact hcard
  have hsfinite : s.Finite := Set.finite_of_encard_eq_coe hsCard
  let t := hsfinite.toFinset
  have htcard : t.card = k := by
    have hh := hsfinite.encard_eq_coe_toFinset_card
    change s.encard = (t.card:ℕ∞) at hh
    rw [hsCard] at hh
    exact_mod_cast hh.symm
  let v : Fin k → PhysicalSphere N := t.orderEmbOfFin htcard
  refine ⟨v,hcard,?_,?_⟩
  · intro i
    have hi : v i ∈ s := by
      exact hsfinite.mem_toFinset.mp (t.orderEmbOfFin_mem htcard i)
    exact hi
  · intro i j hij
    exact (physicalLexBefore_iff_lt (v i) (v j)).mpr
      ((t.orderEmbOfFin htcard).strictMono hij)

theorem sortedWindowTupleGraph_fst_image (μ : FiniteMixture)
    (Q m M : ℝ) (U : Set ℝ) (k : ℕ) :
    Prod.fst '' sortedWindowTupleGraph (N := N) μ Q m M U k =
      {J : Disorder N μ.maxDegree |
        (windowCenters μ Q m M U J).encard = (k:ℕ∞)} := by
  ext J
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact hz.1
  · intro hJ
    obtain ⟨v,hv⟩ := exists_sortedWindowTuple_of_encard_eq μ Q m M U k J hJ
    exact ⟨(J,v),hv,rfl⟩

end
end SlowEquilibration.SourceReductionSortedCenterTuples
