-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionSortedCenterTuples
public import SlowEquilibration.SourceReductionFixedCenterWeight
public import SlowEquilibration.SourceReductionWeightedCenterScore

@[expose] public section

/-! Borel weighted sums over finite original-disorder critical-center
fibers, using the unique lexicographically ordered tuple and Lusin--Souslin. -/

namespace SlowEquilibration.SourceReductionWeightedFiberBorel
noncomputable section
open Set MeasureTheory SphericalModel SphericalRotationCovariance
open SourceReductionClosedBandGraph SourceReductionFinitePathUnionBound
open SourceReductionFiberCardinalityBorel SourceReductionSortedCenterTuples
open SourceReductionFiniteFiberBorel
open SourceReductionFixedCenterWeight
open SourceReductionWeightedCenterScore
open SourceReductionPhysicalLexOrder SourceReductionTrueCapPathWeight
open ConditionedEntrance
open SphericalAging.HardSphereDynamics
open scoped Topology RealInnerProductSpace NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {N : ℕ}

def sortedTupleWeight (μ : FiniteMixture)
    (k : ℕ) (f : Disorder N μ.maxDegree × PhysicalSphere N → ℝ≥0∞)
    (z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N)) : ℝ≥0∞ :=
  ∑ i : Fin k, f (z.1,z.2 i)

theorem sortedTupleWeight_measurable (μ : FiniteMixture)
    (k : ℕ)
    (f : Disorder N μ.maxDegree × PhysicalSphere N → ℝ≥0∞)
    (hf : Measurable f) :
    Measurable (sortedTupleWeight μ k f) := by
  unfold sortedTupleWeight
  apply Finset.measurable_fun_sum
  intro i _
  exact hf.comp (measurable_fst.prodMk
    ((measurable_pi_apply i).comp measurable_snd))

/-- Every Borel test of a sorted tuple's weighted sum has Borel image in
the original disorder, because its first-coordinate projection is injective
on the exact-cardinality sorted center graph. -/
theorem sortedTupleWeight_image_measurableSet (μ : FiniteMixture)
    (Q m M : ℝ) {U : Set ℝ} (hU : IsClosed U) (k : ℕ)
    (f : Disorder N μ.maxDegree × PhysicalSphere N → ℝ≥0∞)
    (hf : Measurable f) (B : Set ℝ≥0∞) (hB : MeasurableSet B) :
    MeasurableSet (Prod.fst ''
      (sortedWindowTupleGraph μ Q m M U k ∩
        {z | sortedTupleWeight μ k f z ∈ B})) := by
  have hGraph := sortedWindowTupleGraph_measurableSet (N := N) μ Q m M hU k
  have hSum := sortedTupleWeight_measurable μ k f hf
  have hSet : MeasurableSet
      (sortedWindowTupleGraph μ Q m M U k ∩
        {z | sortedTupleWeight μ k f z ∈ B}) :=
    hGraph.inter (hB.preimage hSum)
  have hSphereClosed : IsClosed {x : Vector N | OnSphere x} := by
    have hh : IsClosed {x : Vector N | ‖x‖^2=(N:ℝ)} :=
      isClosed_eq (continuous_norm.pow 2) continuous_const
    convert hh using 1
    ext x
    exact onSphere_iff_norm_sq x
  letI : PolishSpace (PhysicalSphere N) := hSphereClosed.polishSpace
  exact hSet.image_of_continuousOn_injOn continuous_fst.continuousOn
    ((sortedWindowTupleGraph_fst_injOn μ Q m M U k).mono inter_subset_left)

/-- The finite-fiber sum for any jointly Borel nonnegative center weight,
extended by `⊤` on an infinite center fiber. -/
def finiteFiberWeightedSum (μ : FiniteMixture)
    (Q m M : ℝ) (U : Set ℝ)
    (f : Disorder N μ.maxDegree × PhysicalSphere N → ℝ≥0∞)
    (J : Disorder N μ.maxDegree) : ℝ≥0∞ := by
  classical
  exact if hfinite : (windowCenters μ Q m M U J).Finite then
    ∑ u ∈ (physicalWindowCenters_finite μ Q m M U J hfinite).toFinset,
      f (J,u)
  else ⊤

theorem finiteFiberWeightedSum_of_finite (μ : FiniteMixture)
    (Q m M : ℝ) (U : Set ℝ)
    (f : Disorder N μ.maxDegree × PhysicalSphere N → ℝ≥0∞)
    (J : Disorder N μ.maxDegree)
    (hfinite : (windowCenters μ Q m M U J).Finite) :
    finiteFiberWeightedSum μ Q m M U f J =
      ∑ u ∈ (physicalWindowCenters_finite μ Q m M U J hfinite).toFinset,
        f (J,u) := by
  classical
  simp [finiteFiberWeightedSum, hfinite]

theorem finiteFiberWeightedSum_of_infinite (μ : FiniteMixture)
    (Q m M : ℝ) (U : Set ℝ)
    (f : Disorder N μ.maxDegree × PhysicalSphere N → ℝ≥0∞)
    (J : Disorder N μ.maxDegree)
    (hinfinite : (windowCenters μ Q m M U J).Infinite) :
    finiteFiberWeightedSum μ Q m M U f J = ⊤ := by
  classical
  have hnot : ¬ (windowCenters μ Q m M U J).Finite := hinfinite
  simp only [finiteFiberWeightedSum, dite_eq_right hnot]

theorem finiteFiberWeightedSum_eq_sortedTupleWeight
    (μ : FiniteMixture) (Q m M : ℝ) (U : Set ℝ) (k : ℕ)
    (f : Disorder N μ.maxDegree × PhysicalSphere N → ℝ≥0∞)
    (J : Disorder N μ.maxDegree) (v : Fin k → PhysicalSphere N)
    (hv : (J,v) ∈ sortedWindowTupleGraph μ Q m M U k) :
    finiteFiberWeightedSum μ Q m M U f J = sortedTupleWeight μ k f (J,v) := by
  classical
  letI := physicalLexOrder N
  have hcard : (physicalWindowCenters μ Q m M U J).encard = (k:ℕ∞) := by
    rw [physicalWindowCenters_encard_eq]
    exact hv.1
  have hfinite : (windowCenters μ Q m M U J).Finite :=
    Set.finite_of_encard_eq_coe hv.1
  let hs := physicalWindowCenters_finite μ Q m M U J hfinite
  let t := hs.toFinset
  have htcard : t.card = k := by
    have hh := hs.encard_eq_coe_toFinset_card
    change (physicalWindowCenters μ Q m M U J).encard = (t.card:ℕ∞) at hh
    rw [hcard] at hh
    exact_mod_cast hh.symm
  have hvMono : StrictMono v := by
    intro i j hij
    exact (physicalLexBefore_iff_lt (v i) (v j)).mp (hv.2.2 i j hij)
  have hmem (i : Fin k) : v i ∈ t :=
    hs.mem_toFinset.mpr (hv.2.1 i)
  have heq : v = t.orderEmbOfFin htcard :=
    Finset.orderEmbOfFin_unique htcard hmem hvMono
  rw [finiteFiberWeightedSum_of_finite μ Q m M U f J hfinite]
  change (∑ u ∈ t, f (J,u)) = sortedTupleWeight μ k f (J,v)
  rw [heq]
  unfold sortedTupleWeight
  have hsum :=
    (Finset.sum_image (s := Finset.univ) (f := fun u => f (J,u))
      (t.orderEmbOfFin htcard).injective.injOn)
  have himg : Finset.image (t.orderEmbOfFin htcard) Finset.univ = t := by
    ext u
    constructor
    · intro hu
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
      exact Finset.orderEmbOfFin_mem t htcard i
    · intro hu
      obtain ⟨i,rfl⟩ := (Finset.range_orderEmbOfFin t htcard).ge hu
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [himg] at hsum
  exact hsum

/-- A Borel center weight has a Borel extended sum over the literal
window-critical-center fiber, including the prescribed `⊤` at infinity. -/
theorem finiteFiberWeightedSum_measurable (μ : FiniteMixture)
    (Q m M : ℝ) {U : Set ℝ} (hU : IsClosed U)
    (f : Disorder N μ.maxDegree × PhysicalSphere N → ℝ≥0∞)
    (hf : Measurable f) :
    Measurable (finiteFiberWeightedSum μ Q m M U f) := by
  intro B hB
  let G (k : ℕ) : Set (Disorder N μ.maxDegree × (Fin k → PhysicalSphere N)) :=
    sortedWindowTupleGraph μ Q m M U k ∩
      {z | sortedTupleWeight μ k f z ∈ B}
  have hInf : MeasurableSet {J : Disorder N μ.maxDegree |
      (windowCenters μ Q m M U J).Infinite ∧ (⊤:ℝ≥0∞) ∈ B} := by
    by_cases htop : (⊤:ℝ≥0∞) ∈ B
    · simpa only [htop,and_true] using
        windowCenters_infinite_measurableSet (N := N) μ Q m M hU
    · simp only [htop,and_false,Set.ofPred_false]
      exact MeasurableSet.empty
  have hFin : MeasurableSet (⋃ k : ℕ, Prod.fst '' G k) := by
    apply MeasurableSet.iUnion
    intro k
    exact sortedTupleWeight_image_measurableSet μ Q m M hU k f hf B hB
  have hEq : {J : Disorder N μ.maxDegree |
      finiteFiberWeightedSum μ Q m M U f J ∈ B} =
      {J | (windowCenters μ Q m M U J).Infinite ∧ (⊤:ℝ≥0∞) ∈ B} ∪
        ⋃ k : ℕ, Prod.fst '' G k := by
    ext J
    constructor
    · intro hJ
      change finiteFiberWeightedSum μ Q m M U f J ∈ B at hJ
      by_cases hfinite : (windowCenters μ Q m M U J).Finite
      · obtain ⟨k,hcard⟩ := hfinite.exists_encard_eq_coe
        obtain ⟨v,hv⟩ :=
          exists_sortedWindowTuple_of_encard_eq μ Q m M U k J hcard
        right
        refine Set.mem_iUnion.mpr ⟨k,?_⟩
        refine ⟨(J,v),⟨hv,?_⟩,rfl⟩
        change sortedTupleWeight μ k f (J,v) ∈ B
        rw [finiteFiberWeightedSum_eq_sortedTupleWeight μ Q m M U k f J v hv] at hJ
        exact hJ
      · left
        have hinfinite : (windowCenters μ Q m M U J).Infinite := hfinite
        rw [finiteFiberWeightedSum_of_infinite μ Q m M U f J hinfinite] at hJ
        exact ⟨hinfinite,hJ⟩
    · intro hJ
      change finiteFiberWeightedSum μ Q m M U f J ∈ B
      rcases hJ with hJ | hJ
      · rw [finiteFiberWeightedSum_of_infinite μ Q m M U f J hJ.1]
        exact hJ.2
      · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hJ
        obtain ⟨z,hz,hzJ⟩ := hk
        have hzgraph : z ∈ sortedWindowTupleGraph μ Q m M U k := hz.1
        have hzw : sortedTupleWeight μ k f z ∈ B := hz.2
        subst J
        rcases z with ⟨J,v⟩
        rw [finiteFiberWeightedSum_eq_sortedTupleWeight
          μ Q m M U k f J v hzgraph]
        exact hzw
  change MeasurableSet {J : Disorder N μ.maxDegree |
    finiteFiberWeightedSum μ Q m M U f J ∈ B}
  rw [hEq]
  exact hInf.union hFin

/-- The manuscript's literal weighted center score `S(H)` is Borel as an
extended-real function of the original Gaussian tensor disorder. -/
theorem actualWindowCenterWeightedHitSum_measurable (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M a β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (T : ℝ≥0) :
    Measurable (actualWindowCenterWeightedHitSum (N := N) μ Q m M a β U T) := by
  let f : Disorder N μ.maxDegree × PhysicalSphere N → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (originalTrueCapHitProbability μ β T a z.2.1 z.1)
  have hf : Measurable f :=
    originalTrueCapHitProbability_joint_measurable hN μ β T a
  have heq (J : Disorder N μ.maxDegree) :
      actualWindowCenterWeightedHitSum μ Q m M a β U T J =
        finiteFiberWeightedSum μ Q m M U f J := by
    by_cases hfinite : (windowCenters μ Q m M U J).Finite
    · rw [actualWindowCenterWeightedHitSum_of_finite μ Q m M a β U T J hfinite,
        finiteFiberWeightedSum_of_finite μ Q m M U f J hfinite]
    · have hinfinite : (windowCenters μ Q m M U J).Infinite := hfinite
      rw [actualWindowCenterWeightedHitSum_of_infinite μ Q m M a β U T J hinfinite,
        finiteFiberWeightedSum_of_infinite μ Q m M U f J hinfinite]
  have hfun : actualWindowCenterWeightedHitSum μ Q m M a β U T =
      finiteFiberWeightedSum μ Q m M U f := funext heq
  rw [hfun]
  exact finiteFiberWeightedSum_measurable μ Q m M hU f hf

end
end SlowEquilibration.SourceReductionWeightedFiberBorel
