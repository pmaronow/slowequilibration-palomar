-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionSeparatedCenterTuples
public import Mathlib.MeasureTheory.MeasurableSpace.NCard

@[expose] public section

/-! Borel finiteness of the literal critical-center fibers, obtained by a
countable family of compactly projected, uniformly separated tuples. -/

namespace SlowEquilibration.SourceReductionFiniteFiberBorel
noncomputable section
open Set MeasureTheory SphericalModel SphericalKacRiceHittingSource
open SourceReductionClosedBandGraph SourceReductionSeparatedCenterTuples
open SphericalAging.HardSphereDynamics PairConditionalDeterminantMoments
open SphericalRotationCovariance
open scoped Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000

variable {N : ℕ}

/-- A literal fiber has at least `k` centers iff some positive reciprocal
scale supports a pairwise separated `k`-tuple of its physical centers. -/
theorem windowCenters_encard_ge_iff_separated_event
    (μ : FiniteMixture) (Q m M : ℝ) (U : Set ℝ)
    (J : Disorder N μ.maxDegree) (k : ℕ) :
    (k : ℕ∞) ≤ (windowCenters μ Q m M U J).encard ↔
      ∃ n : ℕ, J ∈ separatedWindowCentersEvent μ Q m M U k
        (1 / ((n+1:ℕ):ℝ)) := by
  classical
  constructor
  · intro hk
    have hfin : (Set.univ : Set (Fin k)).Finite := Set.toFinite _
    obtain ⟨f,hf,hinj⟩ := hfin.exists_injOn_of_encard_le
      (by simpa using hk)
    have hmem (i : Fin k) : f i ∈ windowCenters μ Q m M U J :=
      hf (Set.mem_univ i)
    let v : Fin k → PhysicalSphere N := fun i =>
      ⟨f i,(onSphere_iff_norm_sq (f i)).mpr (by
        have hi := hmem i
        change (J,f i) ∈ windowCenterGraph μ Q m M U at hi
        unfold windowCenterGraph at hi
        exact hi.1.1.1)⟩
    have hv (i : Fin k) : (J,(v i).1) ∈ windowCenterGraph μ Q m M U :=
      hmem i
    have hvinj : Function.Injective v := by
      intro i j hij
      apply hinj (Set.mem_univ i) (Set.mem_univ j)
      exact congrArg Subtype.val hij
    by_cases hk0 : k = 0
    · refine ⟨0,v,hv,?_⟩
      intro i
      exact Fin.elim0 (hk0 ▸ i)
    · let i₀ : Fin k := ⟨0,Nat.pos_of_ne_zero hk0⟩
      let F : Finset ℝ := (Finset.univ : Finset (Fin k × Fin k)).image
        (fun ij => if ij.1 = ij.2 then (1:ℝ) else dist (v ij.1) (v ij.2))
      have hF : F.Nonempty := by
        exact Finset.Nonempty.image (⟨(i₀,i₀),Finset.mem_univ _⟩) _
      have hFpos (r : ℝ) (hr : r ∈ F) : 0 < r := by
        obtain ⟨ij,_,rfl⟩ := Finset.mem_image.mp hr
        by_cases hij : ij.1 = ij.2
        · simp [hij]
        · simp only [hij, ↓reduceIte]
          exact dist_pos.mpr (hvinj.ne hij)
      let r := F.min' hF
      have hr : 0 < r := hFpos r (Finset.min'_mem F hF)
      obtain ⟨n,hn⟩ := exists_nat_gt (1/r)
      have hscale : 1 / ((n+1:ℕ):ℝ) ≤ r := by
        have hmul := mul_lt_mul_of_pos_right hn hr
        have hInv : (1/r)*r = 1 := by field_simp
        have hcast : (n:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast (Nat.le_succ n)
        apply (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
        nlinarith [hInv]
      refine ⟨n,v,hv,?_⟩
      intro i j hij
      have hdist : r ≤ dist (v i) (v j) := by
        have hm : (if i = j then (1:ℝ) else dist (v i) (v j)) ∈ F :=
          Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩
        simpa only [hij, ↓reduceIte] using Finset.min'_le F _ hm
      exact hscale.trans hdist
  · rintro ⟨n,v,hv,hsep⟩
    have hVinJ : Function.Injective (fun i : Fin k => (v i).1) := by
      intro i j hij
      have hEq : v i = v j := Subtype.ext hij
      by_contra hne
      have hdist := hsep i j hne
      rw [hEq,dist_self] at hdist
      have hpositive : 0 < 1 / ((n+1:ℕ):ℝ) := by positivity
      linarith
    have hmap : Set.MapsTo (fun i : Fin k => (v i).1)
        Set.univ (windowCenters μ Q m M U J) := by
      intro i _
      exact hv i
    have hcard := Set.encard_le_encard_of_injOn hmap
      (hVinJ.injOn)
    simpa using hcard

/-- The set of disorders with infinitely many literal window centers is
Borel, despite the failure of fiber cardinality to be semicontinuous. -/
theorem windowCenters_infinite_measurableSet (μ : FiniteMixture)
    (Q m M : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    MeasurableSet {J : Disorder N μ.maxDegree |
      (windowCenters μ Q m M U J).Infinite} := by
  have hLarge (k : ℕ) : MeasurableSet {J : Disorder N μ.maxDegree |
      (k : ℕ∞) ≤ (windowCenters μ Q m M U J).encard} := by
    have hEq : {J : Disorder N μ.maxDegree |
        (k : ℕ∞) ≤ (windowCenters μ Q m M U J).encard} =
        ⋃ n : ℕ, separatedWindowCentersEvent μ Q m M U k
          (1 / ((n+1:ℕ):ℝ)) := by
      ext J
      simpa only [Set.mem_ofPred_eq,Set.mem_iUnion] using
        windowCenters_encard_ge_iff_separated_event μ Q m M U J k
    rw [hEq]
    exact MeasurableSet.iUnion (fun n =>
      (separatedWindowCentersEvent_isClosed μ Q m M hU k _).measurableSet)
  have hEq : {J : Disorder N μ.maxDegree |
      (windowCenters μ Q m M U J).Infinite} =
      ⋂ k : ℕ, {J : Disorder N μ.maxDegree |
        (k : ℕ∞) ≤ (windowCenters μ Q m M U J).encard} := by
    ext J
    constructor
    · intro hJ
      simp only [Set.mem_iInter,Set.mem_ofPred_eq]
      intro k
      rw [hJ.encard_eq]
      exact le_top
    · intro hJ
      by_contra hfin
      have hs : (windowCenters μ Q m M U J).Finite := by
        simpa only [Set.mem_ofPred_eq,Set.Infinite,not_not] using hfin
      obtain ⟨k,hk⟩ := hs.exists_encard_eq_coe
      have hlarge := (Set.mem_iInter.mp hJ) (k+1)
      change ((k+1:ℕ):ℕ∞) ≤ (windowCenters μ Q m M U J).encard at hlarge
      rw [hk] at hlarge
      exact (by norm_cast at hlarge; omega)
  rw [hEq]
  exact MeasurableSet.iInter hLarge

theorem windowCenters_finite_measurableSet (μ : FiniteMixture)
    (Q m M : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    MeasurableSet {J : Disorder N μ.maxDegree |
      (windowCenters μ Q m M U J).Finite} := by
  have h := windowCenters_infinite_measurableSet (N := N) μ Q m M hU
  convert h.compl using 1
  ext J
  simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,Set.Infinite,not_not]

end
end SlowEquilibration.SourceReductionFiniteFiberBorel
