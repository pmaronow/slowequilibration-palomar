-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionFiniteFiberBorel

@[expose] public section

/-! The extended natural cardinality of the actual original-disorder
critical-center fiber is Borel, including the infinite-fiber value `⊤`. -/

namespace SlowEquilibration.SourceReductionFiberCardinalityBorel
noncomputable section
open Set MeasureTheory SphericalModel SourceReductionClosedBandGraph
open SourceReductionSeparatedCenterTuples
open SourceReductionFiniteFiberBorel
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 700000

variable {N : ℕ}

theorem windowCenters_encard_measurable (μ : FiniteMixture)
    (Q m M : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    Measurable (fun J : Disorder N μ.maxDegree =>
      (windowCenters μ Q m M U J).encard) := by
  let F : Disorder N μ.maxDegree → ℕ∞ :=
    fun J => (windowCenters μ Q m M U J).encard
  have hLarge (k : ℕ) : MeasurableSet {J : Disorder N μ.maxDegree |
      (k : ℕ∞) ≤ F J} := by
    have hEq : {J : Disorder N μ.maxDegree | (k : ℕ∞) ≤ F J} =
        ⋃ n : ℕ, separatedWindowCentersEvent μ Q m M U k
          (1 / ((n+1:ℕ):ℝ)) := by
      ext J
      simpa only [F,Set.mem_ofPred_eq,Set.mem_iUnion] using
        windowCenters_encard_ge_iff_separated_event μ Q m M U J k
    rw [hEq]
    exact MeasurableSet.iUnion (fun n =>
      (separatedWindowCentersEvent_isClosed μ Q m M hU k _).measurableSet)
  apply ENat.measurable_iff.mpr
  intro k
  have hEq : F ⁻¹' {(k:ℕ∞)} =
      {J : Disorder N μ.maxDegree | (k:ℕ∞) ≤ F J} \
      {J : Disorder N μ.maxDegree | ((k+1:ℕ):ℕ∞) ≤ F J} := by
    ext J
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_sdiff,Set.mem_ofPred_eq]
    constructor
    · intro h
      rw [h]
      exact ⟨le_refl _, by norm_cast; omega⟩
    · rintro ⟨hlo,hhi⟩
      cases hval : F J with
      | top =>
          exact False.elim (hhi (by rw [hval]; exact le_top))
      | coe n =>
          have hkn : k ≤ n := by
            rw [hval] at hlo
            exact_mod_cast hlo
          have hnk : n < k+1 := by
            have hh : ¬ k+1 ≤ n := by
              intro hh
              apply hhi
              rw [hval]
              exact_mod_cast hh
            omega
          have heq : n=k := by omega
          simp only [heq]
  rw [hEq]
  exact (hLarge k).diff (hLarge (k+1))

end
end SlowEquilibration.SourceReductionFiberCardinalityBorel
