-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionClosedBandGraph
public import SlowEquilibration.SphericalKacRiceHittingSource

@[expose] public section

/-! Compact-fiber closed projection for any prescribed number of physically
separated original critical centers. This is the quantitative Borel building
block for the cardinality assertion in manuscript `lem:red-unions` (c). -/

namespace SlowEquilibration.SourceReductionSeparatedCenterTuples
noncomputable section
open Set MeasureTheory SphericalModel SphericalKacRiceHittingSource
open SourceReductionClosedBandGraph SphericalRotationCovariance
open SphericalAging.HardSphereDynamics PairConditionalDeterminantMoments
open scoped Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.style.haveILetI false

variable {N : ℕ}

def separatedWindowTupleGraph (μ : FiniteMixture) (Q m M : ℝ)
    (U : Set ℝ) (k : ℕ) (r : ℝ) :
    Set (Disorder N μ.maxDegree × (Fin k → PhysicalSphere N)) :=
  {z | (∀ i, (z.1,(z.2 i).1) ∈ windowCenterGraph μ Q m M U) ∧
    ∀ i j : Fin k, i ≠ j → r ≤ dist (z.2 i) (z.2 j)}

theorem separatedWindowTupleGraph_isClosed (μ : FiniteMixture)
    (Q m M : ℝ) {U : Set ℝ} (hU : IsClosed U) (k : ℕ) (r : ℝ) :
    IsClosed (separatedWindowTupleGraph (N := N) μ Q m M U k r) := by
  have hC : IsClosed {z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) |
      ∀ i, (z.1,(z.2 i).1) ∈ windowCenterGraph μ Q m M U} := by
    have hc' : IsClosed (⋂ i : Fin k,
        {z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) |
          (z.1,(z.2 i).1) ∈ windowCenterGraph μ Q m M U}) := by
      apply isClosed_iInter
      intro i
      exact (windowCenterGraph_isClosed μ Q m M hU).preimage
        (continuous_fst.prodMk
          (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))
    simpa only [Set.iInter_ofPred] using hc'
  have hS : IsClosed {z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) |
      ∀ i j : Fin k, i ≠ j → r ≤ dist (z.2 i) (z.2 j)} := by
    have hs' : IsClosed (⋂ i : Fin k, ⋂ j : Fin k,
        {z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) |
          i ≠ j → r ≤ dist (z.2 i) (z.2 j)}) := by
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro j
      by_cases hij : i = j
      · simp [hij]
      · have hc : Continuous (fun z : Disorder N μ.maxDegree × (Fin k → PhysicalSphere N) =>
            dist (z.2 i) (z.2 j)) := by fun_prop
        simpa [hij] using (isClosed_le continuous_const hc)
    simpa only [Set.iInter_ofPred] using hs'
  exact hC.inter hS

def separatedWindowCentersEvent (μ : FiniteMixture) (Q m M : ℝ)
    (U : Set ℝ) (k : ℕ) (r : ℝ) : Set (Disorder N μ.maxDegree) :=
  {J | ∃ v : Fin k → PhysicalSphere N,
    (∀ i, (J,(v i).1) ∈ windowCenterGraph μ Q m M U) ∧
    ∀ i j : Fin k, i ≠ j → r ≤ dist (v i) (v j)}

theorem separatedWindowCentersEvent_isClosed (μ : FiniteMixture)
    (Q m M : ℝ) {U : Set ℝ} (hU : IsClosed U) (k : ℕ) (r : ℝ) :
    IsClosed (separatedWindowCentersEvent (N := N) μ Q m M U k r) := by
  have hS : IsCompact {x : Vector N | OnSphere x} := by
    convert sourceSphere_compact N using 1
    ext x
    exact onSphere_iff_norm_sq x
  letI : CompactSpace (PhysicalSphere N) :=
    isCompact_iff_compactSpace.mp hS
  have hProj : IsClosed (Prod.fst '' separatedWindowTupleGraph
      (N := N) μ Q m M U k r) :=
    isClosedMap_fst_of_compactSpace _
      (separatedWindowTupleGraph_isClosed μ Q m M hU k r)
  convert hProj using 1
  ext J
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨(J,v),hv,rfl⟩
  · rintro ⟨z,hz,hzJ⟩
    subst J
    exact ⟨z.2,hz⟩

end
end SlowEquilibration.SourceReductionSeparatedCenterTuples
