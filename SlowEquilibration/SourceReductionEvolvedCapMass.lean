-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionUniformPathMarginal
public import SlowEquilibration.SourceReductionPointCapMass

/-! The original uniform-start Langevin semigroup assigns no more mass to
the literal critical-center cap union at a given time than the probability
of visiting that union at some time in the continuous path horizon. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionEvolvedCapMass
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalDynamics
open SourceReductionPointCapMass SourceReductionUniformPathMarginal
open SourceReductionPathMarginal
open SourceReductionClosedBandGraph SourceReductionClosedPathUnionGraph
open SourceReductionCompactBandProjection
open SphericalKacRiceHittingSource SphericalRealTimePathKernel
open SphericalRotationCovariance SphericalFieldKernels
open SphericalAging.HardSphereDynamics PairConditionalDeterminantMoments
open scoped NNReal ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {N : ℕ}

def ambientPointCapUnion (μ : FiniteMixture) (Q m M a : ℝ)
    (U : Set ℝ) (J : Disorder N μ.maxDegree) : Set (Vector N) :=
  Subtype.val '' {x : PhysicalSphere N |
    (J,x) ∈ pointCapUnionGraph μ Q m M a U}

theorem ambientPointCapUnion_isClosed (μ : FiniteMixture)
    (Q m M a : ℝ) {U : Set ℝ} (hU : IsClosed U)
    (J : Disorder N μ.maxDegree) :
    IsClosed (ambientPointCapUnion μ Q m M a U J) := by
  have hS : IsCompact {x : Vector N | OnSphere x} := by
    convert sourceSphere_compact N using 1
    ext x
    exact onSphere_iff_norm_sq x
  letI : CompactSpace (PhysicalSphere N) :=
    isCompact_iff_compactSpace.mp hS
  have hF : IsClosed {x : PhysicalSphere N |
      (J,x) ∈ pointCapUnionGraph μ Q m M a U} :=
    (pointCapUnionGraph_isClosed (N := N) μ Q m M a hU).preimage
      (continuous_const.prodMk continuous_id)
  exact (hF.isCompact.image continuous_subtype_val).isClosed

theorem evolved_pointCap_le_pathHit (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M a β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (t : RealPathTime T) :
    (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real
      (ambientPointCapUnion μ Q m M a U J) ≤
      actualWindowPathHitProbability hN μ Q m M a β U T J := by
  have hA : MeasurableSet (ambientPointCapUnion μ Q m M a U J) :=
    (ambientPointCapUnion_isClosed μ Q m M a hU J).measurableSet
  have hE : {p : RealSpherePath N T |
      (p t).1 ∈ ambientPointCapUnion μ Q m M a U J} =
      {p | (J,p t) ∈ pointCapUnionGraph μ Q m M a U} := by
    ext p
    change (∃ x : PhysicalSphere N,
      (J,x) ∈ pointCapUnionGraph μ Q m M a U ∧ x.1 = (p t).1) ↔
        (J,p t) ∈ pointCapUnionGraph μ Q m M a U
    constructor
    · rintro ⟨x,hx,he⟩
      have he' : x = p t := Subtype.ext he
      simpa only [he'] using hx
    · intro hp
      exact ⟨p t,hp,rfl⟩
  calc
    _ = (uniformRealPathKernel hN μ β T (fieldMap μ J)).real
        {p : RealSpherePath N T |
          (p t).1 ∈ ambientPointCapUnion μ Q m M a U J} :=
      (uniformRealPathKernel_eval_real_eq_evolved hN μ β T J t hA).symm
    _ = (uniformRealPathKernel hN μ β T (fieldMap μ J)).real
        {p | (J,p t) ∈ pointCapUnionGraph μ Q m M a U} := by rw [hE]
    _ ≤ _ := uniformRealPathKernel_pointCap_le_hit hN μ Q m M a β hU T J t

/-- The manuscript's time-supremum bound for the original semigroup and
the actual continuous-path union event, on every disorder realization. -/
theorem evolved_pointCap_sup_le_pathHit (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M a β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) :
    sSup {r : ℝ | ∃ t : RealPathTime T,
      r = (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real
        (ambientPointCapUnion μ Q m M a U J)} ≤
      actualWindowPathHitProbability hN μ Q m M a β U T J := by
  apply csSup_le
  · let t₀ : RealPathTime T := ⟨0,⟨le_rfl,NNReal.coe_nonneg T⟩⟩
    exact ⟨_,t₀,rfl⟩
  · rintro r ⟨t,rfl⟩
    exact evolved_pointCap_le_pathHit hN μ Q m M a β hU T J t

end
end SlowEquilibration.SourceReductionEvolvedCapMass
