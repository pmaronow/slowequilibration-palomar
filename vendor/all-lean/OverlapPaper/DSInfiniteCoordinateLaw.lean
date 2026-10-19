module

public import OverlapPaper.DSFiniteLimitIdentification
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section

/-! Genuine infinite conditional iid sampling and finite-cylinder
identification of the resulting overlap array law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace OverlapPaper
set_option maxHeartbeats 800000

def coordinateInfiniteSamplingKernel : Kernel DSDirectingSpace (ℕ→DSCoordinateBall) :=
  (iidSamplingKernel DSCoordinateBall).comap toCoordinateProbability measurable_toCoordinateProbability

instance coordinateInfiniteSamplingKernel_markov : IsMarkovKernel coordinateInfiniteSamplingKernel := by
  unfold coordinateInfiniteSamplingKernel
  infer_instance

def coordinateInfiniteSamplingLaw (ρ : ProbabilityMeasure DSDirectingSpace) :
    Measure (DSDirectingSpace×(ℕ→DSCoordinateBall)) :=
  (ρ : Measure DSDirectingSpace) ⊗ₘ coordinateInfiniteSamplingKernel

instance coordinateInfiniteSamplingLaw_probability (ρ : ProbabilityMeasure DSDirectingSpace) :
    IsProbabilityMeasure (coordinateInfiniteSamplingLaw ρ) := by
  unfold coordinateInfiniteSamplingLaw
  infer_instance

theorem coordinateInfiniteSamplingLaw_firstFinite (ρ : ProbabilityMeasure DSDirectingSpace) (k : ℕ) :
    (coordinateInfiniteSamplingLaw ρ).map (Prod.map id (firstFiniteSamples k))=
      coordinateFiniteSamplingLaw ρ k := by
  rw [coordinateInfiniteSamplingLaw,coordinateFiniteSamplingLaw,←Measure.compProd_map
    (measurable_firstFiniteSamples k)]
  congr 1
  apply Kernel.ext
  intro μ
  rw [Kernel.map_apply _ (measurable_firstFiniteSamples k),coordinateInfiniteSamplingKernel,Kernel.comap_apply,
    coordinateFiniteSamplingKernel_apply]
  exact infiniteIID_firstFiniteSamples k _

def coordinateOverlapArray (v : ℕ→DSCoordinateBall) : OverlapArray :=
  fun ij => ⟨inner ℝ (coordinateVector (v ij.1.1)) (coordinateVector (v ij.1.2)),
    abs_le.mp (abs_coordinateInner_le_one _ _)⟩

theorem measurable_coordinateOverlapArray : Measurable coordinateOverlapArray := by
  apply Measurable.of_eval
  intro ij
  exact (Measurable.comp (f := fun v : ℕ→DSCoordinateBall => (v ij.1.1,v ij.1.2))
    measurable_coordinateInner ((measurable_pi_apply ij.1.1).prodMk (measurable_pi_apply ij.1.2))).subtype_mk

theorem finiteOverlapPrefix_coordinateOverlapArray (k : ℕ) (v : ℕ→DSCoordinateBall) :
    finiteOverlapPrefix k (coordinateOverlapArray v)=finiteCoordinateOverlap k (firstFiniteSamples k v) := rfl

def coordinateOverlapSamplingProbability (ρ : ProbabilityMeasure DSDirectingSpace) :
    ProbabilityMeasure OverlapArray :=
  ⟨(coordinateInfiniteSamplingLaw ρ).map (fun p => coordinateOverlapArray p.2),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_coordinateOverlapArray.comp measurable_snd).aemeasurable).mpr inferInstance⟩

theorem coordinateOverlapSamplingProbability_firstFinite (ρ : ProbabilityMeasure DSDirectingSpace) (k : ℕ) :
    (coordinateOverlapSamplingProbability ρ).map (finiteOverlapPrefix k)=finiteGramSamplingProbability ρ k := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((coordinateInfiniteSamplingLaw ρ).map (fun p => coordinateOverlapArray p.2)).map
    (finiteOverlapPrefix k)=(coordinateFiniteSamplingLaw ρ k).map
      (fun p => finiteCoordinateOverlap k p.2)
  rw [Measure.map_map (f := fun p : DSDirectingSpace×(ℕ→DSCoordinateBall) => coordinateOverlapArray p.2)
    (continuous_finiteOverlapPrefix k).measurable
      (measurable_coordinateOverlapArray.comp measurable_snd)]
  change (coordinateInfiniteSamplingLaw ρ).map
    (fun p => finiteOverlapPrefix k (coordinateOverlapArray p.2))=
      (coordinateFiniteSamplingLaw ρ k).map (fun p => finiteCoordinateOverlap k p.2)
  rw [←coordinateInfiniteSamplingLaw_firstFinite ρ k,
    Measure.map_map (g := fun p : DSDirectingSpace×(Fin k→DSCoordinateBall) => finiteCoordinateOverlap k p.2)
      (f := Prod.map id (firstFiniteSamples k)) ((measurable_finiteCoordinateOverlap k).comp measurable_snd)
      (measurable_id.prodMap (measurable_firstFiniteSamples k))]
  rfl

theorem overlapMeasure_eq_of_finitePrefixes {μ ν : Measure OverlapArray}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀k,μ.map (finiteOverlapPrefix k)=ν.map (finiteOverlapPrefix k)) : μ=ν := by
  classical
  apply ext_of_generate_finite (squareCylinders fun _ : ReplicaPair =>
    {s : Set (Icc (-1:ℝ) 1) | MeasurableSet s}) generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => fun s hs t ht _ => by
      change MeasurableSet s at hs
      change MeasurableSet t at ht
      exact hs.inter ht) (by simp))
  · rintro S ⟨s,t,ht,rfl⟩
    let k := s.sup (fun ij => ij.1.2)+1
    have hb (ij : ReplicaPair) (hs : ij∈s) : ij.1.2<k :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun ij : ReplicaPair => ij.1.2) hs)
    let j : ∀ij : ReplicaPair,ij∈s→FiniteReplicaPair k := fun ij hs =>
      ⟨(⟨ij.1.1,ij.2.trans (hb ij hs)⟩,⟨ij.1.2,hb ij hs⟩),ij.2⟩
    let T : Set (FiniteOverlapArray k) := {y | ∀ij,∀hs : ij∈s,y (j ij hs)∈t ij}
    have hT : MeasurableSet T := by
      simp only [T,Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro ij
      apply MeasurableSet.iInter
      intro hs
      exact (measurable_pi_apply (j ij hs)) (ht ij (mem_univ ij))
    have he : (s : Set ReplicaPair).pi t=finiteOverlapPrefix k ⁻¹' T := by
      ext R
      simp only [Set.mem_pi,Finset.mem_coe,Set.mem_preimage,T,Set.mem_ofPred_eq]
      rfl
    rw [he,←Measure.map_apply (continuous_finiteOverlapPrefix k).measurable hT,h k,
      Measure.map_apply (continuous_finiteOverlapPrefix k).measurable hT]
  · simp

theorem coordinateOverlapSamplingProbability_eq (ν : ProbabilityMeasure GramArray)
    (hν : WeaklyExchangeableOverlapLaw (ν.map Subtype.val))
    (ρ : ProbabilityMeasure DSDirectingSpace) (φ : ℕ→ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (gramEmpiricalDirectingLaw ν∘φ) atTop (𝓝 ρ)) :
    coordinateOverlapSamplingProbability ρ=ν.map Subtype.val := by
  apply ProbabilityMeasure.toMeasure_injective
  apply overlapMeasure_eq_of_finitePrefixes
  intro k
  have hk := coordinateOverlapSamplingProbability_firstFinite ρ k
  rw [finiteGramSamplingProbability_eq ν hν ρ φ hφ hlim k] at hk
  have hm : (ν.map Subtype.val).map (finiteOverlapPrefix k)=
      ν.map (fun R => finiteOverlapPrefix k R.1) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_map (continuous_finiteOverlapPrefix k).measurable measurable_subtype_coe
  exact congrArg (fun ν : ProbabilityMeasure (FiniteOverlapArray k) => (ν : Measure (FiniteOverlapArray k)))
    (hk.trans hm.symm)

theorem exists_coordinate_directing_representation (ν : ProbabilityMeasure GramArray)
    (hν : WeaklyExchangeableOverlapLaw (ν.map Subtype.val)) :
    ∃ρ : ProbabilityMeasure DSDirectingSpace,coordinateOverlapSamplingProbability ρ=ν.map Subtype.val := by
  obtain ⟨ρ,φ,hφ,hlim⟩ := gramEmpiricalDirectingLaw_compact_subsequence ν
  exact ⟨ρ,coordinateOverlapSamplingProbability_eq ν hν ρ φ hφ hlim⟩

end OverlapPaper
