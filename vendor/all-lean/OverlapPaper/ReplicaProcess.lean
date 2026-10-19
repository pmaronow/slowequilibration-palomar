module
public import OverlapPaper.FiniteIntegrability
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

@[expose] public section

/-! The actual disorder-dependent Gibbs kernel and countably many replicas. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace OverlapPaper

theorem continuous_gibbsWeight {n : ℕ} (h : ℝ) (σ : Configuration n) :
    Continuous (fun g:Disorder n=>gibbsWeight h g σ) :=
  (Real.continuous_exp.comp (continuous_totalHamiltonian h σ)).div
    (continuous_partitionFunction h) (fun g=>(partitionFunction_pos h g).ne')

def gibbsKernel (n : ℕ) (h : ℝ) : Kernel (Disorder n) (Configuration n) where
  toFun:=gibbsLaw h
  measurable':=Measure.measurable_of_measurable_coe _ (by
    intro s hs
    have he : (fun g:Disorder n=>gibbsLaw h g s)=
        fun g=>∑σ:Configuration n,s.indicator
          (fun σ=>ENNReal.ofReal (gibbsWeight h g σ)) σ := by
      funext g
      simp only [gibbsLaw,gibbsPMF,PMF.toMeasure_ofFintype_apply _ _ hs,tsum_fintype]
    rw [he]
    apply Finset.measurable_sum
    intro σ hσ
    by_cases hh : σ∈s
    · simpa [hh,Function.comp_def] using
        ENNReal.measurable_ofReal.comp (continuous_gibbsWeight h σ).measurable
    · simp [hh])

@[simp] theorem gibbsKernel_apply (n : ℕ) (h : ℝ) (g : Disorder n) :
    gibbsKernel n h g=gibbsLaw h g := rfl

instance gibbsKernel_isMarkovKernel (n : ℕ) (h : ℝ) : IsMarkovKernel (gibbsKernel n h) :=
  ⟨fun g=>by change IsProbabilityMeasure (gibbsLaw h g);infer_instance⟩

def trajectorySpace (n : ℕ) : ℕ → Type
  | 0=>Disorder n
  | _+1=>Configuration n

@[reducible] instance trajectorySpace_measurableSpace (n k : ℕ) :
    MeasurableSpace (trajectorySpace n k) := by
  cases k <;> unfold trajectorySpace <;> infer_instance

def replicaTransition (n : ℕ) (h : ℝ) (k : ℕ) :
    Kernel (Πi:Finset.Iic k,trajectorySpace n i) (trajectorySpace n (k+1)) :=
  (gibbsKernel n h).comap (fun y=>y ⟨0,by simp⟩) (measurable_pi_apply _)

instance replicaTransition_isMarkovKernel (n : ℕ) (h : ℝ) (k : ℕ) :
    IsMarkovKernel (replicaTransition n h k) := by
  constructor
  intro y
  constructor
  change gibbsLaw h (y ⟨0,by simp⟩) univ=1
  exact @IsProbabilityMeasure.measure_univ _ _ _ (gibbsLaw_isProbabilityMeasure h _)

def jointReplicaLaw (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) (n : ℕ) :
    Measure (Πk,trajectorySpace n k) := Kernel.trajMeasure (disorderLaw ξ n) (replicaTransition n h)

instance jointReplicaLaw_isProbabilityMeasure (ξ : FourPapersCommon.AdmissibleEvenMixture)
    (h : ℝ) (n : ℕ) : IsProbabilityMeasure (jointReplicaLaw ξ h n) := by
  unfold jointReplicaLaw
  exact @Kernel.instIsProbabilityMeasureForallTrajMeasure
    (trajectorySpace n) (trajectorySpace_measurableSpace n) (replicaTransition n h)
    (fun k=>replicaTransition_isMarkovKernel n h k) (disorderLaw ξ n)
    (disorderLaw_isProbabilityMeasure ξ n)

abbrev ReplicaPair := {ij:ℕ×ℕ // ij.1 < ij.2}
abbrev OverlapArray := ReplicaPair → Icc (-1:ℝ) 1

instance overlapArray_compactSpace : CompactSpace OverlapArray := inferInstance
instance overlapArray_secondCountableTopology : SecondCountableTopology OverlapArray := inferInstance

def finiteOverlapArray {n : ℕ} (σ : ℕ → Configuration n) : OverlapArray :=
  fun ij=>⟨overlap (σ ij.val.1) (σ ij.val.2),overlap_mem_unit _ _⟩

theorem measurable_finiteOverlapArray {n : ℕ} : Measurable (@finiteOverlapArray n) := by
  apply Measurable.of_eval
  intro ij
  apply Measurable.subtype_mk
  change Measurable (fun σ:ℕ → Configuration n=>overlap (σ ij.val.1) (σ ij.val.2))
  have hh : Measurable (fun p:Configuration n×Configuration n=>overlap p.1 p.2) :=
    measurable_of_countable _
  exact hh.comp (show Measurable (fun σ:ℕ → Configuration n=>(σ ij.val.1,σ ij.val.2)) from
    (measurable_pi_apply ij.val.1).prodMk (measurable_pi_apply ij.val.2))

def trajectoryOverlapArray {n : ℕ} (y : Πk,trajectorySpace n k) : OverlapArray :=
  finiteOverlapArray (fun k=>y (k+1))

theorem measurable_trajectoryOverlapArray {n : ℕ} :
    Measurable (@trajectoryOverlapArray n) :=
  measurable_finiteOverlapArray.comp (Measurable.of_eval (fun _=>measurable_pi_apply _))

def annealedOverlapLaw (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) (n : ℕ) :
    Measure OverlapArray := (jointReplicaLaw ξ h n).map trajectoryOverlapArray

instance annealedOverlapLaw_isProbabilityMeasure (ξ : FourPapersCommon.AdmissibleEvenMixture)
    (h : ℝ) (n : ℕ) : IsProbabilityMeasure (annealedOverlapLaw ξ h n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_trajectoryOverlapArray.aemeasurable).mpr
    (inferInstance : IsProbabilityMeasure (jointReplicaLaw ξ h n))

end OverlapPaper
