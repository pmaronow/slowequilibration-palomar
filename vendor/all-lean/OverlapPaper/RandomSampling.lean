module

public import OverlapPaper.NormObservable
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

/-! Genuine conditional independent sampling from a random probability measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace OverlapPaper

section
variable {E : Type*} [MeasurableSpace E]

theorem measurable_iidSamplingLaw :
    Measurable (fun μ:ProbabilityMeasure E=>Measure.infinitePi (fun _ : ℕ=>(μ:Measure E))) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _=>fun s hs t ht _=>hs.inter ht) (by simp))
  rintro U ⟨s,t,ht,rfl⟩
  have hm : ∀i,MeasurableSet (t i):=fun i=>ht i (mem_univ i)
  simp only [Measure.infinitePi_pi _ (fun i _=>hm i)]
  have hm' (i : ℕ) : Measurable (fun μ:ProbabilityMeasure E=>(μ:Measure E) (t i)) :=
    (Measure.measurable_coe (hm i)).comp measurable_subtype_coe
  exact s.measurable_prod (fun i _=>hm' i)

def iidSamplingKernel (E : Type*) [MeasurableSpace E] : Kernel (ProbabilityMeasure E) (ℕ→E) where
  toFun μ:=Measure.infinitePi (fun _ : ℕ=>(μ:Measure E))
  measurable':=measurable_iidSamplingLaw

instance iidSamplingKernel_isMarkovKernel : IsMarkovKernel (iidSamplingKernel E) := by
  constructor
  intro μ
  change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ=>(μ:Measure E)))
  infer_instance

def randomSamplingLaw (ν : Measure (ProbabilityMeasure E)) :
    Measure (ProbabilityMeasure E×(ℕ→E)) := ν⊗ₘiidSamplingKernel E

instance randomSamplingLaw_isProbabilityMeasure (ν : Measure (ProbabilityMeasure E))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (randomSamplingLaw ν) := by
  unfold randomSamplingLaw
  infer_instance

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (ν : Measure (ProbabilityMeasure E)) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in theorem randomSampling_normObservable_eq
    (hball : ∀ᵐ(μ:ProbabilityMeasure E) ∂ν,∀ᵐx ∂(μ:Measure E),‖x‖≤1) :
    ∀ᵐp ∂randomSamplingLaw ν,∀i,
      normObservable (fun i j=>inner ℝ (p.2 i) (p.2 j)) i=‖p.2 i‖^2 := by
  apply Measure.ae_compProd_of_ae_ae
  · simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_eq_fun
    · have hm : Measurable (fun x:ProbabilityMeasure E×(ℕ→E)=>
          fun j k=>inner ℝ (x.2 j) (x.2 k)) := by
        apply Measurable.of_eval
        intro j
        apply Measurable.of_eval
        intro k
        fun_prop
      exact (measurable_normObservable i).comp hm
    · fun_prop
  · filter_upwards [hball] with μ hμ
    exact iid_normObservable_eq (μ:Measure E) hμ

omit [IsProbabilityMeasure ν] in theorem randomSampling_normObservable_and_balls
    (hball : ∀ᵐ(μ:ProbabilityMeasure E) ∂ν,∀ᵐx ∂(μ:Measure E),‖x‖≤1) :
    ∀ᵐp ∂randomSamplingLaw ν,
      (∀i,normObservable (fun i j=>inner ℝ (p.2 i) (p.2 j)) i=‖p.2 i‖^2)∧
      (∀i j ε,0<ε→(p.2 j∈Metric.ball (p.2 i) ε ↔
        normObservable (fun i j=>inner ℝ (p.2 i) (p.2 j)) i+
        normObservable (fun i j=>inner ℝ (p.2 i) (p.2 j)) j-
        2*inner ℝ (p.2 i) (p.2 j)<ε^2)) := by
  filter_upwards [randomSampling_normObservable_eq ν hball] with p hp
  refine ⟨hp,?_⟩
  intro i j ε hε
  rw [hp i,hp j,Metric.mem_ball,dist_comm,dist_eq_norm]
  have he:=norm_sub_sq_real (p.2 i) (p.2 j)
  constructor <;> intro h <;> nlinarith [norm_nonneg (p.2 i-p.2 j)]

end
end OverlapPaper
