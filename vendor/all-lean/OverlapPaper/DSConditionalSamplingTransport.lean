module

public import OverlapPaper.RandomSampling
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section

/-! Functoriality of genuine conditional iid sampling under measurable
maps. This transports an actual directing measure, not a representation premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace OverlapPaper
set_option maxHeartbeats 500000

section
variable {X Y E F : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace E] [MeasurableSpace F]

theorem compProd_transport (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : Kernel X E) [IsMarkovKernel κ] (η : Kernel Y F) [IsMarkovKernel η]
    (f : X→Y) (hf : Measurable f) (g : E→F) (hg : Measurable g)
    (hk : ∀x,(κ x).map g=η (f x)) :
    (ν⊗ₘκ).map (Prod.map f g)=(ν.map f)⊗ₘη := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (hf.prodMap hg) (hs.prod ht)]
  have he : (Prod.map f g) ⁻¹' (s×ˢt)=(f⁻¹'s)×ˢ(g⁻¹'t) := rfl
  rw [he,Measure.compProd_apply_prod (hs.preimage hf) (ht.preimage hg),
    Measure.compProd_apply_prod hs ht,
    setLIntegral_map hs (η.measurable_coe ht) hf]
  apply lintegral_congr
  intro x
  rw [←hk x,Measure.map_apply hg ht]

end

section
variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

def probabilityPushMap (f : E→F) (μ : ProbabilityMeasure E) : ProbabilityMeasure F := μ.map f

theorem measurable_probabilityPushMap (f : E→F) (hf : Measurable f) :
    Measurable (probabilityPushMap f) := by
  apply Measurable.subtype_mk
  exact (Measure.measurable_map f hf).comp measurable_subtype_coe

theorem iidSamplingLaw_map (μ : ProbabilityMeasure E) (f : E→F) (hf : Measurable f) :
    (Measure.infinitePi (fun _ : ℕ => (μ : Measure E))).map (fun v i => f (v i))=
      Measure.infinitePi (fun _ : ℕ => (probabilityPushMap f μ : Measure F)) := by
  exact Measure.infinitePi_map_pi (fun _ : ℕ => (μ : Measure E)) (fun _ => hf)

theorem randomSamplingLaw_map (ν : Measure (ProbabilityMeasure E)) [IsProbabilityMeasure ν]
    (f : E→F) (hf : Measurable f) :
    (randomSamplingLaw ν).map (Prod.map (probabilityPushMap f) (fun v i => f (v i)))=
      randomSamplingLaw (ν.map (probabilityPushMap f)) := by
  apply compProd_transport ν (iidSamplingKernel E) (iidSamplingKernel F)
    (probabilityPushMap f) (measurable_probabilityPushMap f hf) _
    (Measurable.of_eval (fun i => hf.comp (measurable_pi_apply i)))
  intro μ
  exact iidSamplingLaw_map μ f hf

end
end OverlapPaper
