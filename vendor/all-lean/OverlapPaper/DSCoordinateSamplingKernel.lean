module

public import OverlapPaper.DSPairSamplingMean
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-! Genuine conditional coordinate sampling, retaining the actual Giry
probability measures and their product kernels. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace OverlapPaper

def coordinateSamplingKernel : Kernel DSDirectingSpace DSCoordinateBall where
  toFun ρ := toCoordinateProbability ρ
  measurable' := measurable_subtype_coe.comp measurable_toCoordinateProbability

instance coordinateSamplingKernel_markov : IsMarkovKernel coordinateSamplingKernel := by
  constructor
  intro ρ
  change IsProbabilityMeasure (toCoordinateProbability ρ : Measure DSCoordinateBall)
  infer_instance

def coordinatePairSamplingKernel : Kernel DSDirectingSpace (DSCoordinateBall×DSCoordinateBall) :=
  coordinateSamplingKernel ×ₖ coordinateSamplingKernel

instance coordinatePairSamplingKernel_markov : IsMarkovKernel coordinatePairSamplingKernel := by
  unfold coordinatePairSamplingKernel
  infer_instance

theorem coordinatePairSamplingKernel_apply (ρ : DSDirectingSpace) :
    coordinatePairSamplingKernel ρ=
      ((toCoordinateProbability ρ).prod (toCoordinateProbability ρ) : Measure _) :=
  Kernel.prod_apply _ _ _

def coordinatePairSamplingLaw (ρ : ProbabilityMeasure DSDirectingSpace) :
    Measure (DSDirectingSpace×(DSCoordinateBall×DSCoordinateBall)) :=
  (ρ : Measure DSDirectingSpace) ⊗ₘ coordinatePairSamplingKernel

instance coordinatePairSamplingLaw_probability (ρ : ProbabilityMeasure DSDirectingSpace) :
    IsProbabilityMeasure (coordinatePairSamplingLaw ρ) := by
  unfold coordinatePairSamplingLaw
  infer_instance

theorem integral_coordinatePairSamplingLaw (ρ : ProbabilityMeasure DSDirectingSpace)
    (f : (DSCoordinateBall×DSCoordinateBall)→ℝ) (hf : Measurable f) (C : ℝ)
    (hb : ∀p,‖f p‖≤C) :
    ∫p,f p.2 ∂coordinatePairSamplingLaw ρ=
      ∫μ,(∫p,f p ∂((toCoordinateProbability μ).prod (toCoordinateProbability μ) : Measure _))
        ∂(ρ : Measure DSDirectingSpace) := by
  have hi : Integrable (fun p : DSDirectingSpace×(DSCoordinateBall×DSCoordinateBall) => f p.2)
      (coordinatePairSamplingLaw ρ) :=
    integrable_const C |>.mono' (hf.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall (fun p => hb p.2))
  rw [coordinatePairSamplingLaw,Measure.integral_compProd hi]
  simp only [coordinatePairSamplingKernel_apply]

end OverlapPaper
