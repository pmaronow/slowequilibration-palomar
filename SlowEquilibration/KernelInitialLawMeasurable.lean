-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.KernelTVMeasurable
public import SlowEquilibration.SphericalGibbsKernel
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! Genuine joint measurability of evolving arbitrary initial probability
measures in a parameter-dependent Markov kernel. No regularity or density
is required of the initial probability measure. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.KernelInitialLawMeasurable

open MeasureTheory ProbabilityTheory Set Filter
open KernelTVMeasurable
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

/-- The identity family of arbitrary initial probability measures. -/
def initialKernel : Kernel (Θ × ProbabilityMeasure X) X where
  toFun p := p.2.toMeasure
  measurable' := measurable_subtype_coe.comp measurable_snd

@[simp] lemma initialKernel_apply (p : Θ × ProbabilityMeasure X) :
    (initialKernel (Θ := Θ) (X := X)) p = p.2.toMeasure := rfl

instance initialKernel_isMarkov : IsMarkovKernel (initialKernel (Θ := Θ) (X := X)) where
  isProbabilityMeasure p := p.2.property

/-- Sampling the actual initial measure while retaining the parameter. -/
def initialInputKernel : Kernel (Θ × ProbabilityMeasure X) (Θ × X) :=
  Kernel.deterministic Prod.fst measurable_fst ×ₖ initialKernel

instance initialInputKernel_isMarkov : IsMarkovKernel (initialInputKernel (Θ := Θ) (X := X)) := by
  unfold initialInputKernel
  infer_instance

/-- The parameter and arbitrary initial law are both genuine kernel
inputs, so their output laws form a genuine measurable kernel. -/
def outputKernel (K : Kernel (Θ × X) X) : Kernel (Θ × ProbabilityMeasure X) X :=
  K ∘ₖ initialInputKernel

instance outputKernel_isMarkov (K : Kernel (Θ × X) X) [IsMarkovKernel K] :
    IsMarkovKernel (outputKernel K) := by
  unfold outputKernel
  infer_instance

def conditionalKernel (K : Kernel (Θ × X) X) (θ : Θ) : Kernel X X :=
  K.comap (Prod.mk θ) (measurable_const.prodMk measurable_id)

instance conditionalKernel_isMarkov (K : Kernel (Θ × X) X) [IsMarkovKernel K] (θ : Θ) :
    IsMarkovKernel (conditionalKernel K θ) := by
  unfold conditionalKernel
  infer_instance

/-- Ordinary evolution of an arbitrary initial probability measure. -/
def initialLawOutput (K : Kernel (Θ × X) X) (θ : Θ) (ν : ProbabilityMeasure X) : Measure X :=
  conditionalKernel K θ ∘ₘ ν.toMeasure

@[simp] theorem outputKernel_apply (K : Kernel (Θ × X) X) [IsMarkovKernel K]
    (p : Θ × ProbabilityMeasure X) : outputKernel K p = initialLawOutput K p.1 p.2 := by
  ext A hA
  rw [outputKernel, Kernel.comp_apply' _ _ _ hA, initialInputKernel, Kernel.prod_apply,
    Kernel.deterministic_apply, initialKernel_apply, Measure.dirac_prod]
  have hmk : Measurable (Prod.mk p.1 : X → Θ × X) := measurable_const.prodMk measurable_id
  rw [lintegral_map (K.measurable_coe hA) hmk]
  change (∫⁻ x, K (p.1,x) A ∂p.2.toMeasure) =
    (conditionalKernel K p.1 ∘ₘ p.2.toMeasure) A
  rw [Measure.bind_apply hA (conditionalKernel K p.1).aemeasurable]
  rfl

theorem initialLawOutput_measurable (K : Kernel (Θ × X) X) [IsMarkovKernel K] :
    Measurable (fun p : Θ × ProbabilityMeasure X => initialLawOutput K p.1 p.2) := by
  have he : (fun p : Θ × ProbabilityMeasure X => initialLawOutput K p.1 p.2) = outputKernel K := by
    funext p
    exact (outputKernel_apply K p).symm
  rw [he]
  exact (outputKernel K).measurable

variable [MeasurableSpace.CountablyGenerated X]

/-- The actual TV distance is jointly measurable in parameter and initial
probability measure, including singular initial laws. -/
theorem initialLawOutput_totalVariation_measurable (K : Kernel (Θ × X) X)
    [IsMarkovKernel K] (π : Kernel Θ X) [IsMarkovKernel π] :
    Measurable (fun p : Θ × ProbabilityMeasure X => totalVariation (initialLawOutput K p.1 p.2) (π p.1)) := by
  apply measurable_totalVariation _ _ (initialLawOutput_measurable K) (π.measurable.comp measurable_fst)
  · intro p
    change IsProbabilityMeasure (conditionalKernel K p.1 ∘ₘ p.2.toMeasure)
    infer_instance
  · intro p
    change IsProbabilityMeasure (π p.1)
    infer_instance

theorem initialLawOutput_totalVariation_le_measurableSet (K : Kernel (Θ × X) X)
    [IsMarkovKernel K] (π : Kernel Θ X) [IsMarkovKernel π] (r : ℝ) :
    MeasurableSet {p : Θ × ProbabilityMeasure X | totalVariation (initialLawOutput K p.1 p.2) (π p.1) ≤ r} :=
  measurableSet_le (initialLawOutput_totalVariation_measurable K π) measurable_const

/-- The field failure probability is measurable in the prescribed
initial probability measure. This is the parameter needed for Haar/Fubini
averaging and random menus independent of the field. -/
theorem initialLaw_failure_mass_measurable (d : Measure Θ) [SFinite d]
    (K : Kernel (Θ × X) X) [IsMarkovKernel K] (π : Kernel Θ X) [IsMarkovKernel π] (r : ℝ) :
    Measurable (fun ν : ProbabilityMeasure X =>
      d {θ | totalVariation (initialLawOutput K θ ν) (π θ) ≤ r}) := by
  exact measurable_measure_prodMk_right (initialLawOutput_totalVariation_le_measurableSet K π r)

theorem initialLaw_failure_realMass_measurable (d : Measure Θ) [SFinite d]
    (K : Kernel (Θ × X) X) [IsMarkovKernel K] (π : Kernel Θ X) [IsMarkovKernel π] (r : ℝ) :
    Measurable (fun ν : ProbabilityMeasure X =>
      d.real {θ | totalVariation (initialLawOutput K θ ν) (π θ) ≤ r}) :=
  (initialLaw_failure_mass_measurable d K π r).ennreal_toReal

end SlowEquilibration.KernelInitialLawMeasurable
