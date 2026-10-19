-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntropyTransfer

/-! Mutual information is unchanged by replacing redundant disorder
coordinates with the actual measurable field representation when the
initial law depends only on that representation. Infinite entropies are
allowed. This preserves the source information premise I(H;X₀). -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.InformationFactorization

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {D H X : Type*} [MeasurableSpace D] [MeasurableSpace H] [MeasurableSpace X]

theorem comap_comp_eq_comp_map (d : Measure D) (f : D → H) (hf : Measurable f)
    (μ : Kernel H X) : μ.comap f hf ∘ₘ d = μ ∘ₘ d.map f := by
  ext A hA
  rw [Measure.bind_apply hA (μ.comap f hf).aemeasurable, Measure.bind_apply hA μ.aemeasurable,
    lintegral_map (μ.measurable_coe hA) hf]
  rfl

/-- Exact causal field-information identity for a genuine probability
kernel, including singular laws and infinite mutual information. -/
theorem mutualInformation_of_measurable_factor [MeasurableSpace.CountablyGenerated X]
    (d : Measure D) [IsProbabilityMeasure d] (f : D → H) (hf : Measurable f)
    (μ : Kernel H X) [IsMarkovKernel μ] :
    endpointMutualInformation d (μ.comap f hf) = endpointMutualInformation (d.map f) μ := by
  let avg := μ ∘ₘ d.map f
  have havg : μ.comap f hf ∘ₘ d = avg := comap_comp_eq_comp_map d f hf μ
  have hleft := relativeEntropy_compProd_right_integral d (μ.comap f hf) (Kernel.const D avg)
  have hright := relativeEntropy_compProd_right_integral (d.map f) μ (Kernel.const H avg)
  simp only [Measure.compProd_const, Kernel.const_apply] at hleft hright
  unfold endpointMutualInformation
  rw [havg, hleft, hright]
  have hm : Measurable (fun h => InformationTheory.klDiv (μ h) avg) :=
    measurable_kernel_relativeEntropy μ (Kernel.const H avg)
  rw [lintegral_map hm hf]
  rfl

end SlowEquilibration.InformationFactorization
