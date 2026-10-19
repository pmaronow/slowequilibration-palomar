-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceInitialQuantitativeInput
public import SlowEquilibration.SphericalInformationReduction

/-! The conditional-entropy conclusion of manuscript `thm:main-initial`
(iii) and the mutual-information corollary `cor:cp-information`. Taking
Holder order two in the common quantitative uniform-start input gives
the positive exponent `(d - 2) / 4`. The existing physical reductions then
give separation over the whole common time interval, with conditional
KL small only in probability and with singular initial marginals allowed
in the information conclusion. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceInitialEntropyInformation

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalRotationCovariance SphericalFieldKernels
open SphericalFullFieldPathKernel SphericalAging.HardSphereDynamics
open SourceInitialQuantitativeInput
open scoped Topology NNReal ENNReal

set_option autoImplicit false

variable (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
variable
  (B : ∀ N, ℝ → Set (SphericalFieldKernels.Field N μ × Vector N))
  (S : QuantitativeUniformStart μ β T B)

include S

private theorem half_alpha_pos : 0 < alpha μ / 2 := by
  have hdegree : (4 : ℝ) ≤ (μ.minDegree : ℝ) := by
    exact_mod_cast S.degree
  unfold alpha
  linarith

/-- The `r = 2` specialization of source `eq:cp-endpoint`, with the same
band family and horizon as the full quantitative input. -/
theorem half_alpha_uniformEntryMass_rate :
    ∀ M : ℝ, 0 < M → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N in atTop,
        SphericalFieldKernels.uniformEntryMass μ β (T N) (B N M) ≤
          C * (N : ℝ)^(-(alpha μ / 2)) := by
  intro M hM
  obtain ⟨C, hC, hrate⟩ := S.rate M 2 hM (by norm_num)
  refine ⟨C, hC, ?_⟩
  have hexponent : -alpha μ * (1 - 1 / (2 : ℝ)) = -(alpha μ / 2) := by ring
  simpa only [hexponent] using hrate

/-- Manuscript `thm:main-initial` (iii): conditional KL relative to the
uniform sphere law need only be `o(log N)` in probability. -/
theorem small_conditional_KL_allTime_separation
    (κ : ∀ N, Kernel (SphericalFieldKernels.Field N μ) (Vector N))
    [∀ N, IsMarkovKernel (κ N)]
    (hKL : ReductionEntropy.LittleLogInProbability
      (fun N => SphericalFieldKernels.fieldLaw N μ)
      (fun N H => InformationTheory.klDiv (κ N H) (sphereLaw N))) :
    VaryingProbability.InProbability
      (fun N => SphericalFieldKernels.fieldLaw N μ)
      (fun N => SphericalFieldKernels.intervalDistance μ β (T N) (κ N))
      1 := by
  refine SphericalInformationReduction.entropy_allTime_separation
    μ β T κ B S.measurable (half_alpha_pos μ β T B S) ?_ S.capture hKL
  intro M hM
  obtain ⟨C, _hC, hrate⟩ := half_alpha_uniformEntryMass_rate μ β T B S M hM
  exact ⟨C, hrate⟩

/-- Manuscript `cor:cp-information`: `o(log N)` mutual information
between the full field and the initial point implies all-time separation,
even when the initial marginal is singular relative to the uniform law. -/
theorem small_field_information_allTime_separation
    (κ : ∀ N, Kernel (SphericalFieldKernels.Field N μ) (Vector N))
    [∀ N, IsMarkovKernel (κ N)]
    (hsupport : ∀ N, 2 ≤ N → ∀ H,
      ∀ᵐ x ∂κ N H, OnSphere x)
    (hI : ReductionInformation.LittleLog
      (fun N =>
        endpointMutualInformation (SphericalFieldKernels.fieldLaw N μ) (κ N))) :
    VaryingProbability.InProbability
      (fun N => SphericalFieldKernels.fieldLaw N μ)
      (fun N => SphericalFieldKernels.intervalDistance μ β (T N) (κ N))
      1 := by
  refine SphericalInformationReduction.information_allTime_separation
    μ β T κ B S.measurable hsupport ?_ (half_alpha_pos μ β T B S)
    (half_alpha_uniformEntryMass_rate μ β T B S) S.capture hI
  intro M hM N hN V J
  unfold pullbackBand
  rw [← fieldRotation_fieldMap μ V J]
  exact S.rotation M hM N hN V (fieldMap μ J)

end SlowEquilibration.SourceInitialEntropyInformation
