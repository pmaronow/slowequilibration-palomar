module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalTransitionRotation
public import SlowEquilibration.Separation

@[expose] public section

/-! # Actual initial-law rotation and endpoint contraction

The arbitrary prescribed initial probability may be singular. Rotation
covariance and endpoint contraction are derived for the literal mixed
Langevin kernels and the actual normalized Gibbs law.
-/
namespace SlowEquilibration.SphericalRotationCovariance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalReversibility
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
variable {N : ℕ}

/-- The literal time-t law commutes with simultaneous field and initial-law
rotation, by the proved actual pointwise kernel covariance. -/
theorem mixedEvolvedLaw_rotation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (t : ℝ≥0) (ν : Measure (Vector N)) (hν : ∀ᵐ x ∂ν, OnSphere x) :
    (mixedTransitionKernel μ J β t ∘ₘ ν).map U =
      mixedTransitionKernel μ (rotatedDisorder U J) β t ∘ₘ ν.map U := by
  ext B hB
  rw [Measure.map_apply U.continuous.measurable hB,
    Measure.bind_apply (U.continuous.measurable hB) (mixedTransitionKernel μ J β t).aemeasurable,
    Measure.bind_apply hB (mixedTransitionKernel μ (rotatedDisorder U J) β t).aemeasurable,
    lintegral_map ((mixedTransitionKernel μ (rotatedDisorder U J) β t).measurable_coe hB)
      U.continuous.measurable]
  apply lintegral_congr_ae
  filter_upwards [hν] with x hx
  have he := congrArg (fun M : Measure (Vector N) => M B)
    (mixedTransitionKernel_rotation hN μ J β U t x hx)
  rw [Measure.map_apply U.continuous.measurable hB] at he
  exact he

/-- The actual total variation distance is preserved by simultaneous
rotation of the mixture field and prescribed initial probability. -/
theorem mixed_totalVariation_rotation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (t : ℝ≥0) (ν : Measure (Vector N)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, OnSphere x) :
    totalVariation (mixedTransitionKernel μ (rotatedDisorder U J) β t ∘ₘ ν.map U)
      (mixtureGibbsLaw μ β (rotatedDisorder U J)) =
    totalVariation (mixedTransitionKernel μ J β t ∘ₘ ν) (mixtureGibbsLaw μ β J) := by
  let := mixtureGibbsLaw_probability hN μ β J
  rw [← mixedEvolvedLaw_rotation hN μ J β U t ν hν,
    ← mixtureGibbsLaw_rotation hN μ J β U]
  exact totalVariation_map_measurableEquiv _ _ U.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

lemma mixed_kernel_semigroup (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) :
    ∀ s t, mixedTransitionKernel μ J β (s+t)=
      mixedTransitionKernel μ J β s ∘ₖ mixedTransitionKernel μ J β t := by
  intro s t
  apply Kernel.ext
  intro x
  simpa only [add_comm s t] using mixedTransitionKernel_semigroup μ J β t s x

/-- Actual total variation is antitone for every ordinary prescribed initial
probability, using true kernel Chapman--Kolmogorov and true Gibbs invariance. -/
theorem mixed_totalVariation_antitone (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (ν : Measure (Vector N)) [IsProbabilityMeasure ν] :
    Antitone (fun t : ℝ≥0 => totalVariation (mixedTransitionKernel μ J β t ∘ₘ ν)
      (mixtureGibbsLaw μ β J)) := by
  let := mixtureGibbsLaw_probability hN μ β J
  exact totalVariation_semigroup_antitone _ ν _ (mixed_kernel_semigroup μ J β)
    (mixedTransitionKernel_gibbs_invariant hN μ J β)

/-- The manuscript time-interval infimum is the actual endpoint distance,
including T=0, with no contraction hypothesis replacing the physical law. -/
theorem mixed_totalVariation_endpoint_infimum (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (ν : Measure (Vector N)) [IsProbabilityMeasure ν]
    {T : ℝ} (hT : 0 ≤ T) :
    sInf ((fun t : ℝ => totalVariation (mixedTransitionKernel μ J β t.toNNReal ∘ₘ ν)
      (mixtureGibbsLaw μ β J)) '' Icc 0 T) =
      totalVariation (mixedTransitionKernel μ J β T.toNNReal ∘ₘ ν) (mixtureGibbsLaw μ β J) := by
  let := mixtureGibbsLaw_probability hN μ β J
  apply endpoint_infimum _ _ hT
  intro s hs t ht hst
  exact mixed_totalVariation_antitone hN μ J β ν (Real.toNNReal_mono hst)

end
end SlowEquilibration.SphericalRotationCovariance
