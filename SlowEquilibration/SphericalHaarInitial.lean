module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalOrthogonalHaar
public import SlowEquilibration.SphericalInitialRotation
public import SlowEquilibration.KernelTVMeasurable

@[expose] public section

/-! # Ordinary Haar averaging of actual evolved initial laws

The rotation-indexed initial kernel is explicitly constructed. Its Haar
mixture is the literal sphere law, and true total-variation convexity gives
the pointwise-in-disorder averaged comparison used in source red-haar.
-/
namespace SlowEquilibration.SphericalOrthogonalHaar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalReversibility SphericalRotationCovariance
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
variable {N : ℕ}

def rotatedInitialKernel (ν : Measure (Vector N)) : Kernel (OrthogonalGroup N) (Vector N) :=
  (Kernel.id ×ₖ Kernel.const (OrthogonalGroup N) ν).map
    (fun q : OrthogonalGroup N × Vector N => action q.1 q.2)

instance rotatedInitialKernel_markov (ν : Measure (Vector N)) [IsProbabilityMeasure ν] :
    IsMarkovKernel (rotatedInitialKernel ν) := by
  unfold rotatedInitialKernel
  exact Kernel.IsMarkovKernel.map _ (action_continuous N).measurable

lemma rotatedInitialKernel_apply (ν : Measure (Vector N)) [IsProbabilityMeasure ν] (g : OrthogonalGroup N) :
    rotatedInitialKernel ν g=ν.map (Unitary.linearIsometryEquiv g) := by
  rw [rotatedInitialKernel,Kernel.map_apply _ (action_continuous N).measurable,
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (action_continuous N).measurable measurable_prodMk_left]
  rfl

lemma rotatedInitialKernel_average (ν : Measure (Vector N)) [IsProbabilityMeasure ν] :
    rotatedInitialKernel ν ∘ₘ haar N=average ν := by
  rw [rotatedInitialKernel,← Measure.map_comp (haar N) _ (action_continuous N).measurable,
    ← Measure.compProd_eq_comp_prod,Measure.compProd_const]
  rfl

lemma kernel_comp_real (ρ : Measure (OrthogonalGroup N)) (κ : Kernel (OrthogonalGroup N) (Vector N))
    [IsMarkovKernel κ] {B : Set (Vector N)} (hB : MeasurableSet B) :
    (κ ∘ₘ ρ).real B=∫ g, (κ g).real B ∂ρ := by
  rw [Measure.real,Measure.bind_apply hB κ.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hB).aemeasurable
    (.of_forall fun g => measure_lt_top (κ g) B)).symm

/-- Actual event-supremum total variation is convex under a genuine
probability kernel mixture. Its measurability is the proved countable-sup
theorem, and every integral is bounded by one. -/
theorem totalVariation_kernel_average_le (ρ : Measure (OrthogonalGroup N))
    [IsProbabilityMeasure ρ] (κ : Kernel (OrthogonalGroup N) (Vector N)) [IsMarkovKernel κ]
    (π : Measure (Vector N)) [IsProbabilityMeasure π] :
    totalVariation (κ ∘ₘ ρ) π ≤ ∫ g, totalVariation (κ g) π ∂ρ := by
  have hiTV : Integrable (fun g => totalVariation (κ g) π) ρ := by
    apply Integrable.of_bound (KernelTVMeasurable.measurable_kernel_totalVariation_const κ π).aestronglyMeasurable 1
    exact .of_forall fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (totalVariation_nonneg (κ g) π)]
      exact totalVariation_le_one _ _
  apply csSup_le
  · exact ⟨0,∅,MeasurableSet.empty,by simp⟩
  · rintro r ⟨B,hB,rfl⟩
    have hiB : Integrable (fun g => (κ g).real B) ρ := by
      apply Integrable.of_bound ((κ.measurable_coe hB).ennreal_toReal).aestronglyMeasurable 1
      exact .of_forall fun g => by
        change |(κ g).real B| ≤ 1
        rw [abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one
    have he : (κ ∘ₘ ρ).real B-π.real B = ∫ g, (κ g).real B-π.real B ∂ρ := by
      rw [integral_sub hiB (integrable_const _),kernel_comp_real ρ κ hB]
      simp
    rw [he]
    calc
      _ ≤ ∫ g, |(κ g).real B-π.real B| ∂ρ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun g => (κ g).real B-π.real B)
      _ ≤ _ := integral_mono_ae (hiB.sub (integrable_const _)).abs hiTV
        (.of_forall fun g => event_difference_le_totalVariation (κ g) π hB)

/-- The actual evolved uniform initial law has no greater TV distance than
the ordinary Haar average of the evolved rotated prescribed initial laws,
for each fixed realized field. This is the true convexity step of red-haar. -/
theorem uniform_initial_totalVariation_le_haar_average (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) (ν : Measure (Vector N)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, OnSphere x) :
    totalVariation (mixedTransitionKernel μ J β t ∘ₘ sphereLaw N) (mixtureGibbsLaw μ β J) ≤
      ∫ g : OrthogonalGroup N, totalVariation
        (mixedTransitionKernel μ J β t ∘ₘ ν.map (Unitary.linearIsometryEquiv g)) (mixtureGibbsLaw μ β J) ∂haar N := by
  let := mixtureGibbsLaw_probability hN μ β J
  have he := totalVariation_kernel_average_le (haar N)
    (mixedTransitionKernel μ J β t ∘ₖ rotatedInitialKernel ν) (mixtureGibbsLaw μ β J)
  rw [← Measure.comp_assoc,rotatedInitialKernel_average,average_eq_sphereLaw hN ν hν] at he
  convert he using 1
  congr 1
  funext g
  rw [← rotatedInitialKernel_apply ν g]
  rfl

end
end SlowEquilibration.SphericalOrthogonalHaar
