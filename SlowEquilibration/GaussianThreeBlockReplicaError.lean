-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianThreeBlockMeanComparison
public import SlowEquilibration.GaussianSpinKernels
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-! # Actual replica-event error in the three-block covariance comparison

A literal signed-kernel indicator error integrates to the probability
of the same event under two actual Gibbs replicas. Its Gaussian average
is measurable and integrable, with no replica-law premise.
-/
namespace SlowEquilibration.GaussianThreeBlockComparison
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V ι : Type*} [MeasurableSpace V] [Fintype ι]

def pairEventMass (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Fin 3) (θ : ℝ) (E : Set (V × V)) (w : EuclideanSpace ℝ ι) : ℝ :=
  ((GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w).prod
    (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w)).real E

theorem pairEventMass_measurable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ)
    (E : Set (V × V)) (hE : MeasurableSet E) : Measurable (pairEventMass ν L label θ E) := by
  let G := GaussianSpinInterpolation.gibbsKernel ν (rotatedLinear L label θ)
  let _ := GaussianSpinInterpolation.gibbsKernel_markov ν _ (rotatedLinear_measurable L hL label θ) hK
    (rotatedLinear_bound ν L hK hb label θ)
  have hm := ((G ×ₖ G).measurable_coe hE).ennreal_toReal
  convert hm using 1
  funext w
  rw [Kernel.prod_apply]
  dsimp only [G,pairEventMass]
  rw [GaussianSpinInterpolation.gibbsKernel_apply ν _ (rotatedLinear_measurable L hL label θ) hK
    (rotatedLinear_bound ν L hK hb label θ)]
  rfl

theorem pairEventMass_mem_Icc (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ)
    (E : Set (V × V)) (w : EuclideanSpace ℝ ι) : pairEventMass ν L label θ E w∈Icc 0 1 := by
  let _ := GaussianSpinInterpolation.gibbsMeasure_probability ν _ (rotatedLinear_measurable L hL label θ)
    (rotatedLinear_bound ν L hK hb label θ) w
  exact ⟨measureReal_nonneg,measureReal_le_one⟩

theorem pairEventMass_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ)
    (E : Set (V × V)) (hE : MeasurableSet E) :
    Integrable (pairEventMass ν L label θ E) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply Integrable.of_bound (pairEventMass_measurable ν L hL hK hb label θ E hE).aestronglyMeasurable 1
  exact .of_forall fun w => by
    rw [Real.norm_eq_abs,abs_of_nonneg (pairEventMass_mem_Icc ν L hL hK hb label θ E w).1]
    exact (pairEventMass_mem_Icc ν L hL hK hb label θ E w).2

variable [DecidableEq ι]

/-- The pointwise signed covariance error is the actual pair-event
probability after genuine Gibbs normalization and independent replicas. -/
theorem pairKernelExpectation_le_of_indicator (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Fin 3)
    (E : Set (V × V)) (hE : MeasurableSet E) {c a : ℝ}
    (hpair : ∀ᵐ z ∂ν.prod ν,signedKernel L label z.1 z.2 ≤ c+a*E.indicator (fun _ => (1 : ℝ)) z)
    (θ : ℝ) (w : EuclideanSpace ℝ ι) :
    pairKernelExpectation ν L label θ w ≤ c+a*pairEventMass ν L label θ E w := by
  let G := GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w
  let _ := GaussianSpinInterpolation.gibbsMeasure_probability ν _ (rotatedLinear_measurable L hL label θ)
    (rotatedLinear_bound ν L hK hb label θ) w
  have hac : G ≪ ν := GaussianSpinInterpolation.gibbsMeasure_absolutelyContinuous ν _ w
  have hi : Integrable (E.indicator (fun _ : V × V => (1 : ℝ))) (G.prod G) :=
    (integrable_const 1).indicator hE
  have hh := integral_mono_ae (signedKernel_pair_integrable ν L hL hK hb label θ w)
    ((integrable_const c).add (hi.const_mul a)) (hpair.filter_mono (hac.prod hac).ae_le)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const c) (hi.const_mul a),integral_const_mul,
    integral_indicator_const 1 hE] at hh
  simp only [integral_const,probReal_univ,smul_eq_mul,mul_one,one_mul] at hh
  exact hh

/-- The true Gaussian average of the signed pair kernel is bounded by
its comparison level and the literal Gaussian-averaged replica-event mass. -/
theorem meanPairKernel_le_of_indicator (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Fin 3)
    (E : Set (V × V)) (hE : MeasurableSet E) {c a : ℝ}
    (hpair : ∀ᵐ z ∂ν.prod ν,signedKernel L label z.1 z.2 ≤ c+a*E.indicator (fun _ => (1 : ℝ)) z)
    (θ : ℝ) :
    meanPairKernel ν L label θ ≤ c+a*(∫w,pairEventMass ν L label θ E w
      ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hi := pairEventMass_integrable ν L hL hK hb label θ E hE
  have hh := integral_mono_ae (pairKernelExpectation_gaussian_integrable ν L hL hK hb label θ)
    ((integrable_const c).add (hi.const_mul a))
    (.of_forall (pairKernelExpectation_le_of_indicator ν L hL hK hb label E hE hpair θ))
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const c) (hi.const_mul a),integral_const_mul] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  exact hh

end
end SlowEquilibration.GaussianThreeBlockComparison
