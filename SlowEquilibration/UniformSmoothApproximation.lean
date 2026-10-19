-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib

@[expose] public section

namespace SlowEquilibration.UniformSmoothApproximation

open MeasureTheory MeasureTheory.Measure Filter Metric Set ContinuousLinearMap
open scoped ContDiff Topology Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [HasContDiffBump E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [IsNegInvariant μ]

omit [FiniteDimensional ℝ E] [HasContDiffBump E] [MeasurableSpace E] [BorelSpace E] in
/-- The scalar multiplication pairing used in differentiation of convolution
is genuinely the scalar multiplication pairing on derivative operators. -/
theorem scalarPair_precompR :
    (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompR E =
      (lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) := by
  ext c A
  rfl

include μ in
/-- An actual compact-supported C¹ function admits a globally uniform smooth
approximation of both its values and its genuine Frechet derivative. The
approximant is convolution with a normalized smooth compact bump. -/
theorem exists_uniform_smooth_C1_approximation (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧
      (∀ x, dist (g x) (f x) ≤ ε) ∧
      ∀ x, dist (fderiv ℝ g x) (fderiv ℝ f x) ≤ ε := by
  have hu : UniformContinuous f := hcf.uniformContinuous_of_continuous hf.continuous
  have hdu : UniformContinuous (fderiv ℝ f) :=
    (hcf.fderiv ℝ).uniformContinuous_of_continuous (hf.continuous_fderiv one_ne_zero)
  obtain ⟨δ, hδ, hvalue⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  obtain ⟨δd, hδd, hderiv⟩ := Metric.uniformContinuous_iff.mp hdu ε hε
  let r := min δ δd
  have hr : 0 < r := lt_min hδ hδd
  let φ : ContDiffBump (0 : E) := ⟨r/2, r, by positivity, by linarith⟩
  let g : E → ℝ := φ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  have hg : ContDiff ℝ ∞ g :=
    (φ.hasCompactSupport_normed (μ := μ)).contDiff_convolution_left
      (lsmul ℝ ℝ) φ.contDiff_normed hf.continuous.locallyIntegrable
  refine ⟨g, hg, ?_, ?_⟩
  · intro x
    apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
    intro y hy
    apply (hvalue ?_).le
    exact (show dist y x < r from hy).trans_le (min_le_left _ _)
  · intro x
    have hd := hcf.hasFDerivAt_convolution_right (μ := μ) (lsmul ℝ ℝ)
      (φ.continuous_normed (μ := μ)).locallyIntegrable hf x
    have hD : fderiv ℝ g x =
        (φ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) x := by
      rw [scalarPair_precompR] at hd
      exact hd.fderiv
    rw [hD]
    apply φ.dist_normed_convolution_le (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
    intro y hy
    apply (hderiv ?_).le
    exact (show dist y x < r from hy).trans_le (min_le_right _ _)

include μ in
/-- A true sequence of globally smooth functions converges uniformly in the
values and Frechet derivatives to any compact-supported actual C¹ function. -/
theorem exists_uniform_smooth_C1_sequence (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) :
    ∃ g : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n x, dist (g n x) (f x) ≤ 1/((n:ℝ)+1)) ∧
      ∀ n x, dist (fderiv ℝ (g n) x) (fderiv ℝ f x) ≤ 1/((n:ℝ)+1) := by
  have he (n : ℕ) : 0 < 1/((n:ℝ)+1) := by positivity
  choose g hg hv hd using fun n => exists_uniform_smooth_C1_approximation μ f hf hcf (he n)
  exact ⟨g, hg, hv, hd⟩

end SlowEquilibration.UniformSmoothApproximation
