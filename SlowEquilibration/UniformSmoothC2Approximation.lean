-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.UniformSmoothApproximation

@[expose] public section

namespace SlowEquilibration.UniformSmoothC2Approximation

open MeasureTheory MeasureTheory.Measure Filter Metric Set ContinuousLinearMap
open scoped ContDiff Topology Convolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option Elab.async false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [HasContDiffBump E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [IsNegInvariant μ]

omit [FiniteDimensional ℝ E] [HasContDiffBump E] [MeasurableSpace E] [BorelSpace E] in
/-- Differentiating scalar convolution uses the actual scalar pairing on
the derivative-operator codomain, also for operator-valued functions. -/
theorem scalarPair_precompR {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).precompR E =
      (lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F)) := by
  ext c A
  rfl

include μ in
/-- Genuine normalized bump convolution approximates a compact-supported
C² function uniformly in its value, Frechet derivative, and genuine second
Frechet derivative. The approximant is actually smooth with compact support. -/
theorem exists_uniform_smooth_C2_approximation (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hcf : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ x, dist (g x) (f x) ≤ ε) ∧
      (∀ x, dist (fderiv ℝ g x) (fderiv ℝ f x) ≤ ε) ∧
      ∀ x, dist (fderiv ℝ (fderiv ℝ g) x) (fderiv ℝ (fderiv ℝ f) x) ≤ ε := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hu : UniformContinuous f := hcf.uniformContinuous_of_continuous hf.continuous
  have hdu : UniformContinuous (fderiv ℝ f) :=
    (hcf.fderiv ℝ).uniformContinuous_of_continuous hfd.continuous
  have hddu : UniformContinuous (fderiv ℝ (fderiv ℝ f)) :=
    ((hcf.fderiv ℝ).fderiv ℝ).uniformContinuous_of_continuous
      (hfd.continuous_fderiv one_ne_zero)
  obtain ⟨δ, hδ, hvalue⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  obtain ⟨δd, hδd, hderiv⟩ := Metric.uniformContinuous_iff.mp hdu ε hε
  obtain ⟨δdd, hδdd, hsecond⟩ :=
    (Metric.uniformContinuous_iff (α := E) (β := E →L[ℝ] (E →L[ℝ] ℝ))).mp hddu ε hε
  let r := min δ (min δd δdd)
  have hr : 0 < r := lt_min hδ (lt_min hδd hδdd)
  let φ : ContDiffBump (0 : E) := ⟨r/2, r, by positivity, by linarith⟩
  let g : E → ℝ := φ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  have hg : ContDiff ℝ ∞ g :=
    (φ.hasCompactSupport_normed (μ := μ)).contDiff_convolution_left
      (lsmul ℝ ℝ) φ.contDiff_normed hf.continuous.locallyIntegrable
  have hcg : HasCompactSupport g :=
    (φ.hasCompactSupport_normed (μ := μ)).convolution (L := lsmul ℝ ℝ) hcf
  have hD : fderiv ℝ g = (φ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) := by
    funext x
    have hd := hcf.hasFDerivAt_convolution_right (μ := μ) (lsmul ℝ ℝ)
      (φ.continuous_normed (μ := μ)).locallyIntegrable hf₁ x
    rw [scalarPair_precompR (E := E) (F := ℝ)] at hd
    exact hd.fderiv
  have hDD : fderiv ℝ (fderiv ℝ g) =
      (φ.normed μ ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) →L[ℝ]
        (E →L[ℝ] (E →L[ℝ] ℝ))), μ] fderiv ℝ (fderiv ℝ f)) := by
    rw [hD]
    funext x
    have hdd := (hcf.fderiv ℝ).hasFDerivAt_convolution_right (μ := μ)
      (lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))
      (φ.continuous_normed (μ := μ)).locallyIntegrable hfd x
    rw [scalarPair_precompR (E := E) (F := E →L[ℝ] ℝ)] at hdd
    exact hdd.fderiv
  refine ⟨g, hg, hcg, ?_, ?_, ?_⟩
  · intro x
    apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
    intro y hy
    apply (hvalue ?_).le
    exact (show dist y x < r from hy).trans_le (min_le_left _ _)
  · intro x
    rw [hD]
    apply φ.dist_normed_convolution_le hfd.continuous.aestronglyMeasurable
    intro y hy
    apply (hderiv ?_).le
    exact (show dist y x < r from hy).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  · intro x
    rw [hDD]
    apply φ.dist_normed_convolution_le
      (hfd.continuous_fderiv one_ne_zero).aestronglyMeasurable
    intro y hy
    apply (hsecond ?_).le
    exact (show dist y x < r from hy).trans_le ((min_le_right _ _).trans (min_le_right _ _))

include μ in
/-- Actual globally smooth compact approximants converge uniformly in all
three C² quantities, with the explicit rate needed for graph-core arguments. -/
theorem exists_uniform_smooth_C2_sequence_compact (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hcf : HasCompactSupport f) :
    ∃ g : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (g n) ∧ HasCompactSupport (g n)) ∧
      (∀ n x, dist (g n x) (f x) ≤ 1/((n:ℝ)+1)) ∧
      (∀ n x, dist (fderiv ℝ (g n) x) (fderiv ℝ f x) ≤ 1/((n:ℝ)+1)) ∧
      ∀ n x, dist (fderiv ℝ (fderiv ℝ (g n)) x) (fderiv ℝ (fderiv ℝ f) x) ≤
        1/((n:ℝ)+1) := by
  have he (n : ℕ) : 0 < 1/((n:ℝ)+1) := by positivity
  choose g hg hgc hv hd hdd using
    fun n => exists_uniform_smooth_C2_approximation μ f hf hcf (he n)
  exact ⟨g, fun n => ⟨hg n, hgc n⟩, hv, hd, hdd⟩

include μ in
/-- The C² smooth approximation sequence, retaining genuine first and
second Frechet derivatives in the statement. -/
theorem exists_uniform_smooth_C2_sequence (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hcf : HasCompactSupport f) :
    ∃ g : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n x, dist (g n x) (f x) ≤ 1/((n:ℝ)+1)) ∧
      (∀ n x, dist (fderiv ℝ (g n) x) (fderiv ℝ f x) ≤ 1/((n:ℝ)+1)) ∧
      ∀ n x, dist (fderiv ℝ (fderiv ℝ (g n)) x) (fderiv ℝ (fderiv ℝ f) x) ≤
        1/((n:ℝ)+1) := by
  obtain ⟨g, hg, hv, hd, hdd⟩ := exists_uniform_smooth_C2_sequence_compact μ f hf hcf
  exact ⟨g, fun n => (hg n).1, hv, hd, hdd⟩

end SlowEquilibration.UniformSmoothC2Approximation
