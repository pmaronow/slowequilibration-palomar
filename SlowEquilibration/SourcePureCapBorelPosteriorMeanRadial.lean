-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapBorelRadialFirst

/-! The exact original posterior mean of a Borel latitude band is a
pole-independent radial integral. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelPosteriorMeanRadial
noncomputable section
open Set MeasureTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet
open SphericalPureOriginalConditionalBandFubini
open SourcePureCapBorelRadialFirst
open SourcePureLatitudeRadialDisintegration
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_posterior_borel_mean_radial
    (n p : ℕ) (hn : 2 ≤ n) (hp : 2 ≤ p)
    (β H : ℝ) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {I : Set ℝ} (hI : MeasurableSet I) :
    let μ := FiniteMixture.pure p hp 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) 1
    ENNReal.ofReal (∫ J,
      partitionOn β (field (mixtureCoefficients μ) J) (overlapRegion u I)
      ∂valueConditionedLaw c u hu (H/(n+1:ℕ))) =
      ∫⁻ s : Ioi (0:ℝ), radialMeanWeight n p β H I s ∂radialLaw n := by
  dsimp only
  let B := overlapRegion u I
  have hB : MeasurableSet B := overlapRegion_measurable u hI
  let f := B.indicator (originalPureMeanProfile n p 1 β H u)
  have hi : Integrable f (sphereLaw (n+1)) :=
    (integrable_sphere_of_continuous (by omega)
      (originalPureMeanProfile_continuous n p 1 β H u)).indicator hB
  have hnonneg : 0 ≤ᵐ[sphereLaw (n+1)] f := by
    apply Filter.Eventually.of_forall
    intro w
    by_cases hw : w ∈ B
    · simp only [f,Set.indicator_of_mem hw,originalPureMeanProfile]
      positivity
    · simp [f,Set.indicator_of_notMem hw]
  have hFubini := pure_original_conditioned_band_mean_sphere
    n p hp 1 (by positivity) (Q := 1) (by positivity) u hu β H I hI
  dsimp only at hFubini
  simp only [Real.sqrt_one,one_pow,one_mul] at hFubini
  rw [hFubini,← integral_indicator hB]
  change ENNReal.ofReal (∫ w, f w ∂sphereLaw (n+1)) = _
  rw [ofReal_integral_eq_lintegral_ofReal hi hnonneg]
  exact original_pure_mean_borel_radial n p hn β H u hu hI

end
end SlowEquilibration.SourcePureCapBorelPosteriorMeanRadial
