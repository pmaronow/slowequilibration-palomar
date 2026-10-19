-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeGaussianRadiusNormalization
public import SlowEquilibration.GaussianNormConcentration

/-! Concentration transfer from the original Gaussian to the original
uniform spherical law, using a bounded McShane extension and the actual
exponential radial exceptional set. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.EntranceLatitudeGaussianRadius
open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- A bounded observable on the physical sphere has an equally bounded,
globally Lipschitz Gaussian extension agreeing on the radial annulus. -/
theorem bounded_sphere_observable_gaussian_extension {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (L : ℝ≥0) {B : ℝ} (hB : 0 ≤ B)
    (hf : LipschitzOnWith L f {x | ‖x‖ = Real.sqrt (N : ℝ)})
    (hbound : ∀ x, ‖x‖ = Real.sqrt (N : ℝ) → |f x| ≤ B) :
    ∃ g : Vector N → ℝ, LipschitzWith (4 * L) g ∧
      (∀ x, |g x| ≤ B) ∧
      EqOn (f ∘ normalize N) g {x | Real.sqrt (N : ℝ) / 2 ≤ ‖x‖} := by
  obtain ⟨g, hg, he⟩ := sphere_observable_gaussian_extension hN f L hf
  refine ⟨fun x => min B (max (-B) (g x)), (hg.const_max (-B)).const_min B, ?_, ?_⟩
  · intro x
    apply abs_le.mpr
    exact ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩
  · intro x hx
    change Real.sqrt (N : ℝ) / 2 ≤ ‖x‖ at hx
    have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
    have hx0 : x ≠ 0 := by intro hh; subst x; simp only [norm_zero] at hx; linarith
    have hb := abs_le.mp (hbound (normalize N x) (normalize_norm x hx0))
    change f (normalize N x) = min B (max (-B) (g x))
    rw [← he hx]
    simp only [Function.comp_apply]
    rw [max_eq_right hb.1, min_eq_right hb.2]

/-- Agreement outside a small exceptional set controls the actual means.
The functions and the measure here are arbitrary; no concentration premise
is used. -/
theorem integral_sub_le_exceptional_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F g : Ω → ℝ)
    (hF : AEStronglyMeasurable F μ) (hg : AEStronglyMeasurable g μ)
    {B : ℝ} (_hB : 0 ≤ B)
    (hFb : ∀ᵐ x ∂μ, |F x| ≤ B) (hgb : ∀ᵐ x ∂μ, |g x| ≤ B)
    (S : Set Ω) (hS : MeasurableSet S) (he : ∀ x ∉ S, F x = g x) :
    |(∫ x, F x ∂μ) - ∫ x, g x ∂μ| ≤ (2 * B) * μ.real S := by
  have hFi : Integrable F μ := Integrable.of_bound hF B (by simpa only [Real.norm_eq_abs] using hFb)
  have hgi : Integrable g μ := Integrable.of_bound hg B (by simpa only [Real.norm_eq_abs] using hgb)
  have hi : Integrable (S.indicator (fun _ => (2 * B))) μ := (integrable_const _).indicator hS
  have hb : ∀ᵐ x ∂μ, |F x - g x| ≤ S.indicator (fun _ => (2 * B)) x := by
    filter_upwards [hFb, hgb] with x hx hy
    by_cases hs : x ∈ S
    · rw [indicator_of_mem hs]
      exact (abs_sub _ _).trans (by linarith)
    · rw [he x hs, sub_self, abs_zero, indicator_of_notMem hs]
  calc
    _ = |∫ x, F x - g x ∂μ| := by rw [integral_sub hFi hgi]
    _ ≤ ∫ x, |F x - g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, S.indicator (fun _ => (2 * B)) x ∂μ := integral_mono_ae (hFi.sub hgi).abs hi hb
    _ = _ := by rw [integral_indicator hS]; simp [mul_comm]

/-- True centered Gaussian concentration in the exact law underlying
`sphereLaw`, with no change of the coefficient measure. -/
theorem gaussian_seed_centered_upper_tail {N : ℕ} (g : Vector N → ℝ)
    (L : ℝ≥0) (hg : LipschitzWith L g) {s : ℝ} (hs : 0 ≤ s) :
    (gaussianLaw N).real {x | (∫ y, g y ∂gaussianLaw N) + s ≤ g x} ≤
      Real.exp (-s ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  have hl : LipschitzWith (L : ℝ).toNNReal g := by simpa using hg
  have ht := GaussianNormConcentration.centered_lipschitz_upper_tail g L.coe_nonneg hl hs
  rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian] at ht
  exact ht

end SlowEquilibration.EntranceLatitudeGaussianRadius
