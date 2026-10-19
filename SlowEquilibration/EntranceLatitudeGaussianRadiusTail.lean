-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeGaussianRadiusConcentration

/-! Actual spherical concentration with an explicitly exponentially small
radial correction. Both the spherical measure and its Gaussian seed are the
literal laws used by the manuscript's diffusion. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.EntranceLatitudeGaussianRadius
open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- A bounded Gaussian extension on the radial annulus has nearly the true
spherical mean, with a derived exponential error. -/
theorem sphere_gaussian_extension_mean_close {N : ℕ} (hN : 0 < N)
    (f g : Vector N → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (hB : 0 ≤ B)
    (hFb : ∀ x, ‖x‖ = Real.sqrt (N : ℝ) → |f x| ≤ B)
    (hgb : ∀ x, |g x| ≤ B)
    (he : EqOn (f ∘ normalize N) g {x | Real.sqrt (N : ℝ) / 2 ≤ ‖x‖}) :
    |(∫ x, f x ∂sphereLaw N) - ∫ x, g x ∂gaussianLaw N| ≤
      (2 * B) * Real.exp (-(N : ℝ) / 8) := by
  let S : Set (Vector N) := {x | ‖x‖ < Real.sqrt (N : ℝ) / 2}
  have hS : MeasurableSet S := measurableSet_lt measurable_norm measurable_const
  have hF : ∀ᵐ x ∂gaussianLaw N, |f (normalize N x)| ≤ B := by
    filter_upwards [gaussian_ne_zero_ae (by omega : 1 ≤ N)] with x hx
    exact hFb _ (normalize_norm x hx)
  have hmean := integral_sub_le_exceptional_mass (gaussianLaw N) (f ∘ normalize N) g
    (hf.comp (normalize_measurable N)).aestronglyMeasurable hg.aestronglyMeasurable
    hB hF (Filter.Eventually.of_forall hgb) S hS (fun x hx => he (by
      change ¬ ‖x‖ < Real.sqrt (N : ℝ) / 2 at hx
      change Real.sqrt (N : ℝ) / 2 ≤ ‖x‖
      exact le_of_not_gt hx))
  have hp : (gaussianLaw N).real S ≤ Real.exp (-(N : ℝ) / 8) :=
    (measureReal_mono (by
      intro x hx
      change ‖x‖ < Real.sqrt (N : ℝ) / 2 at hx
      change ‖x‖ ≤ Real.sqrt (N : ℝ) / 2
      exact hx.le)).trans (spherical_seed_small_radius_probability_real N)
  rw [sphereLaw, integral_map (normalize_measurable N).aemeasurable hf.aestronglyMeasurable]
  exact hmean.trans (mul_le_mul_of_nonneg_left hp (by positivity))

/-- Every bounded Lipschitz observable on the actual physical sphere has a
Gaussian upper tail, with explicit dimension-free Lipschitz constant and an
exponentially small radial correction. The centering is its actual spherical
integral. -/
theorem sphere_observable_centered_upper_tail {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (hf : Measurable f) (L : ℝ≥0)
    (hLip : LipschitzOnWith L f {x | ‖x‖ = Real.sqrt (N : ℝ)})
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖x‖ = Real.sqrt (N : ℝ) → |f x| ≤ B)
    {s : ℝ} (hs : 0 ≤ s) :
    (sphereLaw N).real {x | (∫ y, f y ∂sphereLaw N) +
      (2 * B) * Real.exp (-(N : ℝ) / 8) + s ≤ f x} ≤
      Real.exp (-s ^ 2 / (32 * (L : ℝ) ^ 2)) + Real.exp (-(N : ℝ) / 8) := by
  obtain ⟨g, hg, hgb, he⟩ := bounded_sphere_observable_gaussian_extension hN f L hB hLip hbound
  have hm := sphere_gaussian_extension_mean_close hN f g hf hg.continuous.measurable hB hbound hgb he
  let S : Set (Vector N) := {x | ‖x‖ < Real.sqrt (N : ℝ) / 2}
  let U : Set (Vector N) := {x | (∫ y, g y ∂gaussianLaw N) + s ≤ g x}
  have hsub : (normalize N) ⁻¹' {x | (∫ y, f y ∂sphereLaw N) +
      (2 * B) * Real.exp (-(N : ℝ) / 8) + s ≤ f x} ⊆ U ∪ S := by
    intro x hx
    by_cases hsx : x ∈ S
    · exact Or.inr hsx
    · left
      have heq : f (normalize N x) = g x := he (by
        change ¬ ‖x‖ < Real.sqrt (N : ℝ) / 2 at hsx
        change Real.sqrt (N : ℝ) / 2 ≤ ‖x‖
        exact le_of_not_gt hsx)
      have hmg := (abs_le.mp hm).1
      change (∫ y, f y ∂sphereLaw N) + (2 * B) * Real.exp (-(N : ℝ) / 8) + s ≤
        f (normalize N x) at hx
      change (∫ y, g y ∂gaussianLaw N) + s ≤ g x
      rw [heq] at hx
      linarith
  have ht := gaussian_seed_centered_upper_tail g (4 * L) hg hs
  have hp : (gaussianLaw N).real S ≤ Real.exp (-(N : ℝ) / 8) :=
    (measureReal_mono (by
      intro x hx
      change ‖x‖ < Real.sqrt (N : ℝ) / 2 at hx
      change ‖x‖ ≤ Real.sqrt (N : ℝ) / 2
      exact hx.le)).trans (spherical_seed_small_radius_probability_real N)
  rw [sphereLaw, map_measureReal_apply (normalize_measurable N)
    (measurableSet_le measurable_const hf)]
  calc
    _ ≤ (gaussianLaw N).real (U ∪ S) := measureReal_mono hsub
    _ ≤ (gaussianLaw N).real U + (gaussianLaw N).real S := measureReal_union_le U S
    _ ≤ Real.exp (-s ^ 2 / (2 * ((4 * L : ℝ≥0) : ℝ) ^ 2)) + Real.exp (-(N : ℝ) / 8) :=
      add_le_add ht hp
    _ = _ := by
      have hden : 2 * ((4 * L : ℝ≥0) : ℝ) ^ 2 = 32 * (L : ℝ) ^ 2 := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        ring
      rw [hden]

end SlowEquilibration.EntranceLatitudeGaussianRadius
