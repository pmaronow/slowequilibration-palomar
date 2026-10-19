-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeGaussianRadiusTail

/-! Centered exponential moments for the literal spherical measure, derived
from Gaussian concentration and the exponentially small radial correction. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.EntranceLatitudeGaussianRadius
open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The true mean of a bounded real observable is bounded by the same bound. -/
theorem integral_abs_le_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ)
    (hF : AEStronglyMeasurable F μ) {B : ℝ}
    (hFb : ∀ᵐ x ∂μ, |F x| ≤ B) : |∫ x, F x ∂μ| ≤ B := by
  have hi : Integrable F μ := Integrable.of_bound hF B (by simpa only [Real.norm_eq_abs] using hFb)
  calc
    _ ≤ ∫ x, |F x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Ω, B ∂μ := integral_mono_ae hi.abs (integrable_const _) hFb
    _ = _ := by simp

/-- A bounded observable has a bounded centered exponential integrand. -/
theorem centered_exp_le_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ)
    (hF : AEStronglyMeasurable F μ) {B : ℝ}
    (hFb : ∀ᵐ x ∂μ, |F x| ≤ B) (t : ℝ) :
    ∀ᵐ x ∂μ, Real.exp (t * (F x - ∫ y, F y ∂μ)) ≤ Real.exp (2 * B * |t|) := by
  have hm := integral_abs_le_bound μ F hF hFb
  filter_upwards [hFb] with x hx
  apply Real.exp_le_exp.mpr
  have ha : |F x - ∫ y, F y ∂μ| ≤ 2 * B := (abs_sub _ _).trans (by linarith)
  calc
    _ ≤ |t * (F x - ∫ y, F y ∂μ)| := le_abs_self _
    _ = |t| * |F x - ∫ y, F y ∂μ| := abs_mul _ _
    _ ≤ |t| * (2 * B) := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
    _ = _ := by ring

/-- Comparing two actual centered exponential integrals when bounded
observables agree off an exceptional set. -/
theorem centered_exponential_integral_exceptional_transfer
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F g : Ω → ℝ) (hF : AEStronglyMeasurable F μ) (hg : AEStronglyMeasurable g μ)
    {B δ : ℝ} (_hB : 0 ≤ B)
    (hFb : ∀ᵐ x ∂μ, |F x| ≤ B) (hgb : ∀ᵐ x ∂μ, |g x| ≤ B)
    (S : Set Ω) (hS : MeasurableSet S) (he : ∀ x ∉ S, F x = g x)
    (hm : |(∫ x, F x ∂μ) - ∫ x, g x ∂μ| ≤ δ) (t : ℝ) :
    (∫ x, Real.exp (t * (F x - ∫ y, F y ∂μ)) ∂μ) ≤
      Real.exp (|t| * δ) * (∫ x, Real.exp (t * (g x - ∫ y, g y ∂μ)) ∂μ) +
        Real.exp (2 * B * |t|) * μ.real S := by
  let EF := fun x => Real.exp (t * (F x - ∫ y, F y ∂μ))
  let EG := fun x => Real.exp (t * (g x - ∫ y, g y ∂μ))
  have hEF := centered_exp_le_bound μ F hF hFb t
  have hEG := centered_exp_le_bound μ g hg hgb t
  have hEFi : Integrable EF μ := Integrable.of_bound
    (((hF.aemeasurable.sub_const _).const_mul t).exp.aestronglyMeasurable) _ (hEF.mono fun x hx => by
      simpa only [EF, Real.norm_of_nonneg (Real.exp_pos _).le] using hx)
  have hEGi : Integrable EG μ := Integrable.of_bound
    (((hg.aemeasurable.sub_const _).const_mul t).exp.aestronglyMeasurable) _ (hEG.mono fun x hx => by
      simpa only [EG, Real.norm_of_nonneg (Real.exp_pos _).le] using hx)
  have hEi : Integrable (S.indicator (fun _ => Real.exp (2 * B * |t|))) μ :=
    (integrable_const _).indicator hS
  have hmean : t * ((∫ y, g y ∂μ) - ∫ y, F y ∂μ) ≤ |t| * δ := by
    calc
      _ ≤ |t * ((∫ y, g y ∂μ) - ∫ y, F y ∂μ)| := le_abs_self _
      _ = |t| * |(∫ y, F y ∂μ) - ∫ y, g y ∂μ| := by rw [abs_mul, abs_sub_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (abs_nonneg _)
  have hb : ∀ᵐ x ∂μ, EF x ≤ Real.exp (|t| * δ) * EG x +
      S.indicator (fun _ => Real.exp (2 * B * |t|)) x := by
    filter_upwards [hEF] with x hx
    by_cases hs : x ∈ S
    · rw [indicator_of_mem hs]
      exact hx.trans (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    · rw [indicator_of_notMem hs, add_zero]
      have heq : EF x = EG x * Real.exp (t * ((∫ y, g y ∂μ) - ∫ y, F y ∂μ)) := by
        dsimp [EF, EG]
        rw [← Real.exp_add, he x hs]
        congr 1
        ring
      rw [heq, mul_comm (Real.exp (|t| * δ))]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmean) (Real.exp_pos _).le
  calc
    _ ≤ ∫ x, Real.exp (|t| * δ) * EG x +
        S.indicator (fun _ => Real.exp (2 * B * |t|)) x ∂μ :=
      integral_mono_ae hEFi ((hEGi.const_mul _).add hEi) hb
    _ = _ := by
      rw [integral_add (hEGi.const_mul _) hEi, integral_const_mul, integral_indicator hS]
      simp [EG, mul_comm]

/-- Centered Gaussian MGF in the precise seed law defining `sphereLaw`. -/
theorem gaussian_seed_centered_mgf_le {N : ℕ} (g : Vector N → ℝ)
    (L : ℝ≥0) (hg : LipschitzWith L g) (t : ℝ) :
    mgf (fun x => g x - ∫ y, g y ∂gaussianLaw N) (gaussianLaw N) t ≤
      Real.exp ((L : ℝ) ^ 2 * t ^ 2 / 2) := by
  have hl : LipschitzWith (L : ℝ).toNNReal g := by simpa using hg
  have ht := GaussianNormConcentration.centered_lipschitz_mgf_le g L.coe_nonneg hl t
  rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian] at ht
  exact ht

/-- A true centered exponential moment for every bounded Lipschitz physical
sphere observable, with explicit exponentially small radial correction. -/
theorem sphere_observable_centered_mgf_le {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (hf : Measurable f) (L : ℝ≥0)
    (hLip : LipschitzOnWith L f {x | ‖x‖ = Real.sqrt (N : ℝ)})
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖x‖ = Real.sqrt (N : ℝ) → |f x| ≤ B) (t : ℝ) :
    mgf (fun x => f x - ∫ y, f y ∂sphereLaw N) (sphereLaw N) t ≤
      Real.exp (|t| * ((2 * B) * Real.exp (-(N : ℝ) / 8)) + 8 * (L : ℝ) ^ 2 * t ^ 2) +
        Real.exp (2 * B * |t| - (N : ℝ) / 8) := by
  obtain ⟨g, hg, hgb, he⟩ := bounded_sphere_observable_gaussian_extension hN f L hB hLip hbound
  let F := f ∘ normalize N
  let S : Set (Vector N) := {x | ‖x‖ < Real.sqrt (N : ℝ) / 2}
  have hS : MeasurableSet S := measurableSet_lt measurable_norm measurable_const
  have hF : AEStronglyMeasurable F (gaussianLaw N) :=
    (hf.comp (normalize_measurable N)).aestronglyMeasurable
  have hFb : ∀ᵐ x ∂gaussianLaw N, |F x| ≤ B := by
    filter_upwards [gaussian_ne_zero_ae (by omega : 1 ≤ N)] with x hx
    exact hbound _ (normalize_norm x hx)
  have hmeanEq : (∫ x, f x ∂sphereLaw N) = ∫ x, F x ∂gaussianLaw N := by
    rw [sphereLaw, integral_map (normalize_measurable N).aemeasurable hf.aestronglyMeasurable]
    rfl
  have hm := sphere_gaussian_extension_mean_close hN f g hf hg.continuous.measurable hB hbound hgb he
  rw [hmeanEq] at hm
  have ht := centered_exponential_integral_exceptional_transfer (gaussianLaw N) F g
    hF hg.continuous.measurable.aestronglyMeasurable hB hFb
    (Filter.Eventually.of_forall hgb) S hS (fun x hx => he (by
      change ¬ ‖x‖ < Real.sqrt (N : ℝ) / 2 at hx
      change Real.sqrt (N : ℝ) / 2 ≤ ‖x‖
      exact le_of_not_gt hx)) hm t
  have hp : (gaussianLaw N).real S ≤ Real.exp (-(N : ℝ) / 8) :=
    (measureReal_mono (by
      intro x hx
      change ‖x‖ < Real.sqrt (N : ℝ) / 2 at hx
      change ‖x‖ ≤ Real.sqrt (N : ℝ) / 2
      exact hx.le)).trans (spherical_seed_small_radius_probability_real N)
  have hmgf := gaussian_seed_centered_mgf_le g (4 * L) hg t
  have hid : mgf (fun x => f x - ∫ y, f y ∂sphereLaw N) (sphereLaw N) t =
      ∫ x, Real.exp (t * (F x - ∫ y, F y ∂gaussianLaw N)) ∂gaussianLaw N := by
    unfold mgf
    rw [sphereLaw, integral_map (normalize_measurable N).aemeasurable (by fun_prop), ← sphereLaw, hmeanEq]
    rfl
  rw [hid]
  apply ht.trans
  calc
    _ ≤ Real.exp (|t| * ((2 * B) * Real.exp (-(N : ℝ) / 8))) *
        Real.exp ((((4 * L : ℝ≥0) : ℝ)) ^ 2 * t ^ 2 / 2) +
        Real.exp (2 * B * |t|) * Real.exp (-(N : ℝ) / 8) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      · norm_num
        ring
      · ring

end SlowEquilibration.EntranceLatitudeGaussianRadius
