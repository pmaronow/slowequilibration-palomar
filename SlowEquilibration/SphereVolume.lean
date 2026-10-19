-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensity
public import SphericalAging.SphereInitialLaw
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FunProp

/-!
# The actual Gaussian direction law and normalized angular Haar volume

Mathlib's genuine polar-coordinate measure theorem and the proven ordinary
Gaussian density identify the manuscript's radial Gaussian law with normalized
angular cone volume in every positive dimension. No angular law identification
is assumed. The polar proof follows the method in OAI's
`Probability/Perceptron/Sphere/GaussianPolar.lean` at the requested commit.
-/

@[expose] public section

namespace SlowEquilibration.SphereVolume

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal Topology Pointwise

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The actual normalized angular volume induced by ordinary ambient Lebesgue
measure, as defined by Mathlib's polar coordinate construction. -/
def unitAngular (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Metric.sphere (0 : E) 1) :=
  ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere

/-- The angular normalization constant is positive and finite. -/
lemma angular_total_ne_zero : (volume : Measure E).toSphere univ ≠ 0 :=
  Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume)

instance unitAngular_probability : IsProbabilityMeasure (unitAngular E) where
  measure_univ := by
    rw [unitAngular, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel angular_total_ne_zero (measure_ne_top _ _)

/-- Ambient Lebesgue radial measure in the normalized angular decomposition. -/
def haarRadius (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Ioi (0 : ℝ)) :=
  (volume : Measure E).toSphere univ • Measure.volumeIoiPow (Module.finrank ℝ E - 1)

/-- Genuine polar integration, derived directly from Mathlib's measure-preserving
homeomorphism on the punctured ambient space. -/
theorem polar_lintegral (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂(volume : Measure E)) =
      ∫⁻ u : Metric.sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ),
        f ((r : ℝ) • (u : E)) ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1)
          ∂(volume : Measure E).toSphere := by
  let h := homeomorphUnitSphereProd E
  let F : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun p => f ((p.2 : ℝ) • (p.1 : E))
  have hF : Measurable F := hf.comp (measurable_snd.subtype_val.smul measurable_fst.subtype_val)
  calc
    _ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), f (x : E) ∂(volume : Measure E).comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫⁻ p, F p ∂(volume : Measure E).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      convert ((volume : Measure E).measurePreserving_homeomorphUnitSphereProd.lintegral_comp hF) using 1
      apply lintegral_congr
      intro x
      change f (x : E) = f ((h x).2.val • (h x).1.val)
      exact congrArg f (congrArg Subtype.val (h.symm_apply_apply x)).symm
    _ = _ := lintegral_prod _ hF.aemeasurable

/-- Polar integration with a genuine angular probability measure. -/
theorem polar_lintegral_normalized (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂(volume : Measure E)) =
      ∫⁻ r : Ioi (0 : ℝ), ∫⁻ u : Metric.sphere (0 : E) 1,
        f ((r : ℝ) • (u : E)) ∂unitAngular E ∂haarRadius E := by
  rw [haarRadius, lintegral_smul_measure]
  simp only [unitAngular, lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr angular_total_ne_zero), ← mul_assoc,
    ENNReal.mul_inv_cancel angular_total_ne_zero (measure_ne_top _ _), one_mul]
  rw [polar_lintegral f hf]
  exact lintegral_lintegral_swap
    (hf.comp (measurable_snd.subtype_val.smul measurable_fst.subtype_val)).aemeasurable

/-- Genuine Gaussian radial weight, from the proven ordinary Lebesgue density. -/
def radialWeight (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (GaussianDensity.normalizer E * Real.exp (-(1 / 2 : ℝ) * r ^ 2))

/-- The actual Gaussian radius distribution on the positive ray. -/
def gaussianRadius (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Ioi (0 : ℝ)) :=
  (haarRadius E).withDensity (fun r => radialWeight E r)

/-- Gaussian polar integration with independently identified genuine angular
volume and an actual radial density. -/
theorem stdGaussian_polar_lintegral (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂stdGaussian E) =
      ∫⁻ r : Ioi (0 : ℝ), ∫⁻ u : Metric.sphere (0 : E) 1,
        f ((r : ℝ) • (u : E)) ∂unitAngular E ∂gaussianRadius E := by
  rw [GaussianDensity.stdGaussian_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _
      GaussianDensity.density_continuous.measurable.ennreal_ofReal hf]
  change (∫⁻ x, radialWeight E ‖x‖ * f x) = _
  rw [polar_lintegral_normalized _ (by unfold radialWeight; fun_prop)]
  have hnorm (r : Ioi (0 : ℝ)) (u : Metric.sphere (0 : E) 1) :
      ‖(r : ℝ) • (u : E)‖ = (r : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.2]
    simp
  simp_rw [hnorm]
  rw [gaussianRadius, lintegral_withDensity_eq_lintegral_mul _ (by unfold radialWeight; fun_prop)]
  · apply lintegral_congr
    intro r
    exact lintegral_const_mul _ (hf.comp (measurable_subtype_coe.const_smul (r : ℝ)))
  · exact Measurable.lintegral_prod_right
      (hf.comp (measurable_fst.subtype_val.smul measurable_snd.subtype_val))

instance gaussianRadius_probability : IsProbabilityMeasure (gaussianRadius E) where
  measure_univ := by
    have h := stdGaussian_polar_lintegral (E := E) (fun _ => 1) measurable_const
    simpa using h.symm

/-- Radial normalization in the ordinary ambient vector space. -/
def normalize (R : ℝ) (x : E) : E := (R / ‖x‖) • x

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma normalize_smul (R : ℝ) (r : Ioi (0 : ℝ)) (u : Metric.sphere (0 : E) 1) :
    normalize R ((r : ℝ) • (u : E)) = R • (u : E) := by
  have hn : ‖(u : E)‖ = 1 := by simp
  rw [normalize, norm_smul, Real.norm_eq_abs, abs_of_pos r.2, hn, mul_one, smul_smul,
    div_mul_cancel₀ _ r.2.ne']

/-- Every genuinely normalized standard Gaussian equals normalized angular
Lebesgue/cone volume, at every specified radius and every positive dimension. -/
theorem normalizedGaussian_eq_angular (R : ℝ) :
    (stdGaussian E).map (normalize R) = (unitAngular E).map (fun u : Metric.sphere (0 : E) 1 => R • (u : E)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by unfold normalize; fun_prop),
    stdGaussian_polar_lintegral _ (by unfold normalize; fun_prop)]
  simp_rw [normalize_smul]
  rw [lintegral_map hf (by fun_prop)]
  simp

/-- Exact identification of the manuscript's actual spherical initial law with
normalized ordinary angular cone volume. This theorem has no bridge premise. -/
theorem sphereLaw_eq_normalized_angular (N : ℕ) (hN : 1 ≤ N) :
    SphericalAging.SphereInitialLaw.sphereLaw N =
      (unitAngular (SphericalAging.FiniteModel.Vector N)).map
        (fun u : Metric.sphere (0 : SphericalAging.FiniteModel.Vector N) 1 =>
          Real.sqrt (N : ℝ) • (u : SphericalAging.FiniteModel.Vector N)) := by
  let : NeZero N := ⟨by omega⟩
  exact normalizedGaussian_eq_angular (E := SphericalAging.FiniteModel.Vector N) (Real.sqrt N)

end
end SlowEquilibration.SphereVolume
