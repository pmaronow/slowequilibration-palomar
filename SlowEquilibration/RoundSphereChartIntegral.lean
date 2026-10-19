-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalIntrinsicChartKacRice
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Genuine round chart integration for arbitrary nonnegative integrands

The chart is a measurable embedding on its actual domain. The change of
variables formula consequently applies to arbitrary nonnegative integrands,
including the actual intrinsic conditional Hessian mark.
-/

@[expose] public section

namespace SlowEquilibration.RoundSphereChartIntegral

open MeasureTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphereChartVolume
open SlowEquilibration.SphericalChartKacRice
open scoped ENNReal Topology

noncomputable section

theorem manuscriptChart_continuous (n : ℕ) : Continuous (manuscriptChart n) := by
  unfold manuscriptChart
  exact (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin n) =>
    Real.sqrt (n + 1 : ℕ))).smul
      ((chartAmbientIsometry n).continuous.comp sphereChartND_continuous)

theorem manuscriptChart_injOn (n : ℕ) : InjOn (manuscriptChart n) (ball 0 2) := by
  intro u hu v hv huv
  apply sphereChartND_injOn hu hv
  apply (chartAmbientIsometry n).injective
  exact (Homeomorph.smulOfNeZero (Real.sqrt (n + 1 : ℕ))
    (Real.sqrt_pos.mpr (by positivity)).ne').injective huv

/-- For a genuine measurable chart embedding, no measurability of the
nonnegative integrand is needed to transport its lower integral. -/
theorem lintegral_map_restrict_chart (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (F : Vector (n + 1) → ℝ≥0∞) :
    (∫⁻ x, F x ∂(ν.restrict (ball 0 2)).map (manuscriptChart n)) =
      ∫⁻ u in ball 0 2, F (manuscriptChart n u) ∂ν := by
  have hs : MeasurableSet (ball (0 : EuclideanSpace ℝ (Fin n)) 2) := isOpen_ball.measurableSet
  have he := (manuscriptChart_continuous n).continuousOn.measurableEmbedding hs
    (manuscriptChart_injOn n)
  have hm : (ν.restrict (ball 0 2)).map (manuscriptChart n) =
      (ν.comap ((↑) : (ball (0 : EuclideanSpace ℝ (Fin n)) 2) → EuclideanSpace ℝ (Fin n))).map
        ((ball (0 : EuclideanSpace ℝ (Fin n)) 2).domRestrict (manuscriptChart n)) := by
    rw [← map_comap_subtype_coe hs,
      Measure.map_map (manuscriptChart_continuous n).measurable measurable_subtype_coe]
    rfl
  rw [hm, he.lintegral_map]
  exact lintegral_subtype_comap hs (fun u => F (manuscriptChart n u))

/-- The independently constructed ordinary round volume has the actual
Frechet Gram density for every nonnegative integrand, with no auxiliary
measurability assumption on a varying-tangent-space expression. -/
theorem manuscriptRoundVolume_lintegral_chart (n : ℕ) (F : Vector (n + 1) → ℝ≥0∞) :
    (∫⁻ x in manuscriptChart n '' ball 0 2, F x ∂manuscriptRoundVolume n) =
      ∫⁻ u in ball 0 2, ENNReal.ofReal (Real.sqrt (manuscriptChartGram n u).det) *
        F (manuscriptChart n u) := by
  let d : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun u =>
    ENNReal.ofReal ((Real.sqrt (n + 1 : ℕ)) ^ n * sphereChartWeightND u)
  have hd : Measurable d := (measurable_const.mul sphereChartWeightND_measurable).ennreal_ofReal
  have he : (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 2)).withDensity
      (fun u => ENNReal.ofReal (Real.sqrt (manuscriptChartGram n u).det)) =
      (volume.restrict (ball 0 2)).withDensity d := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with u hu
    rw [manuscriptChart_riemannian_density (by simpa using hu)]
  rw [manuscriptRoundVolume_restrict_chart isOpen_ball.measurableSet (Subset.rfl), he,
    ← restrict_withDensity isOpen_ball.measurableSet, lintegral_map_restrict_chart,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ hd _ isOpen_ball.measurableSet
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply setLIntegral_congr_fun isOpen_ball.measurableSet
  intro u hu
  dsimp only [Pi.mul_apply, d]
  rw [manuscriptChart_riemannian_density (by simpa using hu)]

end
end SlowEquilibration.RoundSphereChartIntegral
