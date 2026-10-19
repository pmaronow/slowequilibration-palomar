-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphereChartVolume

/-!
# Actual-radius ordinary round volume and its normalized Gaussian law

The measure is formed from genuine ordinary ambient cone volume and genuine
radius scaling. Its local density is proved equal to the actual tangent Gram
Riemannian density, and its normalization is proved equal to the manuscript law.
-/

@[expose] public section

namespace SlowEquilibration.SphereChartVolume

open MeasureTheory Set Metric Function
open scoped ENNReal NNReal Topology

noncomputable section

/-- The positive finite radius-scaling factor for actual round area. -/
def radiusAreaScale (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (n + 1 : ℕ)) ^ n)

lemma radiusAreaScale_ne_zero (n : ℕ) : radiusAreaScale n ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (pow_pos (Real.sqrt_pos.mpr (by positivity)) n)).ne'

lemma radiusAreaScale_ne_top (n : ℕ) : radiusAreaScale n ≠ ⊤ := ENNReal.ofReal_ne_top

/-- The ordinary round volume at the manuscript's actual radius, obtained by
scaling genuine unit spherical cone volume. The metric-density theorem below
identifies this independently defined measure with true round chart area. -/
def manuscriptRoundVolume (n : ℕ) : Measure (SphericalAging.FiniteModel.Vector (n + 1)) :=
  radiusAreaScale n • (sphereAreaND n).map
    (fun w => Real.sqrt (n + 1 : ℕ) • chartAmbientIsometry n w)

lemma manuscriptRoundVolume_total (n : ℕ) :
    manuscriptRoundVolume n univ = radiusAreaScale n *
      (volume : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))).toSphere univ := by
  rw [manuscriptRoundVolume, Measure.smul_apply,
    Measure.map_apply (by fun_prop : Measurable
      (fun w => Real.sqrt (n + 1 : ℕ) • chartAmbientIsometry n w)) MeasurableSet.univ,
    preimage_univ, sphereAreaND, Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    preimage_univ]
  rfl

/-- The independently defined ordinary round volume has exactly the actual
Frechet tangent-Gram density in the manuscript's true-radius chart. -/
theorem manuscriptRoundVolume_restrict_chart {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    (manuscriptRoundVolume n).restrict (manuscriptChart n '' s) =
      Measure.map (manuscriptChart n) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (Real.sqrt (manuscriptChartGram n u).det))) := by
  let f : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → SphericalAging.FiniteModel.Vector (n + 1) :=
    fun w => Real.sqrt (n + 1 : ℕ) • chartAmbientIsometry n w
  have hpos : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hf : MeasurableEmbedding f :=
    ((chartAmbientIsometry n).toHomeomorph.trans
      (Homeomorph.smulOfNeZero (Real.sqrt (n + 1 : ℕ)) hpos.ne')).measurableEmbedding
  have hset : manuscriptChart n '' s = f '' (sphereChartND '' s) := by
    rw [← image_comp]
    rfl
  rw [manuscriptRoundVolume, Measure.restrict_smul, hset, hf.restrict_map,
    preimage_image_eq _ hf.injective, sphereAreaND_restrict_chart hs hsb,
    Measure.map_map hf.measurable sphereChartND_continuous.measurable]
  change radiusAreaScale n • Measure.map (manuscriptChart n)
    ((volume.restrict s).withDensity (fun u => ENNReal.ofReal (sphereChartWeightND u))) = _
  have hchart : Measurable (manuscriptChart n) := by
    unfold manuscriptChart
    exact (measurable_const : Measurable (fun _ : EuclideanSpace ℝ (Fin n) =>
      Real.sqrt (n + 1 : ℕ))).smul ((chartAmbientIsometry n).continuous.measurable.comp
      sphereChartND_continuous.measurable)
  rw [← Measure.map_smul _ hchart.aemeasurable,
    ← withDensity_smul' (radiusAreaScale n) _ (radiusAreaScale_ne_top n)]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hs] with u hu
  rw [manuscriptChart_riemannian_density (by simpa using hsb hu),
    ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg _) _)]
  rfl

/-- The actual Gaussian direction law is normalized ordinary round volume,
with the round metric chart-density identification proved above. -/
theorem sphereLaw_eq_normalized_roundVolume (n : ℕ) :
    SphericalAging.SphereInitialLaw.sphereLaw (n + 1) =
      (manuscriptRoundVolume n univ)⁻¹ • manuscriptRoundVolume n := by
  rw [sphereLaw_eq_normalizedSphereAreaND, normalizedSphereAreaND,
    Measure.map_smul _ ((by fun_prop : Measurable
      (fun w => Real.sqrt (n + 1 : ℕ) • chartAmbientIsometry n w))).aemeasurable,
    manuscriptRoundVolume_total, manuscriptRoundVolume, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (.inl (radiusAreaScale_ne_zero n)) (.inl (radiusAreaScale_ne_top n)),
    mul_right_comm, ENNReal.inv_mul_cancel (radiusAreaScale_ne_zero n) (radiusAreaScale_ne_top n), one_mul]

end
end SlowEquilibration.SphereChartVolume
