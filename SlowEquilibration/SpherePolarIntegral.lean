-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphereLinear
public import SlowEquilibration.GaussianQuadratic

/-! Real Bochner polar integration for the actual standard Gaussian, followed by
the exact radial representation of a tilted linear Gaussian integral. -/

@[expose] public section
namespace SlowEquilibration.SphereVolume
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def polarMap (p : Ioi (0 : ℝ) × Metric.sphere (0 : E) 1) : E :=
  (p.1 : ℝ) • (p.2 : E)

omit [Nontrivial E] in
theorem polarMap_measurable : Measurable (polarMap (E := E)) := by
  unfold polarMap
  fun_prop

theorem gaussian_polar_map :
    ((gaussianRadius E).prod (unitAngular E)).map polarMap = stdGaussian E := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf polarMap_measurable,
    stdGaussian_polar_lintegral f hf]
  exact lintegral_prod _ (hf.comp polarMap_measurable).aemeasurable

theorem gaussian_polar_preserving : MeasurePreserving (polarMap (E := E))
    ((gaussianRadius E).prod (unitAngular E)) (stdGaussian E) :=
  ⟨polarMap_measurable, gaussian_polar_map⟩

theorem gaussianRadius_map :
    (gaussianRadius E).map (Subtype.val : Ioi (0 : ℝ) → ℝ) =
      (stdGaussian E).map norm := by
  rw [← gaussian_polar_map, Measure.map_map (by fun_prop) polarMap_measurable]
  have he : (norm ∘ polarMap : Ioi (0 : ℝ) × Metric.sphere (0 : E) 1 → ℝ) =
      (Subtype.val : Ioi (0 : ℝ) → ℝ) ∘ Prod.fst := by
    funext p
    simp [polarMap, norm_smul, Real.norm_of_nonneg p.1.property.le]
  rw [he, ← Measure.map_map measurable_subtype_coe measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

theorem gaussian_polar_integral {f : E → ℝ} (hf : Integrable f (stdGaussian E)) :
    (∫ x, f x ∂stdGaussian E) =
      ∫ r : Ioi (0 : ℝ), ∫ u : Metric.sphere (0 : E) 1,
        f ((r : ℝ) • (u : E)) ∂unitAngular E ∂gaussianRadius E := by
  have hi : Integrable (fun p => f (polarMap p))
      ((gaussianRadius E).prod (unitAngular E)) :=
    gaussian_polar_preserving.integrable_comp_of_integrable hf
  rw [← gaussian_polar_map, integral_map polarMap_measurable.aemeasurable]
  · exact integral_prod _ hi
  · rw [gaussian_polar_map]
    exact hf.aestronglyMeasurable

theorem gaussian_polar_integrable_inner {f : E → ℝ} (hf : Integrable f (stdGaussian E)) :
    Integrable (fun r : Ioi (0 : ℝ) => ∫ u : Metric.sphere (0 : E) 1,
      f ((r : ℝ) • (u : E)) ∂unitAngular E) (gaussianRadius E) := by
  have hi : Integrable (fun p => f (polarMap p))
      ((gaussianRadius E).prod (unitAngular E)) :=
    gaussian_polar_preserving.integrable_comp_of_integrable hf
  exact hi.integral_prod_left

omit [Nontrivial E] in
private theorem radial_inner_eq (z : ℝ) (w : E) (r : Ioi (0 : ℝ)) :
    (∫ u : Metric.sphere (0 : E) 1,
      Real.exp (inner ℝ w ((r : ℝ) • (u : E)) -
        (z - 1) / 2 * ‖(r : ℝ) • (u : E)‖ ^ 2) ∂unitAngular E) =
      Real.exp (-(z - 1) / 2 * (r : ℝ) ^ 2) * SphereLinear.partition w r := by
  rw [SphereLinear.partition_eq_angular, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    have hu : ‖(u : E)‖ = 1 := by simp
    simp only [real_inner_smul_right, norm_smul, Real.norm_of_nonneg r.property.le, hu, mul_one,
      ← Real.exp_add]
    congr 1
    ring

theorem radial_tilt_integrable {z : ℝ} (hz : 0 < z) (w : E) :
    Integrable (fun r : Ioi (0 : ℝ) =>
      Real.exp (-(z - 1) / 2 * (r : ℝ) ^ 2) * SphereLinear.partition w r)
      (gaussianRadius E) := by
  have h := gaussian_polar_integrable_inner (GaussianQuadratic.integrable_exp_quadratic hz w)
  simpa only [radial_inner_eq] using h

theorem radial_tilt_integral {z : ℝ} (hz : 0 < z) (w : E) :
    (∫ r : Ioi (0 : ℝ), Real.exp (-(z - 1) / 2 * (r : ℝ) ^ 2) *
      SphereLinear.partition w r ∂gaussianRadius E) =
        z ^ (-((Module.finrank ℝ E : ℝ) / 2)) * Real.exp (‖w‖ ^ 2 / (2 * z)) := by
  rw [← GaussianQuadratic.integral_exp_quadratic hz w,
    gaussian_polar_integral (GaussianQuadratic.integrable_exp_quadratic hz w)]
  simp only [radial_inner_eq]

/-- Finite-dimensional Gaussian-shell upper bound for the actual spherical
partition function. No limiting pressure or spherical Parisi formula is used. -/
theorem shell_partition_bound {z R U : ℝ} (hz : 1 ≤ z) (hR : 0 ≤ R) (hRU : R ≤ U)
    (w : E) :
    (gaussianRadius E).real {r : Ioi (0 : ℝ) | R ≤ (r : ℝ) ∧ (r : ℝ) ≤ U} *
      (Real.exp (-(z - 1) / 2 * U ^ 2) * SphereLinear.partition w R) ≤
        z ^ (-((Module.finrank ℝ E : ℝ) / 2)) * Real.exp (‖w‖ ^ 2 / (2 * z)) := by
  let S : Set (Ioi (0 : ℝ)) := {r | R ≤ (r : ℝ) ∧ (r : ℝ) ≤ U}
  let F : Ioi (0 : ℝ) → ℝ := fun r =>
    Real.exp (-(z - 1) / 2 * (r : ℝ) ^ 2) * SphereLinear.partition w r
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_subtype_coe).inter
      (measurableSet_le measurable_subtype_coe measurable_const)
  have hFi : Integrable F (gaussianRadius E) := radial_tilt_integrable (by linarith) w
  have hF0 : ∀ r, 0 ≤ F r := fun r => mul_nonneg (Real.exp_pos _).le
    (SphereLinear.partition_pos w r).le
  have hb (r : Ioi (0 : ℝ)) (hr : r ∈ S) :
      Real.exp (-(z - 1) / 2 * U ^ 2) * SphereLinear.partition w R ≤ F r := by
    apply mul_le_mul
    · apply Real.exp_le_exp.mpr
      have hs : (r : ℝ) ^ 2 ≤ U ^ 2 :=
        (sq_le_sq₀ r.property.le (hR.trans hRU)).mpr hr.2
      nlinarith
    · exact SphereLinear.partition_mono_radius w hR hr.1
    · exact (SphereLinear.partition_pos w R).le
    · exact (Real.exp_pos _).le
  calc
    _ = ∫ _ in S, Real.exp (-(z - 1) / 2 * U ^ 2) *
        SphereLinear.partition w R ∂gaussianRadius E := by simp [S, Measure.real]
    _ ≤ ∫ r in S, F r ∂gaussianRadius E :=
      setIntegral_mono_on (integrable_const _) hFi.integrableOn hS hb
    _ ≤ ∫ r, F r ∂gaussianRadius E :=
      setIntegral_le_integral hFi (Filter.Eventually.of_forall hF0)
    _ = _ := radial_tilt_integral (by linarith) w

end
end SlowEquilibration.SphereVolume
