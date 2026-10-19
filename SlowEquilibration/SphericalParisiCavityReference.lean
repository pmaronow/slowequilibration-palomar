-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiGaussianBlocks
public import SlowEquilibration.SphericalParisiRadialIndependence

@[expose] public section

/-! A true spherical cavity reference-product representation. The original
surface law is reconstructed from an independent original bulk sphere,
its actual generating Gaussian radius, and an actual fresh cavity Gaussian.
Every measure is a literal pushforward of the existing Gaussian/sphere law. -/

namespace SlowEquilibration.SphericalParisiCavityReference

noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalParisiCavityCovariance SphericalParisiGaussianBlocks
open SphericalParisiRadialIndependence SphericalAging.SphereInitialLaw
open scoped InnerProductSpace

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal Gaussian radius distribution in the physical bulk dimension. -/
def radiusLaw (N : ℕ) : Measure ℝ := (gaussianLaw N).map (fun g => ‖g‖)

instance radiusLaw_probability (N : ℕ) : IsProbabilityMeasure (radiusLaw N) := by
  unfold radiusLaw
  infer_instance

theorem sphere_radius_joint_law {N : ℕ} (hN : 1 ≤ N) :
    (gaussianLaw N).map (fun g => (SphericalAging.SphereInitialLaw.normalize N g, ‖g‖)) =
      (SphericalAging.SphereInitialLaw.sphereLaw N).prod (radiusLaw N) := by
  rw [(normalize_independent_radius hN).map_prod_eq_prod_map_map
    (normalize_measurable N).aemeasurable measurable_norm.aemeasurable]
  rfl

/-- The genuine spherical bulk is independent of the actual Gaussian
radius/cavity pair, with its joint probability law identified exactly. -/
theorem sphere_radius_cavity_joint_law {N M : ℕ} (hN : 1 ≤ N) :
    ((gaussianLaw N).prod (gaussianLaw M)).map
      (fun g => (SphericalAging.SphereInitialLaw.normalize N g.1, (‖g.1‖, g.2))) =
        (SphericalAging.SphereInitialLaw.sphereLaw N).prod ((radiusLaw N).prod (gaussianLaw M)) := by
  have hm := Measure.map_prod_map (gaussianLaw N) (gaussianLaw M)
    ((normalize_measurable N).prodMk measurable_norm) measurable_id
  rw [sphere_radius_joint_law hN, Measure.map_id] at hm
  have ha := congrArg (fun μ : Measure ((Vector N × ℝ) × Vector M) =>
    μ.map (MeasurableEquiv.prodAssoc : (Vector N × ℝ) × Vector M ≃ᵐ Vector N × ℝ × Vector M)) hm
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
    (((normalize_measurable N).prodMk measurable_norm).prodMap measurable_id)] at ha
  rw [(measurePreserving_prodAssoc (SphericalAging.SphereInitialLaw.sphereLaw N) (radiusLaw N) (gaussianLaw M)).map_eq] at ha
  exact ha.symm

/-- The concrete sphere map applied to the independently sampled
physical bulk direction, actual Gaussian radius and fresh cavity Gaussian. -/
def cavityReferenceMap (N M : ℕ) (z : Vector N × ℝ × Vector M) : Vector (N+M) :=
  SphericalAging.SphereInitialLaw.normalize (N+M) (append ((z.2.1/Real.sqrt N) • z.1) z.2.2)

theorem cavityReferenceMap_measurable (N M : ℕ) : Measurable (cavityReferenceMap N M) := by
  unfold cavityReferenceMap
  exact (normalize_measurable (N+M)).comp ((append_pair_measurable N M).comp
    (show Measurable (fun z : Vector N × ℝ × Vector M =>
      ((z.2.1/Real.sqrt N) • z.1,z.2.2)) by fun_prop))

private theorem recover_gaussian_bulk {N : ℕ} (hN : 1 ≤ N) (g : Vector N) (hg : g ≠ 0) :
    (‖g‖/Real.sqrt N) • SphericalAging.SphereInitialLaw.normalize N g = g := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))).ne'
  unfold SphericalAging.SphereInitialLaw.normalize
  rw [smul_smul]
  have he : (‖g‖/Real.sqrt N)*(Real.sqrt N/‖g‖)=1 := by
    field_simp [hs, (norm_ne_zero_iff.mpr hg)]
  rw [he, one_smul]

/-- The original normalized spherical reference law has the exact
independent bulk-sphere/radius/cavity-Gaussian product representation.
This derives the true spherical product structure needed by ASS. -/
theorem actual_cavity_reference_product {N M : ℕ} (hN : 1 ≤ N) :
    SphericalAging.SphereInitialLaw.sphereLaw (N+M) =
      ((SphericalAging.SphereInitialLaw.sphereLaw N).prod ((radiusLaw N).prod (gaussianLaw M))).map (cavityReferenceMap N M) := by
  rw [← sphere_radius_cavity_joint_law hN]
  have hm : Measurable (fun g : Vector N × Vector M =>
      (SphericalAging.SphereInitialLaw.normalize N g.1,(‖g.1‖,g.2))) := by
    exact ((normalize_measurable N).comp measurable_fst).prodMk
      ((measurable_norm.comp measurable_fst).prodMk measurable_snd)
  rw [Measure.map_map (cavityReferenceMap_measurable N M) hm]
  rw [sphere_reference_gaussian_blocks N M]
  apply Measure.map_congr
  have hne : ∀ᵐ z ∂(gaussianLaw N).prod (gaussianLaw M), z.1 ≠ 0 := by
    apply ae_of_ae_map (μ := (gaussianLaw N).prod (gaussianLaw M))
      (p := fun g : Vector N => g ≠ 0) measurable_fst.aemeasurable
    change ∀ᵐ g ∂((gaussianLaw N).prod (gaussianLaw M)).fst, g ≠ 0
    rw [Measure.fst_prod]
    simpa only [measure_univ, one_smul] using gaussian_ne_zero_ae hN
  filter_upwards [hne] with z hz
  simp only [Function.comp_apply, cavityReferenceMap]
  rw [recover_gaussian_bulk hN z.1 hz]

end
end SlowEquilibration.SphericalParisiCavityReference
