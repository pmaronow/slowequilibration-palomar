-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCoarea
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

@[expose] public section

/-!
# Actual latitude coarea at every spherical center

A concrete Householder reflection sends the canonical chart pole to any
actual spherical center. True rotation invariance transports the already
proved entropy/disintegration formula, including its normalized latitude law.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter Metric
open SphereChartVolume SphereVolume
open scoped Topology ENNReal InnerProductSpace

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudePoleRotation {n : ℕ} (u : Vector (n+1)) :
    Vector (n+1) ≃ₗᵢ[ℝ] Vector (n+1) :=
  ((ℝ ∙ (latitudeChartPole n-u))ᗮ).reflection

theorem latitudePoleRotation_apply {n : ℕ} (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) :
    latitudePoleRotation u (latitudeChartPole n)=u := by
  apply Submodule.reflection_sub
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [latitudeChartPole_norm_sq,hu]

def latitudeFrameAt {n : ℕ} (u : Vector (n+1)) : Vector n →ₗᵢ[ℝ] Vector (n+1) :=
  (latitudePoleRotation u).toLinearIsometry.comp (latitudeChartFrame n)

theorem latitudeFrameAt_orthogonal {n : ℕ} (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (x : Vector n) :
    inner ℝ (latitudeFrameAt u x) u=0 := by
  nth_rw 2 [← latitudePoleRotation_apply u hu]
  change inner ℝ (latitudePoleRotation u (latitudeChartFrame n x))
    (latitudePoleRotation u (latitudeChartPole n))=0
  rw [(latitudePoleRotation u).inner_map_map,latitudeChartFrame_orthogonal]

theorem latitudeLaw_map_rotation {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (U : Vector (n+1) ≃ₗᵢ[ℝ] Vector (n+1)) :
    (latitudeLaw u e q).map U = latitudeLaw (U u) (U.toLinearIsometry.comp e) q := by
  unfold latitudeLaw
  rw [Measure.map_map U.continuous.measurable (latitudeMap_continuous u e q).measurable]
  congr 1
  funext x
  simp only [Function.comp_apply,latitudeMap,map_add,map_smul]
  rfl

/-- Exact entropy/disintegration for every spherical center, with a concrete
orthonormal frame and the actual uniform sphere probability measure. -/
theorem sphereLaw_lintegral_latitudeLaw_at {n : ℕ} (hn : 2 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (F : Vector (n+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂sphereLaw (n+1)) =
      (((volume : Measure (WithLp 2 (Vector n × ℝ))).toSphere univ)⁻¹ *
        (volume : Measure (Vector n)).toSphere univ) *
        ∫⁻ r : Ioi (0 : ℝ), {s : Ioi (0 : ℝ) | (s : ℝ)<2}.indicator
          (fun s => ENNReal.ofReal ((s : ℝ)*(Real.sqrt (1-(1-(s : ℝ)^2/2)^2))^(n-2))*
            ∫⁻ v, F v ∂latitudeLaw u (latitudeFrameAt u) (1-(s : ℝ)^2/2)) r
          ∂(volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) := by
  let U := latitudePoleRotation u
  have hmean : (∫⁻ x, F (U x) ∂sphereLaw (n+1)) = ∫⁻ x, F x ∂sphereLaw (n+1) := by
    rw [← lintegral_map hF U.continuous.measurable,sphereLaw_rotation_invariant U]
  rw [← hmean,sphereLaw_lintegral_latitudeLaw hn (fun x => F (U x)) (hF.comp U.continuous.measurable)]
  congr 1
  apply lintegral_congr
  intro r
  by_cases hr : (r : ℝ)<2
  · rw [Set.indicator_of_mem (show r ∈ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr),
      Set.indicator_of_mem (show r ∈ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr)]
    congr 1
    rw [← lintegral_map hF U.continuous.measurable,latitudeLaw_map_rotation,
      latitudePoleRotation_apply u hu]
    rfl
  · rw [Set.indicator_of_notMem (show r ∉ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr),
      Set.indicator_of_notMem (show r ∉ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr)]

end SlowEquilibration.SphericalModel
