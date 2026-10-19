-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeTransport
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-! # Exact transverse Parseval identity for the canonical latitude frame

The actual adjoint of the canonical tangent frame removes precisely the
radial coordinate. The identity holds for arbitrary ambient points, not
only points on the physical sphere.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open SphereChartVolume
open scoped Topology InnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal two-block coordinates of the actual canonical chart. -/
def latitudeChartCoordinates (n : ℕ) (u : Vector (n+1)) : Vector n × ℝ :=
  WithLp.ofLp ((chartAmbientIsometry n).symm u)

/-- The chart frame's true continuous-linear adjoint is its first block. -/
theorem latitudeChartFrame_adjoint_apply (n : ℕ) (u : Vector (n+1)) :
    (latitudeChartFrame n).toContinuousLinearMap.adjoint u=
      (latitudeChartCoordinates n u).1 := by
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ u (chartAmbientIsometry n (WithLp.toLp 2 (y,(0 : ℝ))))=_
  have h := (chartAmbientIsometry n).inner_map_map
    ((chartAmbientIsometry n).symm u) (WithLp.toLp 2 (y,(0 : ℝ)))
  rw [(chartAmbientIsometry n).apply_symm_apply] at h
  rw [h]
  simp [latitudeChartCoordinates,WithLp.prod_inner_apply]

theorem latitudeChartCoordinates_inner (n : ℕ) (u v : Vector (n+1)) :
    inner ℝ u v=
      inner ℝ (latitudeChartCoordinates n u).1 (latitudeChartCoordinates n v).1+
        (latitudeChartCoordinates n u).2*(latitudeChartCoordinates n v).2 := by
  have h := (chartAmbientIsometry n).inner_map_map
    ((chartAmbientIsometry n).symm u) ((chartAmbientIsometry n).symm v)
  rw [(chartAmbientIsometry n).apply_symm_apply,(chartAmbientIsometry n).apply_symm_apply] at h
  calc
    inner ℝ u v=inner ℝ ((chartAmbientIsometry n).symm u) ((chartAmbientIsometry n).symm v) := h
    _=_ := by
      rw [WithLp.prod_inner_apply]
      simp [latitudeChartCoordinates,mul_comm]

theorem latitudeChartCoordinates_pole_inner (n : ℕ) (u : Vector (n+1)) :
    inner ℝ u (latitudeChartPole n)=
      Real.sqrt ((n+1 : ℕ) : ℝ)*(latitudeChartCoordinates n u).2 := by
  rw [latitudeChartPole,real_inner_smul_right]
  have h := (chartAmbientIsometry n).inner_map_map
    ((chartAmbientIsometry n).symm u) (WithLp.toLp 2 (0,(1 : ℝ)))
  rw [(chartAmbientIsometry n).apply_symm_apply] at h
  rw [h]
  simp [latitudeChartCoordinates,WithLp.prod_inner_apply]

/-- Exact chart Parseval, with radial denominator equal to the actual
ambient dimension and no support restriction on the two points. -/
theorem latitudeChartFrame_adjoint_inner (n : ℕ) (u v : Vector (n+1)) :
    inner ℝ ((latitudeChartFrame n).toContinuousLinearMap.adjoint u)
      ((latitudeChartFrame n).toContinuousLinearMap.adjoint v)=
      inner ℝ u v-inner ℝ u (latitudeChartPole n)*inner ℝ v (latitudeChartPole n)/
        ((n+1 : ℕ) : ℝ) := by
  have hN : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hs : (Real.sqrt ((n+1 : ℕ) : ℝ))^2=((n+1 : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hratio :
      (Real.sqrt ((n+1 : ℕ) : ℝ)*(latitudeChartCoordinates n u).2)*
        (Real.sqrt ((n+1 : ℕ) : ℝ)*(latitudeChartCoordinates n v).2)/((n+1 : ℕ) : ℝ)=
      (latitudeChartCoordinates n u).2*(latitudeChartCoordinates n v).2 := by
    calc
      _=(Real.sqrt ((n+1 : ℕ) : ℝ))^2*
          ((latitudeChartCoordinates n u).2*(latitudeChartCoordinates n v).2)/
            ((n+1 : ℕ) : ℝ) := by ring
      _=((n+1 : ℕ) : ℝ)*
          ((latitudeChartCoordinates n u).2*(latitudeChartCoordinates n v).2)/
            ((n+1 : ℕ) : ℝ) := by rw [hs]
      _=_ := by field_simp
  rw [latitudeChartFrame_adjoint_apply,latitudeChartFrame_adjoint_apply,
    latitudeChartCoordinates_pole_inner,latitudeChartCoordinates_pole_inner,hratio]
  linarith [latitudeChartCoordinates_inner n u v]

/-- Adjoint transport through the actual pole rotation. -/
theorem latitudeFrameAt_adjoint_apply {n : ℕ} (x u : Vector (n+1)) :
    (latitudeFrameAt x).toContinuousLinearMap.adjoint u=
      (latitudeChartFrame n).toContinuousLinearMap.adjoint ((latitudePoleRotation x).symm u) := by
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ u (latitudePoleRotation x (latitudeChartFrame n y))=_
  have h := (latitudePoleRotation x).inner_map_map
    ((latitudePoleRotation x).symm u) (latitudeChartFrame n y)
  rw [(latitudePoleRotation x).apply_symm_apply] at h
  exact h

/-- The canonical frame adjoint is the first block after undoing the
literal pole rotation and chart isometry. -/
theorem latitudeFrameAt_adjoint_coordinates {n : ℕ} (x u : Vector (n+1)) :
    (latitudeFrameAt x).toContinuousLinearMap.adjoint u=
      (latitudeChartCoordinates n ((latitudePoleRotation x).symm u)).1 := by
  rw [latitudeFrameAt_adjoint_apply,latitudeChartFrame_adjoint_apply]

/-- Canonical tangent Parseval for every spherical reference and every
pair of ambient vectors, with the physical radial normalization. -/
theorem latitudeFrameAt_adjoint_inner {n : ℕ} (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (u v : Vector (n+1)) :
    inner ℝ ((latitudeFrameAt x).toContinuousLinearMap.adjoint u)
      ((latitudeFrameAt x).toContinuousLinearMap.adjoint v)=
      inner ℝ u v-inner ℝ u x*inner ℝ v x/((n+1 : ℕ) : ℝ) := by
  rw [latitudeFrameAt_adjoint_apply,latitudeFrameAt_adjoint_apply,
    latitudeChartFrame_adjoint_inner]
  have hinner := (latitudePoleRotation x).symm.inner_map_map u v
  have hu := (latitudePoleRotation x).inner_map_map
    ((latitudePoleRotation x).symm u) (latitudeChartPole n)
  have hv := (latitudePoleRotation x).inner_map_map
    ((latitudePoleRotation x).symm v) (latitudeChartPole n)
  rw [(latitudePoleRotation x).apply_symm_apply,latitudePoleRotation_apply x hx] at hu hv
  rw [hinner,← hu,← hv]

end
end SlowEquilibration.SphericalModel
