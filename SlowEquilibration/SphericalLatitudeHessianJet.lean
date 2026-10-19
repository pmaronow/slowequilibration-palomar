-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeIntrinsicHessian
public import SlowEquilibration.SphericalLatitudeJetCovariance

@[expose] public section

/-! The genuine latitude intrinsic Hessian in the actual ambient Gaussian
tensor jets, with its correct section-radial derivative shift. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Metric InnerProductSpace
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalForm SlowEquilibration.SphereHessian
open SphericalAging.HardSphereDynamics
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitudeField_second_derivative {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (y v z : Vector (n+1)) :
    fderiv ℝ (fderiv ℝ (latitudeField c J w e q)) y v z =
      (latitudeScale n q)^2 * fderiv ℝ (fderiv ℝ (field c J))
        (latitudeMap w e q y) (e v) (e z) := by
  let A := latitudeScale n q • e.toContinuousLinearMap
  have hfirst : fderiv ℝ (latitudeField c J w e q) =
      fun y => (fderiv ℝ (field c J) (latitudeMap w e q y)).comp A := by
    funext y
    ext v
    rw [latitudeField_directional_derivative]
    simp only [jet, iteratedFDeriv_one_apply, ContinuousLinearMap.comp_apply, A, smul_apply,
      LinearIsometry.coe_toContinuousLinearMap]
  have hD := (((field_contDiff c J).fderiv_right (m := ⊤) (by simp)).differentiable (by simp)
    (latitudeMap w e q y)).hasFDerivAt.comp y (latitudeMap_hasFDerivAt w e q y)
  have hd := hD.clm_comp (hasFDerivAt_const A y)
  change HasFDerivAt (fun z => (fderiv ℝ (field c J) (latitudeMap w e q z)).comp A) _ y at hd
  rw [hfirst, hd.fderiv]
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, A, smul_apply,
    LinearIsometry.coe_toContinuousLinearMap, map_smul, smul_eq_mul]
  ring

theorem latitudeField_gradient_derivative_inner {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (y v z : Vector (n+1)) :
    inner ℝ (fderiv ℝ (gradient (latitudeField c J w e q)) y v) z =
      fderiv ℝ (fderiv ℝ (latitudeField c J w e q)) y v z := by
  have hd := (latitudeField_contDiff c J w e q).fderiv_right (m := ⊤) (by simp)
  have h := (InnerProductSpace.toDual ℝ (Vector (n+1))).symm.hasFDerivAt.comp y
    (hd.differentiable (by simp) y).hasFDerivAt
  have he := h.fderiv
  change fderiv ℝ (gradient (latitudeField c J w e q)) y = _ at he
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]

theorem latitudeField_radialMultiplier_eq_jet {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (y : Vector (n+1)) :
    radialMultiplier (latitudeField c J w e q) y =
      jet c 1 (latitudeMap w e q y) (fun _ => latitudeRadialVector e q y) J / ((n+1 : ℕ) : ℝ) := by
  unfold radialMultiplier
  rw [real_inner_comm, inner_gradient_left, latitudeField_directional_derivative]
  rfl

/-- The intrinsic section Hessian is the scaled actual ambient tangent
Hessian minus the actual section-radial mark divided by its radius squared. -/
theorem latitude_intrinsicHessian_inner {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : OnSphere y) (v z : tangentPlane y) :
    inner ℝ (intrinsicHessian (latitudeField c J w e q) y v) z =
      (latitudeScale n q)^2 * fderiv ℝ (fderiv ℝ (field c J)) (latitudeMap w e q y)
        (e v) (e z) -
      (jet c 1 (latitudeMap w e q y) (fun _ => latitudeRadialVector e q y) J / ((n+1 : ℕ) : ℝ)) *
        inner ℝ v z := by
  change inner ℝ (intrinsicHessian (latitudeField c J w e q) y v : Vector (n+1)) (z : Vector (n+1)) = _
  rw [intrinsicHessian_apply (by omega) _ y hy
    ((latitudeField_gradient_contDiff c J w e q).differentiable (by simp) y),
    inner_sub_left, real_inner_smul_left, (tangentProjection_symmetric y).apply_clm]
  have hz : tangentProjection y (z : Vector (n+1)) = z := by
    rw [tangentProjection_eq_starProjection (by omega) y hy]
    exact (tangentPlane y).starProjection_eq_self_iff.mpr z.2
  rw [hz, latitudeField_gradient_derivative_inner, latitudeField_second_derivative,
    latitudeField_radialMultiplier_eq_jet]
  rfl

theorem latitude_intrinsicHessian_frame_entry {n P k : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : OnSphere y) (f : Fin k → tangentPlane y) (i j : Fin k) :
    inner ℝ (intrinsicHessian (latitudeField c J w e q) y (f i)) (f j) =
      (latitudeScale n q)^2 * hessianEntry c (latitudeMap w e q y)
        (fun a => e (f a)) i j J -
      (jet c 1 (latitudeMap w e q y) (fun _ => latitudeRadialVector e q y) J / ((n+1 : ℕ) : ℝ)) *
        inner ℝ (f i) (f j) := by
  rw [latitude_intrinsicHessian_inner c J w e q y hy, hessianEntry_eq_fderiv]

end
end SlowEquilibration.SphericalLatitudeChartKacRice
