-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeJointRegression
public import SlowEquilibration.SphericalLatitudeHessianJet

@[expose] public section

/-! The complete actual intrinsic latitude Hessian has a scaled shifted
GOE law under its genuine whole-tensor value/radial/gradient posterior, at
every specified target. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicHessianLaw
open SlowEquilibration.ConditionedIntrinsicHessian
open SlowEquilibration.SphereHessian
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitude_ambientHessian_joint_lift_zero {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    (q : ℝ) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    (ambientHessianCLM c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy)).comp
      (latitudeJointCLM c w e q y hy).adjoint=0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Sum (Fin 2) (Fin n)) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro ij
  rcases ij with ⟨i,l⟩
  let f := (EuclideanSpace.proj (i,l)).comp
    (ambientHessianCLM c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy))
  have h := actual_scalar_cross_covariance f (latitudeJointCLM c w e q y hy)
    (EuclideanSpace.basisFun (Sum (Fin 2) (Fin n)) ℝ j)
  simp only [EuclideanSpace.basisFun_inner] at h
  change cov[fun J : Disorder (n+2) P => ambientHessianCLM c (latitudeMap w e q y)
      (latitudeEmbeddedFrame e y hy) (euclideanDisorder J) (i,l),
    fun J : Disorder (n+2) P => latitudeJointCLM c w e q y hy (euclideanDisorder J) j;
      disorderLaw (n+2) P] =
    ambientHessianCLM c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy)
      ((latitudeJointCLM c w e q y hy).adjoint
        (EuclideanSpace.basisFun (Sum (Fin 2) (Fin n)) ℝ j)) (i,l) at h
  change ambientHessianCLM c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy)
      ((latitudeJointCLM c w e q y hy).adjoint
        (EuclideanSpace.basisFun (Sum (Fin 2) (Fin n)) ℝ j)) (i,l)=0
  rw [← h]
  simp only [ambientHessianCLM_apply, unpack_euclideanDisorder]
  cases j with
  | inl j =>
    fin_cases j
    · simpa [latitudeScoreCLM] using hessian_value_covariance_zero c hc (latitudeMap w e q y)
        (latitudeEmbeddedFrame e y hy) (latitudeEmbeddedFrame_tangent w e he q y hy) i l
    · simpa [latitudeScoreCLM] using hessian_gradient_covariance_zero c hc (latitudeMap w e q y)
        (latitudeEmbeddedFrame e y hy) (latitudeEmbeddedFrame_tangent w e he q y hy) i l
        (latitudeRadialVector e q y)
  | inr j =>
    simpa only [latitudeJointCLM_apply_inr, gradientCLM_apply, unpack_euclideanDisorder] using
      hessian_gradient_covariance_zero c hc (latitudeMap w e q y)
        (latitudeEmbeddedFrame e y hy) (latitudeEmbeddedFrame_tangent w e he q y hy) i l
        (latitudeGradientDirections e q y hy j)

theorem latitude_conditioned_ambient_map {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    (q : ℝ) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (a : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))) :
    (coefficientKernel (latitudeJointCLM c w e q y hy) a).map
      (hessianMatrix c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy)) =
    (disorderLaw (n+2) P).map (hessianMatrix c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy)) := by
  have hm : Measurable (actualObservation
      (ambientHessianCLM c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy))) :=
    (ambientHessianCLM c _ _).continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate (n+2) P => ℝ)).symm.continuous.measurable.comp (flatDisorder_measurable _ _))
  have h := congrArg (fun m => m.map (hessianDecode n))
    (coefficientKernel_target_map_linear _ _ (latitude_ambientHessian_joint_lift_zero c hc w e he q y hy) a)
  rw [Measure.map_map (hessianDecode_measurable n) hm,
    Measure.map_map (hessianDecode_measurable n) hm] at h
  simpa only [Function.comp_def, hessianDecode_actual] using h

theorem latitude_conditioned_ambient_hasLaw {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (a : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))) :
    HasLaw (hessianMatrix c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy))
      (goeLaw n (n+2) (secondCovariance c 1))
      (coefficientKernel (latitudeJointCLM c w e q y hy) a) := by
  have hm : Measurable (actualObservation
      (ambientHessianCLM c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy))) :=
    (ambientHessianCLM c _ _).continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate (n+2) P => ℝ)).symm.continuous.measurable.comp (flatDisorder_measurable _ _))
  have hH : Measurable (hessianMatrix c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy)) := by
    convert (hessianDecode_measurable n).comp hm using 1
    funext J
    exact (hessianDecode_actual c _ _ J).symm
  refine ⟨hH.aemeasurable, ?_⟩
  rw [latitude_conditioned_ambient_map c hc w e he q y hy a]
  exact (tangent_hessian_matrix_hasLaw (by omega) c hc _ (r := 1)
    (by simpa only [mul_one] using latitudeMap_norm_sq (by omega) w hw e he hq y hy)
    (latitudeEmbeddedFrame e y hy) (latitudeEmbeddedFrame_orthonormal e y hy)
    (latitudeEmbeddedFrame_tangent w e he q y hy)).map_eq

def latitudeIntrinsicMatrix {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (J : Disorder (n+2) P) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (tangentBasis y hy).toBasis (tangentBasis y hy).toBasis
    (intrinsicHessian (latitudeField c J w e q) y).toLinearMap

theorem latitudeIntrinsicMatrix_eq {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+2) P)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    latitudeIntrinsicMatrix c w e q y hy J =
      (latitudeScale n q)^2 • hessianMatrix c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy) J -
      (jet c 1 (latitudeMap w e q y) (fun _ => latitudeRadialVector e q y) J / ((n+1 : ℕ) : ℝ)) •
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  have hsphere : SphericalAging.HardSphereDynamics.OnSphere y := by
    change inner ℝ y y = _
    rw [real_inner_self_eq_norm_sq]
    exact hy
  ext i j
  rw [latitudeIntrinsicMatrix, LinearMap.toMatrix_apply]
  change (tangentBasis y hy).repr
    (intrinsicHessian (latitudeField c J w e q) y (tangentBasis y hy j)) i = _
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm,
    latitude_intrinsicHessian_frame_entry c J w e q y hsphere (tangentBasis y hy) j i,
    orthonormal_iff_ite.mp (tangentBasis y hy).orthonormal]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hessianMatrix]
  rw [hessianEntry_symm c (latitudeMap w e q y) (fun a => e (tangentBasis y hy a)) j i]
  simp only [eq_comm]
  rfl

/-- The literal complete intrinsic Hessian of the actual affine latitude
field has the scaled shifted GOE law under every prescribed actual joint
value/section-radial/tangent-gradient target. -/
theorem center_latitude_conditioned_intrinsic_hasLaw {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (a : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    HasLaw (latitudeIntrinsicMatrix c w e q y hy)
      ((goeLaw n (n+2) (Q^2*μ.xi2 Q)).map
        (fun W => (latitudeScale n q)^2 • W-(a (Sum.inl 1)/((n+1 : ℕ) : ℝ)) •
          (1 : Matrix (Fin n) (Fin n) ℝ)))
      (coefficientKernel (latitudeJointCLM c w e q y hy) a) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hH := latitude_conditioned_ambient_hasLaw c hc w hw e he hq1.le y hy a
  rw [show secondCovariance c 1=Q^2*μ.xi2 Q by
    rw [secondCovariance_center, secondCovariance_mixture]] at hH
  have hm : Measurable (fun W : Matrix (Fin n) (Fin n) ℝ =>
      (latitudeScale n q)^2 • W-(a (Sum.inl 1)/((n+1 : ℕ) : ℝ)) • 1) := by fun_prop
  have hshift := (hasLaw_map hm.aemeasurable).fun_comp hH
  apply hshift.congr
  filter_upwards [coefficientKernel_observation_ae _
    (center_latitudeJointCLM_surjective μ hQ w hw e he hq0 hq1 y hy) a] with J hJ
  have hk := congrArg (fun z : EuclideanSpace ℝ (Sum (Fin 2) (Fin n)) => z (Sum.inl 1)) hJ
  change latitudeScoreCLM c w e q y (euclideanDisorder J) 1=a (Sum.inl 1) at hk
  rw [latitudeScoreCLM_apply_one, unpack_euclideanDisorder] at hk
  change latitudeIntrinsicMatrix c w e q y hy J = _
  rw [latitudeIntrinsicMatrix_eq, hk]

end
end SlowEquilibration.SphericalLatitudeChartKacRice
