-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeScoreCovariance
public import SlowEquilibration.DirectionalHessianConditioning

@[expose] public section

/-! Actual joint value/section-radial/tangent-gradient observation of the
original tensor field on an affine latitude, including its true covariance
and surjectivity. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicHessianLaw
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeEmbeddedFrame {n : ℕ} (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2))
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) : Fin n → Vector (n+2) :=
  fun i => e (tangentFrame y hy i)

theorem latitudeEmbeddedFrame_orthonormal {n : ℕ} (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2))
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    Orthonormal ℝ (latitudeEmbeddedFrame e y hy) := by
  simpa only [orthonormal_iff_ite, latitudeEmbeddedFrame, e.inner_map_map] using
    tangentFrame_orthonormal y hy

theorem latitudeEmbeddedFrame_tangent {n : ℕ} (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    (q : ℝ) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (i : Fin n) :
    inner ℝ (latitudeEmbeddedFrame e y hy i) (latitudeMap w e q y)=0 := by
  simp only [latitudeEmbeddedFrame, latitudeMap, inner_add_right, real_inner_smul_right,
    he, e.inner_map_map, tangentFrame_tangent y hy, mul_zero, add_zero]

def latitudeGradientDirections {n : ℕ} (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2))
    (q : ℝ) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) : Fin n → Vector (n+2) :=
  fun i => latitudeScale n q • latitudeEmbeddedFrame e y hy i

theorem latitudeGradientDirections_tangent {n : ℕ} (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    (q : ℝ) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (i : Fin n) :
    inner ℝ (latitudeGradientDirections e q y hy i) (latitudeMap w e q y)=0 := by
  rw [latitudeGradientDirections, real_inner_smul_left, latitudeEmbeddedFrame_tangent w e he q y hy, mul_zero]

theorem latitudeGradientDirections_inner {n : ℕ} (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2))
    (q : ℝ) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (i j : Fin n) :
    inner ℝ (latitudeGradientDirections e q y hy i) (latitudeGradientDirections e q y hy j) =
      (latitudeScale n q)^2*(if i=j then 1 else 0) := by
  simp only [latitudeGradientDirections, real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.mp (latitudeEmbeddedFrame_orthonormal e y hy)]
  ring

theorem latitude_radial_gradient_inner_zero {n : ℕ}
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (i : Fin n) :
    inner ℝ (latitudeRadialVector e q y) (latitudeGradientDirections e q y hy i)=0 := by
  simp only [latitudeRadialVector, latitudeGradientDirections, latitudeEmbeddedFrame,
    real_inner_smul_left, real_inner_smul_right, e.inner_map_map]
  rw [show inner ℝ y (tangentFrame y hy i)=0 by
    rw [real_inner_comm]; exact tangentFrame_tangent y hy i]
  simp

def latitudeJointCLM {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    EuclideanDisorder (n+2) P →L[ℝ] EuclideanSpace ℝ (Sum (Fin 2) (Fin n)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Sum (Fin 2) (Fin n) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim
      (fun i => (EuclideanSpace.proj i).comp (latitudeScoreCLM c w e q y))
      (fun i => (EuclideanSpace.proj i).comp
        (gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy)))))

@[simp] theorem latitudeJointCLM_apply_inl {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (g : EuclideanDisorder (n+2) P) (i : Fin 2) :
    latitudeJointCLM c w e q y hy g (Sum.inl i)=latitudeScoreCLM c w e q y g i := by
  simp [latitudeJointCLM]

@[simp] theorem latitudeJointCLM_apply_inr {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (g : EuclideanDisorder (n+2) P) (i : Fin n) :
    latitudeJointCLM c w e q y hy g (Sum.inr i)=
      gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy) g i := by
  simp [latitudeJointCLM]

theorem latitude_joint_gram_matrix {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Sum (Fin 2) (Fin n)) ℝ).toBasis
      (EuclideanSpace.basisFun (Sum (Fin 2) (Fin n)) ℝ).toBasis
      (GaussianRegression.gram (latitudeJointCLM c w e q y hy)).toLinearMap =
      Matrix.fromBlocks (((n+2 : ℕ) : ℝ) • latitudeScoreCovariance c q) 0 0
        (((latitudeScale n q)^2*firstCovariance c 1) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  classical
  have hx := latitudeMap_norm_sq (by omega) w hw e he hq y hy
  have hcross (i : Fin 2) (j : Fin n) :
      cov[fun J : Disorder (n+2) P => latitudeScoreCLM c w e q y (euclideanDisorder J) i,
        fun J : Disorder (n+2) P => gradientCLM c (latitudeMap w e q y)
          (latitudeGradientDirections e q y hy) (euclideanDisorder J) j; disorderLaw (n+2) P]=0 := by
    fin_cases i
    · simpa [latitudeScoreCLM] using
        value_tangent_gradient_covariance_zero c hc _ _ (latitudeGradientDirections_tangent w e he q y hy j)
    · have hh : cov[jet c 1 (latitudeMap w e q y) (fun _ => latitudeRadialVector e q y),
          jet c 1 (latitudeMap w e q y) (fun _ => latitudeGradientDirections e q y hy j);
            disorderLaw (n+2) P]=0 := by
        rw [covariance_comm, tangent_gradient_covariance (by omega) c hc _ _ _ hx
          (latitudeGradientDirections_tangent w e he q y hy j), real_inner_comm,
          latitude_radial_gradient_inner_zero e q y hy j, mul_zero]
      simpa [latitudeScoreCLM] using hh
  ext i j
  rw [LinearMap.toMatrix_apply]
  change GaussianRegression.gram (latitudeJointCLM c w e q y hy)
    (EuclideanSpace.basisFun (Sum (Fin 2) (Fin n)) ℝ j) i = _
  rw [← actual_covariance_gram]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hs := congrFun (congrFun (latitude_score_gram_matrix c hc w hw e he hq y hy) i) j
      rw [LinearMap.toMatrix_apply] at hs
      change GaussianRegression.gram (latitudeScoreCLM c w e q y)
        (EuclideanSpace.basisFun (Fin 2) ℝ j) i = _ at hs
      rw [← actual_covariance_gram] at hs
      simpa only [actualObservation, latitudeJointCLM_apply_inl, Matrix.fromBlocks_apply₁₁] using hs
    | inr j =>
      simpa only [actualObservation, latitudeJointCLM_apply_inl, latitudeJointCLM_apply_inr,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using hcross i j
  | inr i =>
    cases j with
    | inl j =>
      rw [covariance_comm]
      simpa only [actualObservation, latitudeJointCLM_apply_inl, latitudeJointCLM_apply_inr,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using hcross j i
    | inr j =>
      simp only [actualObservation, latitudeJointCLM_apply_inr, gradientCLM_apply, unpack_euclideanDisorder,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      rw [tangent_gradient_covariance (by omega) c hc _ _ _ hx
        (latitudeGradientDirections_tangent w e he q y hy i), latitudeGradientDirections_inner]
      ring

theorem latitude_joint_gram_det {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    (GaussianRegression.gram (latitudeJointCLM c w e q y hy)).det =
      (((n+2 : ℕ) : ℝ)^2*(latitudeScoreCovariance c q).det)*
        ((latitudeScale n q)^2*firstCovariance c 1)^n := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Sum (Fin 2) (Fin n)) ℝ).toBasis,
    latitude_joint_gram_matrix c hc w hw e he hq y hy,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_smul, Matrix.det_one]
  simp

/-- Every true affine joint score/gradient target is valid for every finite
mixture, including pure original fields, when 0<|q|<1. -/
theorem center_latitudeJointCLM_surjective {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    Surjective (latitudeJointCLM (centerCoefficients (mixtureCoefficients μ) Q) w e q y hy) := by
  apply surjective_of_gram_det_ne_zero
  rw [latitude_joint_gram_det _
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) w hw e he hq1.le y hy]
  have hs : 0 < (latitudeScale n q)^2 := by
    rw [latitudeScale_sq hq1.le]
    have hq2 : 0 < 1-q^2 := by nlinarith [(abs_lt.mp hq1).1, (abs_lt.mp hq1).2]
    positivity
  have hf : 0 < firstCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1 := by
    rw [firstCovariance_center, firstCovariance_mixture]
    exact mul_pos hQ (mixture_xi1_pos μ hQ)
  exact (mul_pos (mul_pos (sq_pos_of_pos (by positivity))
    (center_latitudeScoreCovariance_det_pos μ hQ hq0 hq1)) (pow_pos (mul_pos hs hf) n)).ne'

end
end SlowEquilibration.SphericalLatitudeChartKacRice
