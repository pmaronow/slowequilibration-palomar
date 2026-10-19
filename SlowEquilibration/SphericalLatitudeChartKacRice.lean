-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalChartKacRice
public import SlowEquilibration.SphericalLatitude

@[expose] public section

/-! Genuine marked Kac--Rice for the affine latitude pullback of the
original tensor field. The pullback retains its induced constant and linear
Gaussian components. No replacement finite mixture is introduced. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalChartKacRice SlowEquilibration.SphereChartVolume
open SlowEquilibration.WholeFieldRegression SlowEquilibration.GaussianLocalCoordinates
open scoped Topology ENNReal RealInnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeScale (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)*(1-q^2))

def affineChart (n : ℕ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (u : Vector n) : Vector (n+2) :=
  latitudeMap w e q (manuscriptChart n u)

def affineChartDerivative (n : ℕ) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2))
    (q : ℝ) (u : Vector n) : Vector n →L[ℝ] Vector (n+2) :=
  latitudeScale n q • e.toContinuousLinearMap.comp (manuscriptChartDerivative n u)

theorem affineChart_contDiffOn (n : ℕ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) :
    ContDiffOn ℝ ⊤ (affineChart n w e q) (ball 0 2) := by
  unfold affineChart latitudeMap
  exact contDiffOn_const.add
    ((e.toContinuousLinearMap.contDiff.comp_contDiffOn (manuscriptChart_contDiffOn n)).const_smul _)

theorem affineChart_hasFDerivAt {n : ℕ} (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    {u : Vector n} (hu : ‖u‖ < 2) :
    HasFDerivAt (affineChart n w e q) (affineChartDerivative n e q u) u := by
  have h := (e.toContinuousLinearMap.hasFDerivAt.comp u
    (manuscriptChart_hasFDerivAt hu)).const_smul (latitudeScale n q)
  convert h.const_add (q • w) using 1
  · funext x
    rfl
  · rfl

theorem affineChart_norm_sq {n : ℕ} (w : Vector (n+2))
    (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) {u : Vector n} (hu : ‖u‖ < 2) :
    ‖affineChart n w e q u‖^2=((n+2 : ℕ) : ℝ) :=
  latitudeMap_norm_sq (by omega) w hw e he hq _ (manuscriptChart_norm_sq hu)

theorem affineChartDerivative_tangent {n : ℕ} (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    (q : ℝ) {u : Vector n} (hu : ‖u‖ < 2) (v : Vector n) :
    inner ℝ (affineChartDerivative n e q u v) (affineChart n w e q u) = 0 := by
  simp only [affineChartDerivative, affineChart, latitudeMap, smul_apply,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, he,
    e.inner_map_map, manuscriptChartDerivative_tangent hu, mul_zero, add_zero]

theorem affineChartDerivative_inner {n : ℕ}
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (u v z : Vector n) :
    inner ℝ (affineChartDerivative n e q u v) (affineChartDerivative n e q u z) =
      (latitudeScale n q)^2 *
        inner ℝ (manuscriptChartDerivative n u v) (manuscriptChartDerivative n u z) := by
  simp only [affineChartDerivative, smul_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, real_inner_smul_left, real_inner_smul_right,
    e.inner_map_map]
  ring

def affineChartFeature {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (u : Vector n) : EuclideanDisorder (n+2) P :=
  fieldFeature c (affineChart n w e q u)

def affineChartGamma {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (u : Vector n) :
    EuclideanDisorder (n+2) P →L[ℝ] Vector n :=
  (fderiv ℝ (affineChartFeature c w e q) u).adjoint

theorem affineChartFeature_contDiffOn {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) :
    ContDiffOn ℝ ⊤ (affineChartFeature c w e q) (ball 0 2) :=
  (fieldFeature_contDiff c).comp_contDiffOn (affineChart_contDiffOn n w e q)

theorem affineChartGamma_contDiffOn {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) :
    ContDiffOn ℝ 1 (affineChartGamma c w e q) (ball 0 2) := by
  have hd := (affineChartFeature_contDiffOn c w e q).fderiv_of_isOpen isOpen_ball
    (m := 1) (by simp)
  exact (ContinuousLinearMap.adjoint :
    (Vector n →L[ℝ] EuclideanDisorder (n+2) P) ≃ₗᵢ[ℝ]
      (EuclideanDisorder (n+2) P →L[ℝ] Vector n)).contDiff.comp_contDiffOn hd

theorem affineChartGamma_directional_derivative {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    {u : Vector n} (hu : ‖u‖ < 2) (g : EuclideanDisorder (n+2) P) (v : Vector n) :
    inner ℝ v (affineChartGamma c w e q u g) =
      fderiv ℝ (fun y => field c (unpackDisorder g) (affineChart n w e q y)) u v := by
  have hd := (innerSL ℝ g).hasFDerivAt.comp u
    (((affineChartFeature_contDiffOn c w e q).contDiffAt
      (isOpen_ball.mem_nhds (by simpa using hu))).differentiableAt (by simp)).hasFDerivAt
  have he := hd.fderiv
  simp only [Function.comp_def, innerSL_apply_apply] at he
  have hf : (fun y => field c (unpackDisorder g) (affineChart n w e q y)) =
      fun y => inner ℝ g (affineChartFeature c w e q y) := by
    funext y
    exact (fieldFeature_inner c g _).symm
  rw [hf, he]
  simp only [affineChartGamma, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  exact real_inner_comm _ _

theorem affineChartGamma_apply_jet {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    {u : Vector n} (hu : ‖u‖ < 2) (g : EuclideanDisorder (n+2) P) (i : Fin n) :
    affineChartGamma c w e q u g i = jet c 1 (affineChart n w e q u)
      (fun _ => affineChartDerivative n e q u (EuclideanSpace.basisFun (Fin n) ℝ i))
      (unpackDisorder g) := by
  rw [← EuclideanSpace.basisFun_inner, affineChartGamma_directional_derivative c w e q hu]
  have hd := ((field_contDiff c (unpackDisorder g)).differentiable (by simp)
    (affineChart n w e q u)).hasFDerivAt.comp u (affineChart_hasFDerivAt w e q hu)
  have hh := hd.fderiv
  simp only [Function.comp_def] at hh
  rw [hh]
  simp only [ContinuousLinearMap.comp_apply, jet, iteratedFDeriv_one_apply]

theorem affineChart_gram_matrix {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) {u : Vector n} (hu : ‖u‖ < 2) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (GaussianRegression.gram (affineChartGamma c w e q u)).toLinearMap =
      ((latitudeScale n q)^2 * firstCovariance c 1) • manuscriptChartGram n u := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply]
  change GaussianRegression.gram (affineChartGamma c w e q u)
    (EuclideanSpace.basisFun (Fin n) ℝ j) i = _
  rw [← actual_covariance_gram]
  simp only [actualObservation, affineChartGamma_apply_jet c w e q hu, unpack_euclideanDisorder]
  rw [tangent_gradient_covariance (by omega) c hc _ _ _
    (affineChart_norm_sq w hw e he hq hu) (affineChartDerivative_tangent w e he q hu _),
    affineChartDerivative_inner]
  simp only [manuscriptChartGram, (manuscriptChart_hasFDerivAt hu).fderiv,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem affineChart_gram_det {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) {u : Vector n} (hu : ‖u‖ < 2) :
    (GaussianRegression.gram (affineChartGamma c w e q u)).det =
      ((latitudeScale n q)^2 * firstCovariance c 1)^n * (manuscriptChartGram n u).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    affineChart_gram_matrix c hc w hw e he hq hu, Matrix.det_smul]
  simp

theorem affineChartGamma_surjective {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (hfirst : 0 < firstCovariance c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| < 1) {u : Vector n} (hu : ‖u‖ < 2) :
    Surjective (affineChartGamma c w e q u) := by
  apply surjective_of_gram_det_ne_zero
  rw [affineChart_gram_det c hc w hw e he hq.le hu]
  have hs : 0 < latitudeScale n q := by
    apply Real.sqrt_pos.mpr
    have hsq : 0 < 1-q^2 := by nlinarith [(abs_lt.mp hq).1, (abs_lt.mp hq).2]
    exact mul_pos (div_pos (by positivity) (by positivity)) hsq
  exact (mul_pos (pow_pos (mul_pos (sq_pos_of_pos hs) hfirst) _)
    (manuscriptChartGram_det_pos hu)).ne'

/-- Genuine full-coefficient marked latitude Kac--Rice, including its
induced linear Gaussian term and actual conditional tensor law. -/
theorem affine_latitude_marked_kacRice {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (hfirst : 0 < firstCovariance c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| < 1)
    (psi : EuclideanDisorder (n+2) P → Vector n → ℝ≥0∞)
    (hpsi : Measurable fun z : EuclideanDisorder (n+2) P × Vector n => psi z.1 z.2) :
    let Gamma := affineChartGamma c w e q
    AEMeasurable (zeroCount Gamma (ball 0 2) psi) (stdGaussian (EuclideanDisorder (n+2) P)) ∧
    (∫⁻ z, zeroCount Gamma (ball 0 2) psi z ∂stdGaussian (EuclideanDisorder (n+2) P)) =
      ∫⁻ u in ball 0 2, GaussianRegression.observationPdf (Gamma u) 0 *
        ∫⁻ z, ENNReal.ofReal |(spatialJacobian Gamma z u).det| * psi z u
          ∂GaussianRegression.regressionKernel (Gamma u) 0 := by
  exact marked_kacRice _ _ isOpen_ball (affineChartGamma_contDiffOn c w e q)
    (fun u hu => affineChartGamma_surjective c hc hfirst w hw e he hq (by simpa using hu)) psi hpsi

end
end SlowEquilibration.SphericalLatitudeChartKacRice
