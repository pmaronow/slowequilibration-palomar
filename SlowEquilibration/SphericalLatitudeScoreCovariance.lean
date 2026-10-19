-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeJetCovariance
public import SlowEquilibration.WholeFieldRegression

@[expose] public section

/-! The genuine affine latitude value/radial score is nondegenerate even
when the original field is pure. The determinant gains a strictly positive
term from the affine displacement away from the origin. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeScoreCovariance {P : ℕ} (c : Degree P → ℝ) (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i=0 then (if j=0 then covariancePolynomial c 1 else (1-q^2)*firstCovariance c 1)
    else (if j=0 then (1-q^2)*firstCovariance c 1 else
      (1-q^2)*firstCovariance c 1+(1-q^2)^2*secondCovariance c 1)

theorem latitudeScoreCovariance_det {P : ℕ} (c : Degree P → ℝ) (q : ℝ) :
    (latitudeScoreCovariance c q).det =
      (1-q^2)^2*(covariancePolynomial c 1*(firstCovariance c 1+secondCovariance c 1)-
        (firstCovariance c 1)^2)+
      q^2*(1-q^2)*covariancePolynomial c 1*firstCovariance c 1 := by
  simp only [Matrix.det_fin_two, latitudeScoreCovariance, Fin.isValue, Fin.reduceEq,
    ite_true, ite_false]
  ring

theorem latitudeScoreCovariance_det_pos {P : ℕ} (c : Degree P → ℝ)
    (hv : 0 < covariancePolynomial c 1) (ha : 0 < firstCovariance c 1)
    (hPSD : 0 ≤ covariancePolynomial c 1*(firstCovariance c 1+secondCovariance c 1)-
      (firstCovariance c 1)^2) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1) :
    0 < (latitudeScoreCovariance c q).det := by
  rw [latitudeScoreCovariance_det]
  have ht : 0 < 1-q^2 := by nlinarith [(abs_lt.mp hq1).1, (abs_lt.mp hq1).2]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) hPSD)
    (mul_pos (mul_pos (mul_pos (sq_pos_of_ne_zero hq0) ht) hv) ha)

/-- Positive affine displacement removes the pure-model value/radial
degeneracy; all covariance conditions come from the actual finite mixture. -/
theorem center_latitudeScoreCovariance_det_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1) :
    0 < (latitudeScoreCovariance (centerCoefficients (mixtureCoefficients μ) Q) q).det := by
  apply latitudeScoreCovariance_det_pos _ _ _ _ hq0 hq1
  · rw [covariancePolynomial_center_one, covariancePolynomial_mixture]
    exact μ.xi_pos hQ
  · rw [firstCovariance_center, firstCovariance_mixture]
    exact mul_pos hQ (mixture_xi1_pos μ hQ)
  · rw [covariancePolynomial_center_one, covariancePolynomial_mixture,
      firstCovariance_center, firstCovariance_mixture, secondCovariance_center, secondCovariance_mixture]
    have h := μ.scoreCovariance_det_nonneg hQ.le
    simpa only [Matrix.det_fin_two, FiniteMixture.scoreCovariance, Fin.isValue, Fin.reduceEq,
      ite_true, ite_false, pow_two] using h

def latitudeScoreCLM {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (y : Vector (n+1)) :
    EuclideanDisorder (n+2) P →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => if i=0 then
      flatJetCLM c 0 (latitudeMap w e q y) (fun j => Fin.elim0 j)
      else flatJetCLM c 1 (latitudeMap w e q y) (fun _ => latitudeRadialVector e q y)))

@[simp] theorem latitudeScoreCLM_apply_zero {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (y : Vector (n+1))
    (g : EuclideanDisorder (n+2) P) :
    latitudeScoreCLM c w e q y g 0 = jet c 0 (latitudeMap w e q y)
      (fun j => Fin.elim0 j) (unpackDisorder g) := by simp [latitudeScoreCLM]

@[simp] theorem latitudeScoreCLM_apply_one {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (y : Vector (n+1))
    (g : EuclideanDisorder (n+2) P) :
    latitudeScoreCLM c w e q y g 1 = jet c 1 (latitudeMap w e q y)
      (fun _ => latitudeRadialVector e q y) (unpackDisorder g) := by simp [latitudeScoreCLM]

theorem latitude_score_gram_matrix {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (GaussianRegression.gram (latitudeScoreCLM c w e q y)).toLinearMap =
      ((n+2 : ℕ) : ℝ) • latitudeScoreCovariance c q := by
  have hcov := latitude_value_radial_covariances c hc w hw e he hq y hy
  ext i j
  rw [LinearMap.toMatrix_apply]
  change GaussianRegression.gram (latitudeScoreCLM c w e q y)
    (EuclideanSpace.basisFun (Fin 2) ℝ j) i = _
  rw [← actual_covariance_gram]
  fin_cases i <;> fin_cases j
  · simpa [actualObservation, latitudeScoreCovariance] using hcov.1
  · simpa [actualObservation, latitudeScoreCovariance, mul_assoc] using hcov.2.1
  · rw [covariance_comm]
    simpa [actualObservation, latitudeScoreCovariance, mul_assoc] using hcov.2.1
  · simpa [actualObservation, latitudeScoreCovariance] using hcov.2.2

theorem latitude_score_gram_det {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    (GaussianRegression.gram (latitudeScoreCLM c w e q y)).det =
      ((n+2 : ℕ) : ℝ)^2*(latitudeScoreCovariance c q).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    latitude_score_gram_matrix c hc w hw e he hq y hy, Matrix.det_smul]
  simp

/-- Actual score observation surjectivity, including a pure original
mixture, derived from its true affine score covariance. -/
theorem center_latitudeScoreCLM_surjective {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    Surjective (latitudeScoreCLM (centerCoefficients (mixtureCoefficients μ) Q) w e q y) := by
  apply surjective_of_gram_det_ne_zero
  rw [latitude_score_gram_det _
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) w hw e he hq1.le y hy]
  exact (mul_pos (sq_pos_of_pos (by positivity))
    (center_latitudeScoreCovariance_det_pos μ hQ hq0 hq1)).ne'

end
end SlowEquilibration.SphericalLatitudeChartKacRice
