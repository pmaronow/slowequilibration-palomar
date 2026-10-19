-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeScoreCovariance
public import SlowEquilibration.SphericalScoreDensity

@[expose] public section

/-! Exact density of the actual normalized value/section-radial observations
on an affine latitude. All original finite mixtures, including pure mixtures,
have this nonsingular two-dimensional law at 0<|q|<1. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.GaussianRegression
open SlowEquilibration.SphericalSequentialRegression
open scoped Topology ENNReal RealInnerProductSpace Matrix
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem normalized_latitude_score_gram_matrix {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (gram ((((n+2 : ℕ) : ℝ)⁻¹) • latitudeScoreCLM c w e q y)).toLinearMap =
      (((n+2 : ℕ) : ℝ)⁻¹) • latitudeScoreCovariance c q := by
  rw [gram_smul_real]
  change LinearMap.toMatrix _ _ ((((n+2 : ℕ) : ℝ)⁻¹)^2 •
    (gram (latitudeScoreCLM c w e q y)).toLinearMap)=_
  rw [map_smul, latitude_score_gram_matrix c hc w hw e he hq y hy, smul_smul]
  congr 1
  have hn : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem normalized_latitude_score_gram_det {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    (gram ((((n+2 : ℕ) : ℝ)⁻¹) • latitudeScoreCLM c w e q y)).det =
      (latitudeScoreCovariance c q).det / ((n+2 : ℕ) : ℝ)^2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    normalized_latitude_score_gram_matrix c hc w hw e he hq y hy, Matrix.det_smul]
  simp [div_eq_mul_inv, mul_comm]

theorem center_normalized_latitude_score_inverse_apply {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (b : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (fun i => (gram ((((n+2 : ℕ) : ℝ)⁻¹) • latitudeScoreCLM c w e q y)).inverse b i) =
      ((n+2 : ℕ) : ℝ) • ((latitudeScoreCovariance c q)⁻¹ *ᵥ (fun i => b i)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let A := (((n+2 : ℕ) : ℝ)⁻¹) • latitudeScoreCLM c w e q y
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hA : Surjective A := scaled_observation_surjective _
    (center_latitudeScoreCLM_surjective μ hQ w hw e he hq0 hq1 y hy) ((n+2 : ℕ) : ℝ) (by positivity)
  have hi := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (gram A).toLinearMap ((gram A).inverse b)
  rw [normalized_latitude_score_gram_matrix c hc w hw e he hq1.le y hy] at hi
  have hs := (gram_isInvertible A hA).self_apply_inverse b
  change ((((n+2 : ℕ) : ℝ)⁻¹) • latitudeScoreCovariance c q) *ᵥ
    (fun i => (gram A).inverse b i)=(fun i => gram A ((gram A).inverse b) i) at hi
  rw [hs] at hi
  have hn : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd : IsUnit (latitudeScoreCovariance c q).det :=
    isUnit_iff_ne_zero.mpr (center_latitudeScoreCovariance_det_pos μ hQ hq0 hq1).ne'
  have h := congrArg (fun v => (latitudeScoreCovariance c q)⁻¹ *ᵥ (((n+2 : ℕ) : ℝ) • v)) hi
  simpa only [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hn, one_smul,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec, Matrix.mulVec_smul] using h

def latitudeScoreQuadratic {P : ℕ} (c : Degree P → ℝ) (q : ℝ) (b : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (fun i => b i) ⬝ᵥ ((latitudeScoreCovariance c q)⁻¹ *ᵥ (fun i => b i))

theorem center_normalized_latitude_score_lift_norm_sq {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (b : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ‖lift ((((n+2 : ℕ) : ℝ)⁻¹) • latitudeScoreCLM c w e q y) b‖^2 =
      ((n+2 : ℕ) : ℝ)*latitudeScoreQuadratic c q b := by
  dsimp only
  rw [lift_norm_sq _ (scaled_observation_surjective _
    (center_latitudeScoreCLM_surjective μ hQ w hw e he hq0 hq1 y hy) ((n+2 : ℕ) : ℝ) (by positivity))]
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change (fun i => b i) ⬝ᵥ (fun i => (gram ((((n+2 : ℕ) : ℝ)⁻¹) • latitudeScoreCLM
    (centerCoefficients (mixtureCoefficients μ) Q) w e q y)).inverse b i)=_
  rw [center_normalized_latitude_score_inverse_apply μ hQ w hw e he hq0 hq1 y hy b]
  simp only [dotProduct_smul, smul_eq_mul, latitudeScoreQuadratic]

def latitudePhysicalScorePdf {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (q : ℝ)
    (b : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  ENNReal.ofReal (((n+2 : ℕ) : ℝ)/(2*Real.pi*Real.sqrt (latitudeScoreCovariance c q).det)*
    Real.exp (-((n+2 : ℕ) : ℝ)/2*latitudeScoreQuadratic c q b))

/-- The literal actual score density, with its exact N and 2π factors,
independent of the position and chosen orthogonal frame. -/
theorem normalized_latitudeScorePdf_eq {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (b : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    observationPdf ((((n+2 : ℕ) : ℝ)⁻¹) • latitudeScoreCLM c w e q y) b =
      latitudePhysicalScorePdf n c q b := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  unfold observationPdf latitudePhysicalScorePdf
  rw [normalized_latitude_score_gram_det c hc w hw e he hq1.le y hy,
    center_normalized_latitude_score_lift_norm_sq μ hQ w hw e he hq0 hq1 y hy b]
  have hn : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt ((latitudeScoreCovariance c q).det/((n+2 : ℕ) : ℝ)^2)=
      Real.sqrt (latitudeScoreCovariance c q).det / ((n+2 : ℕ) : ℝ) := by
    rw [Real.sqrt_div (center_latitudeScoreCovariance_det_pos μ hQ hq0 hq1).le,
      Real.sqrt_sq (Nat.cast_nonneg _)]
  rw [hs]
  have hnrm : GaussianDensity.normalizer (EuclideanSpace ℝ (Fin 2))=(2*Real.pi)⁻¹ := by
    simp [GaussianDensity.normalizer]
  rw [hnrm]
  congr 1
  congr 1
  · field_simp
    rfl
  · congr 1
    ring

end
end SlowEquilibration.SphericalLatitudeChartKacRice
