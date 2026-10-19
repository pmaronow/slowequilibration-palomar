-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSequentialRegression

/-! The normalized score covariance and explicit density of the actual field. -/

@[expose] public section

namespace SlowEquilibration.SphericalSequentialRegression

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw SlowEquilibration.GaussianRegression
open SlowEquilibration.ValueTangentConditioning
open scoped ENNReal Topology RealInnerProductSpace Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem gram_smul_real {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) (r : ℝ) : gram (r • A) = r ^ 2 • gram A := by
  have hadj : (r • A).adjoint = r • A.adjoint := by
    simpa using ContinuousLinearMap.adjoint.map_smulₛₗ r A
  ext w
  simp only [gram, hadj, ContinuousLinearMap.comp_apply, smul_apply, map_smul, smul_smul, pow_two]

theorem lift_norm_sq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) (hA : Surjective A) (w : F) :
    ‖lift A w‖ ^ 2 = inner ℝ w ((gram A).inverse w) := by
  rw [← real_inner_self_eq_norm_sq]
  calc
    inner ℝ (lift A w) (lift A w) = inner ℝ ((gram A).inverse w) (A (lift A w)) := by
      change inner ℝ (A.adjoint ((gram A).inverse w)) (lift A w) = _
      exact A.adjoint_inner_left _ _
    _ = inner ℝ w ((gram A).inverse w) := by
      rw [observation_lift_apply A hA, real_inner_comm]

theorem center_normalized_score_gram_matrix {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (gram ((N : ℝ)⁻¹ • scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x)).toLinearMap =
      (N : ℝ)⁻¹ • μ.scoreCovariance Q := by
  rw [gram_smul_real]
  change LinearMap.toMatrix _ _ ((N : ℝ)⁻¹ ^ 2 •
    (gram (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x)).toLinearMap) = _
  rw [map_smul, center_score_gram_matrix hN μ hQ x hx, smul_smul]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by positivity
  field_simp

theorem center_normalized_score_gram_det {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    (gram ((N : ℝ)⁻¹ • scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x)).det =
      (μ.scoreCovariance Q).det / (N : ℝ) ^ 2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    center_normalized_score_gram_matrix hN μ hQ x hx, Matrix.det_smul]
  simp [div_eq_mul_inv, mul_comm]

/-- The actual normalized score inverse covariance acts by `N Σ⁻¹`. -/
theorem center_normalized_score_inverse_apply {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) (b : EuclideanSpace ℝ (Fin 2)) :
    (fun i => (gram ((N : ℝ)⁻¹ • scoreCLM
      (centerCoefficients (mixtureCoefficients μ) Q) x)).inverse b i) =
      (N : ℝ) • ((μ.scoreCovariance Q)⁻¹ *ᵥ (fun i => b i)) := by
  let A := (N : ℝ)⁻¹ • scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x
  have hA : Surjective A := scaled_observation_surjective _
    (center_score_surjective hN μ hQ hnp x hx) N (by positivity)
  have hi := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (gram A).toLinearMap ((gram A).inverse b)
  rw [center_normalized_score_gram_matrix hN μ hQ.le x hx] at hi
  have hs := (gram_isInvertible A hA).self_apply_inverse b
  change ((N : ℝ)⁻¹ • μ.scoreCovariance Q) *ᵥ
      (fun i => (gram A).inverse b i) = (fun i => gram A ((gram A).inverse b) i) at hi
  rw [hs] at hi
  have hn : (N : ℝ) ≠ 0 := by positivity
  have hd : IsUnit (μ.scoreCovariance Q).det :=
    isUnit_iff_ne_zero.mpr (μ.scoreCovariance_det_pos hQ hnp).ne'
  have h := congrArg (fun v => (μ.scoreCovariance Q)⁻¹ *ᵥ ((N : ℝ) • v)) hi
  simpa only [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hn, one_smul,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec, Matrix.mulVec_smul] using h

/-- The manuscript's genuine score quadratic form `bᵀ Σ_Q⁻¹ b`. -/
def scoreQuadratic (μ : FiniteMixture) (Q : ℝ) (b : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (fun i => b i) ⬝ᵥ ((μ.scoreCovariance Q)⁻¹ *ᵥ (fun i => b i))

theorem center_normalized_score_lift_norm_sq {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) (b : EuclideanSpace ℝ (Fin 2)) :
    ‖lift ((N : ℝ)⁻¹ • scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x) b‖ ^ 2 =
      (N : ℝ) * scoreQuadratic μ Q b := by
  rw [lift_norm_sq _ (scaled_observation_surjective _
    (center_score_surjective hN μ hQ hnp x hx) N (by positivity))]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  change (fun i => b i) ⬝ᵥ (fun i => (gram ((N : ℝ)⁻¹ • scoreCLM
    (centerCoefficients (mixtureCoefficients μ) Q) x)).inverse b i) = _
  rw [center_normalized_score_inverse_apply hN μ hQ hnp x hx b]
  simp only [dotProduct_smul, smul_eq_mul, scoreQuadratic]

/-- Literal physical two-dimensional score density, with the exact `N` and
`2π` factors and the source inverse-covariance quadratic exponent. -/
theorem normalizedScorePdf_eq {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) (b : EuclideanSpace ℝ (Fin 2)) :
    normalizedScorePdf (centerCoefficients (mixtureCoefficients μ) Q) x b =
      ENNReal.ofReal ((N : ℝ) / (2 * Real.pi * Real.sqrt (μ.scoreCovariance Q).det) *
        Real.exp (-(N : ℝ) / 2 * scoreQuadratic μ Q b)) := by
  unfold normalizedScorePdf observationPdf
  rw [center_normalized_score_gram_det hN μ hQ.le x hx,
    center_normalized_score_lift_norm_sq hN μ hQ hnp x hx b]
  have hn : (N : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt ((μ.scoreCovariance Q).det / (N : ℝ) ^ 2) =
      Real.sqrt (μ.scoreCovariance Q).det / N := by
    rw [Real.sqrt_div (μ.scoreCovariance_det_pos hQ hnp).le,
      Real.sqrt_sq (Nat.cast_nonneg N)]
  rw [hs]
  have hnrm : GaussianDensity.normalizer (EuclideanSpace ℝ (Fin 2)) = (2 * Real.pi)⁻¹ := by
    simp [GaussianDensity.normalizer]
  rw [hnrm]
  congr 1
  congr 1
  · field_simp
  · congr 1
    ring

/-- The exact actual scalar value variance is `N ξ(Q)`. -/
theorem center_value_gram {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    gram (valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x) =
      ((N : ℝ) * μ.xi Q) • ContinuousLinearMap.id ℝ ℝ := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let B := valueCLM c x
  have h := actual_scalar_cross_covariance B B (1 : ℝ)
  have h1 : gram B 1 = (N : ℝ) * μ.xi Q := by
    have he : cov[jet c 0 x (fun i => Fin.elim0 i), jet c 0 x (fun i => Fin.elim0 i);
        disorderLaw N μ.maxDegree] = gram B 1 := by
      simpa only [B, gram, ContinuousLinearMap.comp_apply, valueCLM, flatJetCLM_apply, unpack_euclideanDisorder,
        RCLike.inner_apply, conj_trivial, mul_one] using h
    exact he.symm.trans (center_value_radial_covariances hN μ hQ x hx).1
  apply ContinuousLinearMap.ext
  intro b
  have hb := (gram B).map_smul b (1 : ℝ)
  simpa only [smul_eq_mul, mul_one, h1, smul_apply, ContinuousLinearMap.id_apply, mul_comm] using hb

theorem center_normalized_value_gram {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    gram ((N : ℝ)⁻¹ • valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x) =
      (μ.xi Q / N) • ContinuousLinearMap.id ℝ ℝ := by
  rw [gram_smul_real, center_value_gram hN μ hQ x hx, smul_smul]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by positivity
  field_simp

theorem center_normalized_value_lift_norm_sq {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) (b : ℝ) :
    ‖lift (((n+1 : ℕ) : ℝ)⁻¹ • valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x) b‖ ^ 2 =
      (n+1 : ℕ) * b ^ 2 / μ.xi Q := by
  let A := ((n+1 : ℕ) : ℝ)⁻¹ • valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x
  have hA : Surjective A := scaled_observation_surjective _ (center_value_surjective μ hQ x hx)
    (n+1 : ℕ) (by positivity)
  have hg := center_normalized_value_gram (by omega) μ hQ.le x hx
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hxi : μ.xi Q ≠ 0 := (μ.xi_pos hQ).ne'
  have hi : μ.xi Q / (n+1 : ℕ) * (gram A).inverse b = b := by
    have he := congrArg (fun T : ℝ →L[ℝ] ℝ => T ((gram A).inverse b)) hg
    exact he.symm.trans ((gram_isInvertible A hA).self_apply_inverse b)
  have hinv : (gram A).inverse b = (n+1 : ℕ) * b / μ.xi Q := by
    calc
      _ = b / (μ.xi Q / (n+1 : ℕ)) :=
        (eq_div_iff (div_ne_zero hxi hn)).mpr (by rwa [mul_comm])
      _ = _ := by field_simp
  rw [lift_norm_sq _ hA]
  change inner ℝ b ((gram A).inverse b) = _
  rw [hinv, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- Literal physical scalar score density, including the pure case. -/
theorem normalizedValuePdf_eq {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) (b : ℝ) :
    normalizedValuePdf (centerCoefficients (mixtureCoefficients μ) Q) x b =
      ENNReal.ofReal (Real.sqrt ((n+1 : ℕ) / (2 * Real.pi * μ.xi Q)) *
        Real.exp (-((n+1 : ℕ) : ℝ) * b ^ 2 / (2 * μ.xi Q))) := by
  unfold normalizedValuePdf observationPdf
  rw [center_normalized_value_lift_norm_sq μ hQ x hx b,
    center_normalized_value_gram (by omega) μ hQ.le x hx]
  have hd (r : ℝ) : (r • ContinuousLinearMap.id ℝ ℝ).det = r := by
    simp [ContinuousLinearMap.det, LinearMap.det_smul]
  rw [hd]
  have hnrm : GaussianDensity.normalizer ℝ = (Real.sqrt (2 * Real.pi))⁻¹ := by
    simp [GaussianDensity.normalizer, Real.sqrt_eq_rpow]
  rw [hnrm]
  have hp : (Real.sqrt (μ.xi Q / (n+1 : ℕ)))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ =
      Real.sqrt ((n+1 : ℕ) / (2 * Real.pi * μ.xi Q)) := by
    rw [← mul_inv, ← Real.sqrt_mul (div_nonneg (μ.xi_pos hQ).le (by positivity)), ← Real.sqrt_inv]
    congr 1
    field_simp
  rw [hp]
  congr 2
  congr 1
  ring

/-- The manuscript's normalized mixed score density `p_N(h,k)`. -/
def physicalScorePdf (N : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (b : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  ENNReal.ofReal ((N : ℝ) / (2 * Real.pi * Real.sqrt (μ.scoreCovariance Q).det) *
    Real.exp (-(N : ℝ) / 2 * scoreQuadratic μ Q b))

/-- The manuscript's normalized scalar score density, used in pure models. -/
def physicalValuePdf (N : ℕ) (μ : FiniteMixture) (Q b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (N / (2 * Real.pi * μ.xi Q)) *
    Real.exp (-(N : ℝ) * b ^ 2 / (2 * μ.xi Q)))

/-- Exact source full-field disintegration with the physical mixed density,
for every Borel nonnegative mark of all original tensor coefficients. -/
theorem intrinsic_zero_physical_score_disintegration {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (phi : Disorder (n+1) μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, phi J ∂coefficientKernel (intrinsicGamma c x) 0) =
      ∫⁻ b, physicalScorePdf (n+1) μ Q b *
        ∫⁻ J, phi J ∂coefficientKernel (jointCLM c x (tangentFrame x hx))
          (jointScoreTarget n (((n+1 : ℕ) : ℝ) • b)) := by
  dsimp only
  rw [intrinsic_zero_normalized_score_disintegration μ hQ hnp x hx phi hphi]
  apply lintegral_congr
  intro b
  rw [normalizedScorePdf_eq (by omega) μ hQ hnp x hx b]
  rfl

/-- Exact scalar source disintegration with the physical one-dimensional
density. Specializing to a pure mixture gives its proper `(N h,0)` law. -/
theorem intrinsic_zero_physical_value_disintegration {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (phi : Disorder (n+1) μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, phi J ∂coefficientKernel (intrinsicGamma c x) 0) =
      ∫⁻ b, physicalValuePdf (n+1) μ Q b *
        ∫⁻ J, phi J ∂coefficientKernel (valueTangentCLM c x (tangentFrame x hx))
          (jointValueTarget n ((n+1 : ℕ) * b)) := by
  dsimp only
  rw [intrinsic_zero_normalized_value_disintegration μ hQ x hx phi hphi]
  apply lintegral_congr
  intro b
  rw [normalizedValuePdf_eq μ hQ x hx b]
  rfl

end
end SlowEquilibration.SphericalSequentialRegression
