-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeGlobalCount
public import SlowEquilibration.SphericalSequentialRegression

@[expose] public section

/-! Actual full-tensor score disintegration for the affine latitude field,
at its literal zero intrinsic gradient. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicHessianLaw
open SlowEquilibration.GaussianRegression SlowEquilibration.SphericalSequentialRegression
open SlowEquilibration.IntrinsicGradientRegression SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalChartGeometry SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphereChartVolume
open scoped Topology ENNReal RealInnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitude_gradient_score_adjoint_zero {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    (gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy)).comp
      (latitudeScoreCLM c w e q y).adjoint=0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro i
  have h := actual_scalar_cross_covariance ((EuclideanSpace.proj i).comp
    (gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy)))
    (latitudeScoreCLM c w e q y) (EuclideanSpace.basisFun (Fin 2) ℝ j)
  simp only [EuclideanSpace.basisFun_inner, ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj] at h
  change cov[fun J : Disorder (n+2) P => gradientCLM c (latitudeMap w e q y)
      (latitudeGradientDirections e q y hy) (euclideanDisorder J) i,
    fun J : Disorder (n+2) P => latitudeScoreCLM c w e q y (euclideanDisorder J) j;
      disorderLaw (n+2) P] = _ at h
  change gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy)
    ((latitudeScoreCLM c w e q y).adjoint (EuclideanSpace.basisFun (Fin 2) ℝ j)) i=0
  rw [← h]
  simp only [gradientCLM_apply, unpack_euclideanDisorder]
  fin_cases j
  · rw [covariance_comm]
    simpa [latitudeScoreCLM] using value_tangent_gradient_covariance_zero c hc _ _
      (latitudeGradientDirections_tangent w e he q y hy i)
  · have hh : cov[jet c 1 (latitudeMap w e q y) (fun _ => latitudeGradientDirections e q y hy i),
        jet c 1 (latitudeMap w e q y) (fun _ => latitudeRadialVector e q y);
          disorderLaw (n+2) P]=0 := by
      rw [tangent_gradient_covariance (by omega) c hc _ _ _
        (latitudeMap_norm_sq (by omega) w hw e he hq y hy)
        (latitudeGradientDirections_tangent w e he q y hy i), real_inner_comm,
        latitude_radial_gradient_inner_zero e q y hy i, mul_zero]
    simpa [latitudeScoreCLM] using hh

theorem latitudeJointCLM_ker_gradient_score {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    (latitudeJointCLM c w e q y hy).ker =
      (gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy)).ker ⊓
        (latitudeScoreCLM c w e q y).ker := by
  ext g
  change latitudeJointCLM c w e q y hy g=0 ↔
    gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy) g=0 ∧
      latitudeScoreCLM c w e q y g=0
  constructor
  · intro h
    constructor
    · apply PiLp.ext
      intro i
      simpa only [latitudeJointCLM_apply_inr, PiLp.zero_apply] using congrArg (fun v => v (Sum.inr i)) h
    · apply PiLp.ext
      intro i
      simpa only [latitudeJointCLM_apply_inl, PiLp.zero_apply] using congrArg (fun v => v (Sum.inl i)) h
  · rintro ⟨hg, hs⟩
    apply PiLp.ext
    intro i
    cases i <;> simp [hg, hs]

theorem center_latitudeGradientCLM_surjective {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    Surjective (gradientCLM (centerCoefficients (mixtureCoefficients μ) Q)
      (latitudeMap w e q y) (latitudeGradientDirections e q y hy)) := by
  intro b
  let a : EuclideanSpace ℝ (Sum (Fin 2) (Fin n)) := WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun i => b i))
  obtain ⟨g, hg⟩ := center_latitudeJointCLM_surjective μ hQ w hw e he hq0 hq1 y hy a
  refine ⟨g, ?_⟩
  apply PiLp.ext
  intro i
  exact congrArg (fun v => v (Sum.inr i)) hg

theorem latitudeJointCLM_score_lift {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (hscore : Surjective (latitudeScoreCLM c w e q y)) (b : EuclideanSpace ℝ (Fin 2)) :
    latitudeJointCLM c w e q y hy (lift (latitudeScoreCLM c w e q y) b)=jointScoreTarget n b := by
  apply PiLp.ext
  intro i
  cases i with
  | inl i =>
    change latitudeScoreCLM c w e q y (lift (latitudeScoreCLM c w e q y) b) i=b i
    rw [observation_lift_apply _ hscore]
  | inr i =>
    change gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy)
      (lift (latitudeScoreCLM c w e q y) b) i=0
    rw [orthogonal_observation_lift_zero _ _
      (latitude_gradient_score_adjoint_zero c hc w hw e he hq y hy)]
    rfl

/-- Full original coefficient law at the genuine zero latitude gradient,
disintegrated over its actual value and section-radial law. -/
theorem latitude_gradient_zero_score_disintegration {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (phi : Disorder (n+2) μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, phi J ∂coefficientKernel
      (gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy)) 0) =
      ∫⁻ b, ∫⁻ J, phi J ∂coefficientKernel (latitudeJointCLM c w e q y hy)
        (jointScoreTarget n b) ∂observationLaw (latitudeScoreCLM c w e q y) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hs := center_latitudeScoreCLM_surjective μ hQ w hw e he hq0 hq1 y hy
  have h := coefficientKernel_orthogonal_zero_disintegration
    (gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy))
    (latitudeScoreCLM c w e q y) (latitudeJointCLM c w e q y hy)
    (center_latitudeGradientCLM_surjective μ hQ w hw e he hq0 hq1 y hy) hs
    (center_latitudeJointCLM_surjective μ hQ w hw e he hq0 hq1 y hy)
    (latitude_gradient_score_adjoint_zero c hc w hw e he hq1.le y hy)
    (latitudeJointCLM_ker_gradient_score c w e q y hy) phi hphi
  simpa only [latitudeJointCLM_score_lift c hc w hw e he hq1.le y hy hs] using h


theorem latitude_gradient_zero_iff_intrinsic {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (g : EuclideanDisorder (n+2) P) :
    gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy) g=0 ↔
      surfaceGradient (latitudeField c (unpackDisorder g) w e q) y=0 := by
  have hsphere : SphericalAging.HardSphereDynamics.OnSphere y := by
    change inner ℝ y y = _
    rw [real_inner_self_eq_norm_sq]
    exact hy
  let v : tangentPlane y := ⟨surfaceGradient (latitudeField c (unpackDisorder g) w e q) y,
    tangentProjection_mem (by omega) y _ hsphere⟩
  have hrepr : gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy) g =
      (tangentBasis y hy).repr v := by
    apply PiLp.ext
    intro i
    rw [OrthonormalBasis.repr_apply_apply]
    change _ = inner ℝ (tangentFrame y hy i)
      (surfaceGradient (latitudeField c (unpackDisorder g) w e q) y)
    rw [real_inner_comm, inner_surfaceGradient]
    have hp : tangentProjection y (tangentFrame y hy i)=tangentFrame y hy i := by
      rw [tangentProjection_eq_starProjection (by omega) y hsphere]
      exact (tangentPlane y).starProjection_eq_self_iff.mpr (tangentBasis y hy i).2
    rw [hp, latitudeField_directional_derivative, gradientCLM_apply]
    rfl
  rw [hrepr, (tangentBasis y hy).repr.map_eq_zero_iff]
  exact Subtype.ext_iff


theorem affineChartGamma_ker_eq_latitudeGradient {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    {u : Vector n} (hu : ‖u‖ < 2) (huy : manuscriptChart n u=y) :
    (affineChartGamma c w e q u).ker =
      (gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy)).ker := by
  ext g
  change affineChartGamma c w e q u g=0 ↔ _
  rw [affineChartGamma_zero_iff_intrinsic c w e q hu]
  rw [huy]
  exact (latitude_gradient_zero_iff_intrinsic c w e q y hy g).symm

/-- The actual chart-gradient posterior is disintegrated over actual score
values, preserving the full original tensor field at every stage. -/
theorem latitude_chart_zero_score_disintegration {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    {u : Vector n} (hu : ‖u‖ < 2) (huy : manuscriptChart n u=y)
    (phi : Disorder (n+2) μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, phi J ∂coefficientKernel (affineChartGamma c w e q u) 0) =
      ∫⁻ b, ∫⁻ J, phi J ∂coefficientKernel (latitudeJointCLM c w e q y hy)
        (jointScoreTarget n b) ∂observationLaw (latitudeScoreCLM c w e q y) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hf : 0 < firstCovariance c 1 := by
    rw [firstCovariance_center, firstCovariance_mixture]
    exact mul_pos hQ (mixture_xi1_pos μ hQ)
  rw [coefficientKernel_zero_eq_of_ker_eq
    (affineChartGamma c w e q u)
    (gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy))
    (affineChartGamma_surjective c hc hf w hw e he hq1 hu)
    (center_latitudeGradientCLM_surjective μ hQ w hw e he hq0 hq1 y hy)
    (affineChartGamma_ker_eq_latitudeGradient c w e q y hy hu huy)]
  exact latitude_gradient_zero_score_disintegration μ hQ w hw e he hq0 hq1 y hy phi hphi

end
end SlowEquilibration.SphericalLatitudeChartKacRice
