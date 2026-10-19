-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphereHessian
public import SlowEquilibration.JointFieldRegression

/-!
# Canonical regression at the actual intrinsic spherical gradient

The observation takes values in the complete tangent plane, with the ambient
Euclidean inner product. Its covariance, nondegeneracy, and full original-tensor
zero-target law are derived from the actual mixed field. Chart conditioning
agrees pointwise at zero with this coordinate-free law.
-/

@[expose] public section

namespace SlowEquilibration.IntrinsicGradientRegression

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.WholeFieldRegression
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphericalChartGeometry SlowEquilibration.SphereHessian
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

/-- The actual ambient Riesz gradient, retaining all original coefficients. -/
def ambientGradientCLM {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    EuclideanDisorder N P →L[ℝ] Vector N :=
  gradientCLM c x (EuclideanSpace.basisFun (Fin N) ℝ)

@[simp] theorem ambientGradientCLM_apply {N P : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (g : EuclideanDisorder N P) :
    ambientGradientCLM c x g = gradient (field c (unpackDisorder g)) x := by
  apply PiLp.ext
  intro i
  rw [ambientGradientCLM, gradientCLM_apply, jet, iteratedFDeriv_one_apply]
  rw [← inner_gradient_left, real_inner_comm, EuclideanSpace.basisFun_inner]

/-- The genuine full tangent-gradient observation, without a chosen frame. -/
def intrinsicGamma {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    EuclideanDisorder N P →L[ℝ] tangentPlane x :=
  (tangentPlane x).orthogonalProjectionOnto.comp (ambientGradientCLM c x)

@[simp] theorem intrinsicGamma_inner {N P : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (g : EuclideanDisorder N P) (v : tangentPlane x) :
    inner ℝ v (intrinsicGamma c x g) = jet c 1 x (fun _ => (v : Vector N)) (unpackDisorder g) := by
  rw [intrinsicGamma, ContinuousLinearMap.comp_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, ambientGradientCLM_apply,
    real_inner_comm, inner_gradient_left, jet, iteratedFDeriv_one_apply]

/-- On the manuscript sphere the tangent-valued observation is literally the
actual surface gradient, rather than a covariance-matching substitute. -/
theorem intrinsicGamma_coe {N P : ℕ} (hN : N ≠ 0) (c : Degree P → ℝ)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) (g : EuclideanDisorder N P) :
    (intrinsicGamma c x g : Vector N) = surfaceGradient (field c (unpackDisorder g)) x := by
  rw [intrinsicGamma, ContinuousLinearMap.comp_apply, ambientGradientCLM_apply, surfaceGradient,
    tangentProjection_eq_starProjection hN x
      (by change inner ℝ x x = _; rw [real_inner_self_eq_norm_sq]; exact hx)]
  rfl

/-- Actual scalar covariances recover the Gram operator in any finite-dimensional
Euclidean target, including the true tangent subspace. -/
theorem actual_inner_covariance_gram {N P : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : EuclideanDisorder N P →L[ℝ] F) (v w : F) :
    cov[fun J : Disorder N P => inner ℝ v (A (euclideanDisorder J)),
      fun J : Disorder N P => inner ℝ w (A (euclideanDisorder J)); disorderLaw N P] =
      inner ℝ v (GaussianRegression.gram A w) := by
  have h := (actual_flattened_gaussian N P).covariance_fun_comp
    (f := fun g => inner ℝ v (A g)) (g := fun g => inner ℝ w (A g))
    (continuous_const.inner A.continuous).measurable.aemeasurable
    (continuous_const.inner A.continuous).measurable.aemeasurable
  rw [h]
  have he (u : F) : (fun g : EuclideanDisorder N P => inner ℝ u (A g)) =
      fun g => inner ℝ (A.adjoint u) g := by
    funext g
    rw [A.adjoint_inner_left]
  rw [he v, he w, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply, A.adjoint_inner_left]
  rfl

/-- Exact actual covariance operator on the complete tangent plane. -/
theorem intrinsicGamma_gram {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    GaussianRegression.gram (intrinsicGamma c x) =
      firstCovariance c 1 • ContinuousLinearMap.id ℝ (tangentPlane x) := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℝ
  intro v
  have h := actual_inner_covariance_gram (intrinsicGamma c x) v w
  simp only [intrinsicGamma_inner, unpack_euclideanDisorder] at h
  have hv : inner ℝ (v : Vector N) x = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.2
  rw [tangent_gradient_covariance hN c hc x v w hx hv] at h
  rw [← h]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply,
    Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_right]

/-- Center-overlap tangent covariance, with the manuscript normalization. -/
theorem center_intrinsicGamma_gram {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    GaussianRegression.gram (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) x) =
      (Q * μ.xi1 Q) • ContinuousLinearMap.id ℝ (tangentPlane x) := by
  rw [intrinsicGamma_gram hN _
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ) x hx,
    firstCovariance_center, firstCovariance_mixture]

/-- The true full tangent gradient is nondegenerate for positive overlap. -/
theorem center_intrinsicGamma_surjective {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    Surjective (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) x) := by
  apply surjective_of_gram_det_ne_zero
  rw [center_intrinsicGamma_gram hN μ hQ.le x hx]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    LinearMap.det_smul, ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]
  exact pow_ne_zero _ (mul_pos hQ (mixture_xi1_pos μ hQ)).ne'

/-- Dimension of the complete tangent plane at any actual sphere point. -/
theorem tangentPlane_finrank {n : ℕ} (x : Vector (n + 1))
    (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) : Module.finrank ℝ (tangentPlane x) = n := by
  have hne : x ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by norm_num)] at hx
    have hpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    linarith
  let : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) := ⟨by simp⟩
  exact Submodule.finrank_orthogonal_span_singleton hne

/-- Exact pointwise pdf at intrinsic gradient zero. For Q>0 it is the actual
Gaussian observation density relative to tangent-plane Euclidean volume. -/
theorem center_intrinsic_pdf_zero {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector (n + 1)) (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) :
    GaussianRegression.observationPdf
      (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) x) 0 =
      ENNReal.ofReal (GaussianDensity.normalizer (EuclideanSpace ℝ (Fin n)) /
        Real.sqrt ((Q * μ.xi1 Q) ^ n)) := by
  rw [GaussianRegression.observationPdf_zero,
    center_intrinsicGamma_gram (by omega) μ hQ x hx]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    LinearMap.det_smul, ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one,
    tangentPlane_finrank x hx]
  simp only [GaussianDensity.normalizer, tangentPlane_finrank x hx, finrank_euclideanSpace,
    Fintype.card_fin]

/-- Full Borel disintegration at the complete actual intrinsic gradient,
retaining every original disorder coordinate. -/
theorem intrinsic_whole_field_disintegration {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ))
    (phi : tangentPlane x × Disorder N μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let A := intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) x
    (∫⁻ J, phi (actualObservation A J, J) ∂disorderLaw N μ.maxDegree) =
      ∫⁻ w, ∫⁻ J, phi (w, J) ∂coefficientKernel A w
        ∂GaussianRegression.observationLaw A :=
  actual_disintegration _ (center_intrinsicGamma_surjective hN μ hQ x hx) phi hphi

/-- The canonical whole-coefficient zero kernel is supported on actual
intrinsic critical fields at this specified sphere point. -/
theorem intrinsicKernel_critical_ae {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂coefficientKernel (intrinsicGamma c x) 0,
      surfaceGradient (field c J) x = 0 := by
  dsimp only
  filter_upwards [coefficientKernel_observation_ae _
    (center_intrinsicGamma_surjective hN μ hQ x hx) 0] with J hJ
  have h := congrArg (fun v : tangentPlane x => (v : Vector N)) hJ
  simpa only [actualObservation, intrinsicGamma_coe hN.ne' _ x hx,
    unpack_euclideanDisorder, Submodule.coe_zero] using h

/-- The zero-target conditional law depends only on the genuine observation
kernel. This equality holds at the specified null target, not merely a.e. -/
theorem coefficientKernel_zero_eq_of_ker_eq {N P : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    (A : EuclideanDisorder N P →L[ℝ] F) (B : EuclideanDisorder N P →L[ℝ] G)
    (hA : Surjective A) (hB : Surjective B) (hker : A.ker = B.ker) :
    coefficientKernel A 0 = coefficientKernel B 0 := by
  rw [coefficientKernel_apply, coefficientKernel_apply,
    GaussianRegression.regressionKernel_apply, GaussianRegression.regressionKernel_apply]
  simp only [map_zero, add_zero]
  rw [GaussianRegression.residual_eq_starProjection A hA,
    GaussianRegression.residual_eq_starProjection B hB]
  simp only [hker]

/-- The actual chart gradient is the adjoint of its genuine tangent equivalence
applied to the actual complete intrinsic gradient. -/
theorem chartGamma_eq_adjoint_intrinsic {n P : ℕ} (c : Degree P → ℝ)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    chartGamma n c u =
      (chartTangentEquiv u hu : EuclideanSpace ℝ (Fin n) →L[ℝ]
        tangentPlane (manuscriptChart n u)).adjoint.comp
          (intrinsicGamma c (manuscriptChart n u)) := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ v (chartGamma n c u g) =
    inner ℝ (chartTangentEquiv u hu v : Vector (n + 1))
      (intrinsicGamma c (manuscriptChart n u) g : Vector (n + 1))
  rw [intrinsicGamma_coe (by omega) c _ (manuscriptChart_norm_sq hu),
    chartTangentEquiv_coe, chartGamma_eq_adjoint_surfaceGradient c g hu,
    ContinuousLinearMap.adjoint_inner_right, (manuscriptChart_hasFDerivAt hu).fderiv]

/-- Adjoint injectivity is derived from the full tangent equivalence. -/
theorem adjoint_equiv_injective {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] F) : Injective (e : E →L[ℝ] F).adjoint := by
  intro v w h
  apply ext_inner_left ℝ
  intro z
  obtain ⟨u, rfl⟩ := e.surjective z
  change inner ℝ ((e : E →L[ℝ] F) u) v = inner ℝ ((e : E →L[ℝ] F) u) w
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_right, h]

/-- Chart and intrinsic observations have exactly the same zero fiber. -/
theorem chartGamma_ker_eq {n P : ℕ} (c : Degree P → ℝ)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    (chartGamma n c u).ker = (intrinsicGamma c (manuscriptChart n u)).ker := by
  apply Submodule.ext
  intro g
  change chartGamma n c u g = 0 ↔ intrinsicGamma c (manuscriptChart n u) g = 0
  rw [chartGamma_eq_adjoint_intrinsic c hu]
  change (chartTangentEquiv u hu : EuclideanSpace ℝ (Fin n) →L[ℝ]
    tangentPlane (manuscriptChart n u)).adjoint
      (intrinsicGamma c (manuscriptChart n u) g) = 0 ↔ _
  constructor
  · intro hz
    apply adjoint_equiv_injective (chartTangentEquiv u hu)
    simpa only [map_zero] using hz
  · intro hz
    rw [hz, map_zero]

/-- Literal-zero conditioning of all original tensor coefficients is coordinate
independent under the actual chart/tangent identification. -/
theorem chart_coefficientKernel_zero_eq {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    coefficientKernel (chartGamma n c u) 0 =
      coefficientKernel (intrinsicGamma c (manuscriptChart n u)) 0 := by
  dsimp only
  apply coefficientKernel_zero_eq_of_ker_eq
  · exact center_chartGamma_surjective n μ hQ hu
  · exact center_intrinsicGamma_surjective (by omega) μ hQ _ (manuscriptChart_norm_sq hu)
  · exact chartGamma_ker_eq _ hu

end
end SlowEquilibration.IntrinsicGradientRegression
