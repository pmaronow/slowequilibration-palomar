-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGlobalKacRice
public import SlowEquilibration.WholeFieldRegression
public import SlowEquilibration.RoundSphereVolume

/-!
# Actual mixed tensor field in the genuine round sphere chart

The coordinate gradient is the adjoint derivative of the field's actual
coefficient feature. It is connected to actual first jets, and its covariance
and surjectivity are derived from the actual mixture and chart metric.
-/

@[expose] public section

namespace SlowEquilibration.SphericalChartKacRice

open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphereChartVolume SlowEquilibration.WholeFieldRegression
open SlowEquilibration.GaussianLocalCoordinates
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

variable {n : ℕ}

/-- The exact actual field feature is polynomial and smooth in the ambient point. -/
theorem fieldFeature_contDiff {N P : ℕ} (c : Degree P → ℝ) :
    ContDiff ℝ ⊤ (fieldFeature (N := N) c) := by
  have hp : ContDiff ℝ ⊤ (fun x : Vector N => fun k : Coordinate N P =>
      Real.sqrt (c k.1) * SphericalAging.FiniteModel.normalization N k.1.val.val *
        SphericalAging.FiniteModel.tensorMonomial x k.2) := by
    apply contDiff_pi.mpr
    intro k
    unfold SphericalAging.FiniteModel.tensorMonomial
    fun_prop
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P => ℝ)).symm.contDiff.comp hp

/-- The actual-radius round chart is smooth on its genuine open coordinate domain. -/
theorem manuscriptChart_contDiffOn (n : ℕ) :
    ContDiffOn ℝ ⊤ (manuscriptChart n) (ball 0 2) := by
  exact (((chartAmbientIsometry n).toContinuousLinearEquiv.contDiff.comp_contDiffOn
    sphereChartND_contDiffOn).const_smul (Real.sqrt (n + 1 : ℕ)))

/-- Actual coefficient feature of the manuscript field in the true round chart. -/
def chartFeature {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanDisorder (n + 1) P := fieldFeature c (manuscriptChart n u)

/-- The actual coordinate gradient observation, retaining all tensor coefficients. -/
def chartGamma {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanDisorder (n + 1) P →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (fderiv ℝ (chartFeature n c) u).adjoint

lemma chartFeature_contDiffOn {P : ℕ} (n : ℕ) (c : Degree P → ℝ) :
    ContDiffOn ℝ ⊤ (chartFeature n c) (ball 0 2) :=
  (fieldFeature_contDiff c).comp_contDiffOn (manuscriptChart_contDiffOn n)

/-- C1 regularity of the actual whole-coefficient chart gradient. -/
theorem chartGamma_contDiffOn {P : ℕ} (n : ℕ) (c : Degree P → ℝ) :
    ContDiffOn ℝ 1 (chartGamma n c) (ball 0 2) := by
  have hd := (chartFeature_contDiffOn n c).fderiv_of_isOpen isOpen_ball
    (m := 1) (by simp)
  exact (ContinuousLinearMap.adjoint :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanDisorder (n + 1) P) ≃ₗᵢ[ℝ]
      (EuclideanDisorder (n + 1) P →L[ℝ] EuclideanSpace ℝ (Fin n))).contDiff.comp_contDiffOn hd

/-- The actual chart coordinate field, expressed through its proved coefficient feature. -/
theorem chart_field_feature {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (g : EuclideanDisorder (n + 1) P) :
    (fun u => field c (unpackDisorder g) (manuscriptChart n u)) =
      fun u => inner ℝ g (chartFeature n c u) := by
  funext u
  exact (fieldFeature_inner c g (manuscriptChart n u)).symm

/-- The actual coordinate gradient observation is the actual scalar field
Frechet derivative in every coordinate direction. -/
theorem chartGamma_directional_derivative {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2)
    (g : EuclideanDisorder (n + 1) P) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ v (chartGamma n c u g) =
      fderiv ℝ (fun y => field c (unpackDisorder g) (manuscriptChart n y)) u v := by
  have hd := ((innerSL ℝ g).hasFDerivAt.comp u
    (((chartFeature_contDiffOn n c).contDiffAt (isOpen_ball.mem_nhds (by simpa using hu))).differentiableAt (by simp)).hasFDerivAt)
  have he := hd.fderiv
  simp only [Function.comp_def, innerSL_apply_apply] at he
  rw [chart_field_feature, he]
  simp only [chartGamma, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  exact real_inner_comm _ _

/-- Every actual chart coordinate observation is a first field jet along the
true chart derivative, proved by the field and chart chain rule. -/
theorem chartGamma_apply_jet {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2)
    (g : EuclideanDisorder (n + 1) P) (i : Fin n) :
    chartGamma n c u g i = jet c 1 (manuscriptChart n u)
      (fun _ => manuscriptChartDerivative n u (EuclideanSpace.basisFun (Fin n) ℝ i))
      (unpackDisorder g) := by
  rw [← EuclideanSpace.basisFun_inner, chartGamma_directional_derivative n c hu]
  have hd := ((field_contDiff c (unpackDisorder g)).differentiable (by simp)
    (manuscriptChart n u)).hasFDerivAt.comp u (manuscriptChart_hasFDerivAt hu)
  have he := hd.fderiv
  simp only [Function.comp_def] at he
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, jet, iteratedFDeriv_one_apply]

/-- The true radius chart point belongs to the manuscript sphere. -/
theorem manuscriptChart_norm_sq {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    ‖manuscriptChart n u‖ ^ 2 = (n + 1 : ℕ) := by
  simp only [manuscriptChart, norm_smul, Real.norm_eq_abs, (chartAmbientIsometry n).norm_map,
    sphereChartND_norm hu.le, mul_one, sq_abs]
  exact Real.sq_sqrt (Nat.cast_nonneg _)

/-- All true chart derivative directions are tangent to the actual-radius sphere. -/
theorem manuscriptChartDerivative_tangent {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (manuscriptChartDerivative n u v) (manuscriptChart n u) = 0 := by
  simp only [manuscriptChartDerivative, manuscriptChart, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, real_inner_smul_left, real_inner_smul_right]
  rw [(chartAmbientIsometry n).inner_map_map, real_inner_comm, sphereChartDerivND_orthogonal hu]
  simp

/-- Exact actual chart-gradient covariance, including the genuine round
metric pullback rather than an assumed orthonormal coordinate frame. -/
theorem center_chart_gram_matrix (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (GaussianRegression.gram (chartGamma n (centerCoefficients (mixtureCoefficients μ) Q) u)).toLinearMap =
      (Q * μ.xi1 Q) • manuscriptChartGram n u := by
  classical
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ
  ext i j
  rw [LinearMap.toMatrix_apply]
  change GaussianRegression.gram (chartGamma n c u) (EuclideanSpace.basisFun (Fin n) ℝ j) i = _
  rw [← actual_covariance_gram]
  simp only [actualObservation, chartGamma_apply_jet n c hu, unpack_euclideanDisorder]
  rw [tangent_gradient_covariance (by omega) c hc (manuscriptChart n u)
    _ _ (manuscriptChart_norm_sq hu) (manuscriptChartDerivative_tangent hu _),
    firstCovariance_center, firstCovariance_mixture]
  simp only [manuscriptChartGram, (manuscriptChart_hasFDerivAt hu).fderiv, Matrix.smul_apply, smul_eq_mul]

/-- Exact actual chart observation determinant, with every metric factor present. -/
theorem center_chart_gram_det (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    (GaussianRegression.gram (chartGamma n (centerCoefficients (mixtureCoefficients μ) Q) u)).det =
      (Q * μ.xi1 Q) ^ n * (manuscriptChartGram n u).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    center_chart_gram_matrix n μ hQ hu, Matrix.det_smul]
  simp

/-- The actual round chart metric is positive, as proved from its true derivative Gram determinant. -/
theorem manuscriptChartGram_det_pos {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    0 < (manuscriptChartGram n u).det := by
  apply Real.sqrt_pos.mp
  rw [manuscriptChart_riemannian_density hu]
  have hs := sphereChartScaleND_pos hu
  have hw : 0 < sphereChartWeightND u := by unfold sphereChartWeightND; positivity
  exact mul_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _) hw

/-- Actual chart gradient observations are surjective throughout the genuine
chart domain for every positive-overlap finite mixture. -/
theorem center_chartGamma_surjective (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    Surjective (chartGamma n (centerCoefficients (mixtureCoefficients μ) Q) u) := by
  apply surjective_of_gram_det_ne_zero
  rw [center_chart_gram_det n μ hQ.le hu]
  exact (mul_pos (pow_pos (mul_pos hQ (mixture_xi1_pos μ hQ)) n)
    (manuscriptChartGram_det_pos hu)).ne'

/-- The true gradient-zero predicate equals vanishing of the actual scalar
field's chart Frechet derivative, rather than a surrogate zero condition. -/
theorem chartGamma_zero_iff_derivative_zero {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2)
    (g : EuclideanDisorder (n + 1) P) :
    chartGamma n c u g = 0 ↔
      fderiv ℝ (fun y => field c (unpackDisorder g) (manuscriptChart n y)) u = 0 := by
  constructor
  · intro hzero
    ext v
    rw [← chartGamma_directional_derivative n c hu, hzero, inner_zero_right, zero_apply]
  · intro hzero
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [chartGamma_directional_derivative n c hu, hzero, zero_apply]

/-- Full coefficient Borel marked Kac--Rice for the actual tensor field on
the genuine chart domain, with observation surjectivity proved from the actual mixture. -/
theorem chart_marked_kacRice (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (psi : EuclideanDisorder (n + 1) μ.maxDegree → EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hpsi : Measurable fun p : EuclideanDisorder (n + 1) μ.maxDegree × EuclideanSpace ℝ (Fin n) =>
      psi p.1 p.2) :
    let Gamma := chartGamma n (centerCoefficients (mixtureCoefficients μ) Q)
    AEMeasurable (zeroCount Gamma (ball 0 2) psi) (stdGaussian (EuclideanDisorder (n + 1) μ.maxDegree)) ∧
    (∫⁻ z, zeroCount Gamma (ball 0 2) psi z ∂stdGaussian (EuclideanDisorder (n + 1) μ.maxDegree)) =
      ∫⁻ u in ball 0 2, GaussianRegression.observationPdf (Gamma u) 0 *
        ∫⁻ z, ENNReal.ofReal |(spatialJacobian Gamma z u).det| * psi z u
          ∂GaussianRegression.regressionKernel (Gamma u) 0 := by
  exact marked_kacRice _ _ isOpen_ball (chartGamma_contDiffOn _ _)
    (fun u hu => center_chartGamma_surjective n μ hQ (by simpa using hu)) psi hpsi

/-- The full actual tensor mark in chart coordinates is counted at precisely
the critical points of its genuine scalar chart field. -/
def actualChartCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (psi : Disorder (n + 1) P → EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (J : Disorder (n + 1) P) : ℝ≥0∞ :=
  ∑' u : {u : EuclideanSpace ℝ (Fin n) | u ∈ ball 0 2 ∧
    fderiv ℝ (fun y => field c J (manuscriptChart n y)) u = 0}, psi J u

/-- Actual coordinate Hessian of the gradient of the actual scalar chart field. -/
def actualChartHessian {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n + 1) P) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  spatialJacobian (chartGamma n c) (euclideanDisorder J) u

lemma actualChartCount_eq_zeroCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (psi : Disorder (n + 1) P → EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (J : Disorder (n + 1) P) :
    actualChartCount n c psi J = zeroCount (chartGamma n c) (ball 0 2)
      (fun z u => psi (unpackDisorder z) u) (euclideanDisorder J) := by
  classical
  have he : {u : EuclideanSpace ℝ (Fin n) | u ∈ ball 0 2 ∧
      chartGamma n c u (euclideanDisorder J) = 0} =
      {u : EuclideanSpace ℝ (Fin n) | u ∈ ball 0 2 ∧
        fderiv ℝ (fun y => field c J (manuscriptChart n y)) u = 0} := by
    ext u
    exact and_congr_right (fun hu => by
      simpa only [unpack_euclideanDisorder] using
        chartGamma_zero_iff_derivative_zero n c (by simpa using hu) (euclideanDisorder J))
  unfold actualChartCount zeroCount
  rw [he]
  simp only [unpack_euclideanDisorder]

/-- Genuine full-tensor law chart Kac--Rice, for arbitrary full-field Borel
marks at literal chart-gradient zero, using the actual tensor disorder law. -/
theorem actual_tensor_chart_kacRice (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n + 1) μ.maxDegree → EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n + 1) μ.maxDegree × EuclideanSpace ℝ (Fin n) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualChartCount n c psi) (disorderLaw (n + 1) μ.maxDegree) ∧
    (∫⁻ J, actualChartCount n c psi J ∂disorderLaw (n + 1) μ.maxDegree) =
      ∫⁻ u in ball 0 2, GaussianRegression.observationPdf (chartGamma n c u) 0 *
        ∫⁻ J, ENNReal.ofReal |(actualChartHessian n c J u).det| * psi J u
          ∂coefficientKernel (chartGamma n c u) 0 := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let psiE := fun z : EuclideanDisorder (n + 1) μ.maxDegree => fun u => psi (unpackDisorder z) u
  have hm : Measurable fun p : EuclideanDisorder (n + 1) μ.maxDegree × EuclideanSpace ℝ (Fin n) =>
      psiE p.1 p.2 := hpsi.comp
    (((unpackCLM (n + 1) μ.maxDegree).continuous.measurable.comp measurable_fst).prodMk measurable_snd)
  have hk := chart_marked_kacRice n μ hQ psiE hm
  have hlaw := actual_flattened_gaussian (n + 1) μ.maxDegree
  have he := funext fun J => actualChartCount_eq_zeroCount n c psi J
  have hMap : AEMeasurable (zeroCount (chartGamma n c) (ball 0 2) psiE)
      ((disorderLaw (n + 1) μ.maxDegree).map euclideanDisorder) := by
    rw [hlaw.map_eq]
    exact hk.1
  have hAE := hMap.comp_aemeasurable' hlaw.aemeasurable
  refine ⟨?_, ?_⟩
  · change AEMeasurable (actualChartCount n c psi) (disorderLaw (n + 1) μ.maxDegree)
    rw [he]
    exact hAE
  · rw [he, hlaw.lintegral_comp hk.1, hk.2]
    apply setLIntegral_congr_fun isOpen_ball.measurableSet
    intro u hu
    dsimp only
    congr 1
    rw [coefficientKernel_apply]
    have hmark : Measurable (fun J : Disorder (n + 1) μ.maxDegree =>
        ENNReal.ofReal |(actualChartHessian n c J u).det| * psi J u) := by
      have h := spatial_mark_measurable (chartGamma n c) u
        (((chartGamma_contDiffOn n c).contDiffAt (isOpen_ball.mem_nhds hu)).differentiableAt_one)
        psiE hm
      have hg : Measurable (euclideanDisorder (N := n + 1) (P := μ.maxDegree)) :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate (n + 1) μ.maxDegree => ℝ)).symm.continuous.measurable.comp
          (flatDisorder_measurable _ _)
      simpa only [actualChartHessian, Function.comp_def, psiE, unpack_euclideanDisorder] using h.comp hg
    rw [lintegral_map hmark (unpackCLM (n + 1) μ.maxDegree).continuous.measurable]
    rfl

end
end SlowEquilibration.SphericalChartKacRice
