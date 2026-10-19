-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeActualKacRice
public import SlowEquilibration.SphereHessian

@[expose] public section

/-! The actual intrinsic Hessian of the affine latitude field inside its
genuine full-tensor conditional Kac--Rice law. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Metric InnerProductSpace
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalChartKacRice SlowEquilibration.SphereChartVolume
open SlowEquilibration.WholeFieldRegression SlowEquilibration.GaussianLocalCoordinates
open SlowEquilibration.SphericalForm SlowEquilibration.SphericalChartGeometry
open SlowEquilibration.SphereHessian
open scoped Topology ENNReal RealInnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitudeField_gradient_contDiff {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+2) P)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) :
    ContDiff ℝ ⊤ (gradient (latitudeField c J w e q)) := by
  have hd := (latitudeField_contDiff c J w e q).fderiv_right (m := ⊤) (by simp)
  exact (InnerProductSpace.toDual ℝ (Vector (n+1))).symm.contDiff.comp hd

theorem latitudeField_surfaceGradient_contDiff {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) :
    ContDiff ℝ ⊤ (surfaceGradient (latitudeField c J w e q)) := by
  rw [surfaceGradient_eq]
  have hg := latitudeField_gradient_contDiff c J w e q
  exact hg.sub (((contDiff_id.inner ℝ hg).div_const ((n+1 : ℕ) : ℝ)).smul contDiff_id)

theorem affineChartGamma_eq_adjoint_surfaceGradient {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (g : EuclideanDisorder (n+2) P) {u : Vector n} (hu : ‖u‖ < 2) :
    affineChartGamma c w e q u g = (fderiv ℝ (manuscriptChart n) u).adjoint
      (surfaceGradient (latitudeField c (unpackDisorder g) w e q) (manuscriptChart n u)) := by
  apply ext_inner_left ℝ
  intro v
  rw [affineChartGamma_directional_derivative c w e q hu,
    ContinuousLinearMap.adjoint_inner_right, (manuscriptChart_hasFDerivAt hu).fderiv,
    real_inner_comm, inner_surfaceGradient, projection_chartDerivative hu]
  have hd := ((latitudeField_contDiff c (unpackDisorder g) w e q).differentiable (by simp)
    (manuscriptChart n u)).hasFDerivAt.comp u (manuscriptChart_hasFDerivAt hu)
  exact congrArg (fun L : Vector n →L[ℝ] ℝ => L v) hd.fderiv

/-- The actual latitude chart Hessian is the ordinary pullback of its true
intrinsic Hessian at every actual critical point. -/
theorem actualLatitudeChartHessian_eq_pullback {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    {u : Vector n} (hu : ‖u‖ < 2)
    (hcrit : surfaceGradient (latitudeField c J w e q) (manuscriptChart n u)=0) :
    actualLatitudeChartHessian c w e q J u = pullback (chartTangentEquiv u hu)
      (intrinsicHessian (latitudeField c J w e q) (manuscriptChart n u)) := by
  have hfd := ((manuscriptChart_contDiffOn n).fderiv_of_isOpen isOpen_ball
    (m := 1) (by simp)).contDiffAt (isOpen_ball.mem_nhds (by simpa using hu))
  have hA := (ContinuousLinearMap.adjoint :
    (Vector n →L[ℝ] Vector (n+1)) ≃ₗᵢ[ℝ] (Vector (n+1) →L[ℝ] Vector n)).hasFDerivAt.comp u
        hfd.differentiableAt_one.hasFDerivAt
  have hG := ((latitudeField_surfaceGradient_contDiff c J w e q).differentiable (by simp)
    (manuscriptChart n u)).hasFDerivAt.comp u (manuscriptChart_hasFDerivAt hu)
  have heq : (fun y => affineChartGamma c w e q y (euclideanDisorder J)) =ᶠ[𝓝 u]
      (fun y => (fderiv ℝ (manuscriptChart n) y).adjoint
        (surfaceGradient (latitudeField c J w e q) (manuscriptChart n y))) := by
    filter_upwards [isOpen_ball.mem_nhds (by simpa using hu : u ∈ ball 0 2)] with y hy
    simpa only [unpack_euclideanDisorder] using
      affineChartGamma_eq_adjoint_surfaceGradient c w e q (euclideanDisorder J) (by simpa using hy)
  have hd := hA.clm_apply hG
  simp only [Function.comp_def] at hd
  unfold actualLatitudeChartHessian spatialJacobian
  rw [heq.fderiv_eq, hd.fderiv]
  simp only [hcrit, map_zero, add_zero, (manuscriptChart_hasFDerivAt hu).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    pullback, intrinsicHessian]
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem actualLatitudeChartHessian_det {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    {u : Vector n} (hu : ‖u‖ < 2)
    (hcrit : surfaceGradient (latitudeField c J w e q) (manuscriptChart n u)=0) :
    (actualLatitudeChartHessian c w e q J u).det = (manuscriptChartGram n u).det *
      (intrinsicHessian (latitudeField c J w e q) (manuscriptChart n u)).det := by
  rw [actualLatitudeChartHessian_eq_pullback c J w e q hu hcrit,
    pullback_det, chartTangentEquiv_gram_det hu]

theorem latitude_coefficientKernel_critical_ae {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hfirst : 0 < firstCovariance c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| < 1) {u : Vector n} (hu : ‖u‖ < 2) :
    ∀ᵐ J ∂coefficientKernel (affineChartGamma c w e q u) 0,
      surfaceGradient (latitudeField c J w e q) (manuscriptChart n u)=0 := by
  filter_upwards [coefficientKernel_observation_ae (affineChartGamma c w e q u)
    (affineChartGamma_surjective c hc hfirst w hw e he hq hu) 0] with J hJ
  have hh := (affineChartGamma_zero_iff_intrinsic c w e q hu (euclideanDisorder J)).mp hJ
  simpa only [unpack_euclideanDisorder] using hh

theorem conditional_latitudeChartHessian_integral {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hfirst : 0 < firstCovariance c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| < 1) {u : Vector n} (hu : ‖u‖ < 2)
    (psi : Disorder (n+2) P → ℝ≥0∞) :
    (∫⁻ J, ENNReal.ofReal |(actualLatitudeChartHessian c w e q J u).det| * psi J
      ∂coefficientKernel (affineChartGamma c w e q u) 0) =
      ENNReal.ofReal (manuscriptChartGram n u).det *
        ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) (manuscriptChart n u)).det| * psi J
          ∂coefficientKernel (affineChartGamma c w e q u) 0 := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [latitude_coefficientKernel_critical_ae c hc hfirst w hw e he hq hu] with J hJ
  rw [actualLatitudeChartHessian_det c J w e q hu hJ, abs_mul,
    abs_of_pos (manuscriptChartGram_det_pos hu),
    ENNReal.ofReal_mul (manuscriptChartGram_det_pos hu).le, mul_assoc]

/-- Actual affine-latitude marked chart Kac--Rice with the literal intrinsic
Hessian under the original full-tensor conditional law. -/
theorem actual_tensor_latitude_intrinsic_kacRice {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hfirst : 0 < firstCovariance c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| < 1)
    (psi : Disorder (n+2) P → Vector n → ℝ≥0∞)
    (hpsi : Measurable fun z : Disorder (n+2) P × Vector n => psi z.1 z.2) :
    AEMeasurable (actualLatitudeChartCount c w e q psi) (disorderLaw (n+2) P) ∧
    (∫⁻ J, actualLatitudeChartCount c w e q psi J ∂disorderLaw (n+2) P) =
      ∫⁻ u in ball 0 2, GaussianRegression.observationPdf (affineChartGamma c w e q u) 0 *
        ENNReal.ofReal (manuscriptChartGram n u).det *
          ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) (manuscriptChart n u)).det| * psi J u
            ∂coefficientKernel (affineChartGamma c w e q u) 0 := by
  have hk := actual_tensor_latitude_chart_kacRice c hc hfirst w hw e he hq psi hpsi
  refine ⟨hk.1, hk.2.trans ?_⟩
  apply setLIntegral_congr_fun isOpen_ball.measurableSet
  intro u hu
  dsimp only
  rw [conditional_latitudeChartHessian_integral c hc hfirst w hw e he hq (by simpa using hu)]
  exact (mul_assoc _ _ _).symm

end
end SlowEquilibration.SphericalLatitudeChartKacRice
