-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCountIntegral

@[expose] public section

/-! The genuine marked affine-sphere Kac--Rice formula preserves a uniform
posterior determinant-weight estimate at arbitrary measurable field marks. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.SphereHessian
open SlowEquilibration.SphericalSequentialRegression SlowEquilibration.GaussianRegression
open SlowEquilibration.SphericalChartGeometry SlowEquilibration.SphereChartVolume
open SlowEquilibration.SphericalChartKacRice
open scoped RealInnerProductSpace ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Comparison of actual critical-point counts, with the full random mark
retained under the actual every-target coefficient posterior. -/
theorem actual_latitude_marked_count_le_score_count {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x,inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (psi : Disorder (n+2) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun z : Disorder (n+2) μ.maxDegree × Vector (n+1) => psi z.1 z.2)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (hf : Measurable f) (L : ℝ)
    (hpost : ∀ (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (b : EuclideanSpace ℝ (Fin 2)),
      let c := centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J,ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) y).det| * psi J y
        ∂coefficientKernel (latitudeJointCLM c w e q y hy) (jointScoreTarget n b))≤
      ENNReal.ofReal L*(latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (b 1)*f b)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J,actualLatitudeSphereCount c w e q psi J ∂disorderLaw (n+2) μ.maxDegree)≤
      ENNReal.ofReal L*(∫⁻ J,actualLatitudeSphereCount c w e q
        (fun J y => f (latitudeScoreCLM c w e q y (euclideanDisorder J))) J
          ∂disorderLaw (n+2) μ.maxDegree) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hfirst : 0<firstCovariance c 1 := by
    rw [firstCovariance_center,firstCovariance_mixture]
    exact mul_pos hQ (mixture_xi1_pos μ hQ)
  rw [(actual_latitude_sphere_marked_kacRice hn c hc hfirst w hw e he hq1 psi hpsi).2,
    actual_latitude_score_marked_count_integral hn μ hQ w hw e he hq0 hq1 f hf,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' isOpen_ball.measurableSet
  intro u hu
  have huu : ‖u‖<2 := by simpa only [mem_ball,dist_zero_right] using hu
  let y := manuscriptChart n u
  have hy : ‖y‖^2=((n+1 : ℕ) : ℝ) := manuscriptChart_norm_sq huu
  have hm : Measurable (fun J : Disorder (n+2) μ.maxDegree =>
      ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) y).det| * psi J y) :=
    (latitude_intrinsicDet_measurable c w e q y hy).mul
      (hpsi.comp (measurable_id.prodMk measurable_const))
  rw [latitude_chart_zero_score_disintegration μ hQ w hw e he hq0 hq1 y hy huu rfl _ hm]
  calc
    _ ≤ _*(∫⁻ b,ENNReal.ofReal L*(latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (b 1)*f b)
        ∂observationLaw (latitudeScoreCLM c w e q y)) := by
      gcongr
      exact hpost y hy _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      ac_rfl

end
end SlowEquilibration.SphericalLatitudeChartKacRice
