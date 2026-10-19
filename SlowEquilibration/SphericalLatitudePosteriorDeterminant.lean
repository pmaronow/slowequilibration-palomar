-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeSequentialRegression

@[expose] public section

/-! Actual affine-latitude posterior determinant means and their genuine
score-disintegrated expression. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicHessianLaw
open SlowEquilibration.GaussianRegression SlowEquilibration.SphericalSequentialRegression
open SlowEquilibration.SphereHessian SlowEquilibration.SphericalChartGeometry
open SlowEquilibration.SphericalChartKacRice SlowEquilibration.SphereChartVolume
open scoped Topology ENNReal RealInnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine shifted, scaled GOE absolute-determinant expectation in the
actual dimensions of an affine latitude. The radial target is unnormalized. -/
def latitudeDeterminantMean (n : ℕ) (v q k : ℝ) : ℝ≥0∞ :=
  ∫⁻ W, ENNReal.ofReal |((latitudeScale n q)^2 • W-
    (k/((n+1 : ℕ) : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)).det| ∂goeLaw n (n+2) v

theorem latitudeIntrinsicMatrix_det {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (J : Disorder (n+2) P) :
    (latitudeIntrinsicMatrix c w e q y hy J).det=
      (intrinsicHessian (latitudeField c J w e q) y).det := by
  exact LinearMap.det_toMatrix _ _

theorem latitude_intrinsicDet_measurable {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    Measurable (fun J : Disorder (n+2) P =>
      ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) y).det|) := by
  have hm : Continuous (hessianMatrix c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    convert (jetCLM c 2 (latitudeMap w e q y)
      ![latitudeEmbeddedFrame e y hy i, latitudeEmbeddedFrame e y hy j]).continuous using 1
    funext J
    exact (jetCLM_apply _ _ _ _ J).symm
  have hr : Continuous (fun J : Disorder (n+2) P =>
      jet c 1 (latitudeMap w e q y) (fun _ => latitudeRadialVector e q y) J / ((n+1 : ℕ) : ℝ)) := by
    simpa only [jetCLM_apply] using
      (jetCLM c 1 (latitudeMap w e q y) (fun _ => latitudeRadialVector e q y)).continuous.div_const
        ((n+1 : ℕ) : ℝ)
  have h := ((hm.const_smul ((latitudeScale n q)^2)).sub
    (hr.smul (continuous_const (y := (1 : Matrix (Fin n) (Fin n) ℝ))))).matrix_det.abs.measurable.ennreal_ofReal
  convert h using 1
  funext J
  rw [← latitudeIntrinsicMatrix_det c w e q y hy J, latitudeIntrinsicMatrix_eq]
  rfl

/-- Actual full-coefficient posterior determinant mean at every genuine
joint value/radial/zero-gradient target. -/
theorem latitude_posterior_det_mean {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (b : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) y).det|
      ∂coefficientKernel (latitudeJointCLM c w e q y hy) (jointScoreTarget n b)) =
      latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (b 1) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hl := center_latitude_conditioned_intrinsic_hasLaw μ hQ w hw e he hq0 hq1 y hy
    (jointScoreTarget n b)
  have h := hl.lintegral_comp (f := fun W : Matrix (Fin n) (Fin n) ℝ => ENNReal.ofReal |W.det|)
    (by fun_prop)
  simp only [latitudeIntrinsicMatrix_det] at h
  rw [h, lintegral_map (by fun_prop) (by fun_prop)]
  rfl

/-- Score marks are fixed exactly, not only almost everywhere in the target,
under the genuine full-tensor joint conditional law. -/
theorem latitude_posterior_marked_det_mean {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (b : EuclideanSpace ℝ (Fin 2)) (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) y).det| *
      f (latitudeScoreCLM c w e q y (euclideanDisorder J))
      ∂coefficientKernel (latitudeJointCLM c w e q y hy) (jointScoreTarget n b)) =
      latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (b 1)*f b := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have heq : ∀ᵐ J ∂coefficientKernel (latitudeJointCLM c w e q y hy) (jointScoreTarget n b),
      latitudeScoreCLM c w e q y (euclideanDisorder J)=b := by
    filter_upwards [coefficientKernel_observation_ae _
      (center_latitudeJointCLM_surjective μ hQ w hw e he hq0 hq1 y hy) (jointScoreTarget n b)] with J hJ
    apply PiLp.ext
    intro i
    exact congrArg (fun v => v (Sum.inl i)) hJ
  calc
    _ = ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) y).det| * f b
        ∂coefficientKernel (latitudeJointCLM c w e q y hy) (jointScoreTarget n b) := by
      apply lintegral_congr_ae
      filter_upwards [heq] with J hJ
      rw [hJ]
    _ = _ := by
      rw [lintegral_mul_const _ (latitude_intrinsicDet_measurable c w e q y hy),
        latitude_posterior_det_mean μ hQ w hw e he hq0 hq1 y hy b]

/-- The literal chart posterior determinant and score mark are integrated
against the actual two-dimensional score law and actual GOE determinant mean. -/

theorem latitude_chart_marked_det_integral {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    {u : Vector n} (hu : ‖u‖ < 2) (huy : manuscriptChart n u=y)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (hf : Measurable f) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) y).det| *
      f (latitudeScoreCLM c w e q y (euclideanDisorder J))
      ∂coefficientKernel (affineChartGamma c w e q u) 0) =
      ∫⁻ b, latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (b 1)*f b
        ∂observationLaw (latitudeScoreCLM c w e q y) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hme : Measurable (euclideanDisorder (N := n+2) (P := μ.maxDegree)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate (n+2) μ.maxDegree => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable _ _)
  have hphi : Measurable (fun J : Disorder (n+2) μ.maxDegree =>
      ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) y).det| *
        f (latitudeScoreCLM c w e q y (euclideanDisorder J))) :=
    (latitude_intrinsicDet_measurable c w e q y hy).mul
      (hf.comp ((latitudeScoreCLM c w e q y).continuous.measurable.comp hme))
  have h := latitude_chart_zero_score_disintegration μ hQ w hw e he hq0 hq1 y hy hu huy _ hphi
  exact h.trans (lintegral_congr (fun b =>
    latitude_posterior_marked_det_mean μ hQ w hw e he hq0 hq1 y hy b f))

end
end SlowEquilibration.SphericalLatitudeChartKacRice
