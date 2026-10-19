-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphereHessian

/-!
# Intrinsic Hessian in actual chart Kac--Rice

The literal-zero regression kernel is supported on actual critical fields.
Thus the genuine Hessian pullback theorem applies inside the full original
tensor conditional law, for every nonnegative full-field Borel mark.
-/

@[expose] public section

namespace SlowEquilibration.SphericalIntrinsicChartKacRice

open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphericalChartGeometry SlowEquilibration.SphereHessian
open SlowEquilibration.WholeFieldRegression
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

variable {n : ℕ}

/-- Literal-zero conditioning of the full original tensor law is supported
on genuine intrinsic spherical critical points. -/
theorem coefficientKernel_intrinsic_critical_ae (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂coefficientKernel (chartGamma n c u) 0,
      surfaceGradient (field c J) (manuscriptChart n u) = 0 := by
  dsimp only
  filter_upwards [coefficientKernel_observation_ae
    (chartGamma n (centerCoefficients (mixtureCoefficients μ) Q) u)
    (center_chartGamma_surjective n μ hQ hu) 0] with J hJ
  apply (actual_field_chart_critical_iff _ J hu).mp
  have hc := (chartGamma_zero_iff_derivative_zero n _ hu (euclideanDisorder J)).mp hJ
  simpa only [unpack_euclideanDisorder] using hc

/-- The conditional coordinate Hessian determinant is the actual intrinsic
Hessian determinant times the actual chart metric determinant. -/
theorem conditional_chartHessian_integral (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2)
    (psi : Disorder (n + 1) μ.maxDegree → ℝ≥0∞) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(actualChartHessian n c J u).det| * psi J
      ∂coefficientKernel (chartGamma n c u) 0) =
      ENNReal.ofReal (manuscriptChartGram n u).det *
        ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n u)).det| * psi J
          ∂coefficientKernel (chartGamma n c u) 0 := by
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [coefficientKernel_intrinsic_critical_ae n μ hQ hu] with J hJ
  rw [actualChartHessian_det _ J hu hJ, abs_mul,
    abs_of_pos (manuscriptChartGram_det_pos hu),
    ENNReal.ofReal_mul (manuscriptChartGram_det_pos hu).le, mul_assoc]

/-- Full original-tensor marked chart Kac--Rice with the genuine intrinsic
Hessian and the proved actual metric factor. -/
theorem actual_tensor_chart_intrinsic_kacRice (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n + 1) μ.maxDegree → EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n + 1) μ.maxDegree × EuclideanSpace ℝ (Fin n) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualChartCount n c psi) (disorderLaw (n + 1) μ.maxDegree) ∧
    (∫⁻ J, actualChartCount n c psi J ∂disorderLaw (n + 1) μ.maxDegree) =
      ∫⁻ u in ball 0 2, GaussianRegression.observationPdf (chartGamma n c u) 0 *
        ENNReal.ofReal (manuscriptChartGram n u).det *
          ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n u)).det| * psi J u
            ∂coefficientKernel (chartGamma n c u) 0 := by
  have hk := actual_tensor_chart_kacRice n μ hQ psi hpsi
  refine ⟨hk.1, hk.2.trans ?_⟩
  apply setLIntegral_congr_fun isOpen_ball.measurableSet
  intro u hu
  dsimp only
  rw [conditional_chartHessian_integral n μ hQ (u := u) (by simpa using hu)]
  exact (mul_assoc _ _ _).symm

/-- The explicit isotropic intrinsic gradient density at literal zero. -/
def intrinsicGradientDensity (n : ℕ) (μ : FiniteMixture) (Q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (GaussianDensity.normalizer (EuclideanSpace ℝ (Fin n)) /
    Real.sqrt ((Q * μ.xi1 Q) ^ n))

/-- The coordinate density and Hessian metric factors leave precisely the
ordinary Riemannian area density. -/
theorem chart_density_metric_cancel (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    GaussianRegression.observationPdf
      (chartGamma n (centerCoefficients (mixtureCoefficients μ) Q) u) 0 *
        ENNReal.ofReal (manuscriptChartGram n u).det =
      intrinsicGradientDensity n μ Q * ENNReal.ofReal (Real.sqrt (manuscriptChartGram n u).det) := by
  rw [GaussianRegression.observationPdf_zero, center_chart_gram_det n μ hQ.le hu]
  have ha : 0 < (Q * μ.xi1 Q) ^ n := pow_pos (mul_pos hQ (mixture_xi1_pos μ hQ)) n
  have hd := manuscriptChartGram_det_pos hu
  have hsa := Real.sqrt_pos.mpr ha
  have hsd := Real.sqrt_pos.mpr hd
  unfold intrinsicGradientDensity
  rw [← ENNReal.ofReal_mul (div_nonneg GaussianDensity.normalizer_pos.le (Real.sqrt_nonneg _)),
    ← ENNReal.ofReal_mul (div_nonneg GaussianDensity.normalizer_pos.le (Real.sqrt_nonneg _))]
  congr 1
  rw [Real.sqrt_mul ha.le]
  field_simp
  rw [Real.sq_sqrt hd.le]

/-- Actual marked chart Kac--Rice in intrinsic Hessian and ordinary round
area density, with all coordinate metric factors canceled by proof. -/
theorem actual_tensor_chart_round_kacRice (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n + 1) μ.maxDegree → EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n + 1) μ.maxDegree × EuclideanSpace ℝ (Fin n) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualChartCount n c psi) (disorderLaw (n + 1) μ.maxDegree) ∧
    (∫⁻ J, actualChartCount n c psi J ∂disorderLaw (n + 1) μ.maxDegree) =
      ∫⁻ u in ball 0 2, intrinsicGradientDensity n μ Q *
        ENNReal.ofReal (Real.sqrt (manuscriptChartGram n u).det) *
          ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n u)).det| * psi J u
            ∂coefficientKernel (chartGamma n c u) 0 := by
  have hk := actual_tensor_chart_intrinsic_kacRice n μ hQ psi hpsi
  refine ⟨hk.1, hk.2.trans ?_⟩
  apply setLIntegral_congr_fun isOpen_ball.measurableSet
  intro u hu
  dsimp only
  rw [chart_density_metric_cancel n μ hQ (u := u) (by simpa using hu)]

end
end SlowEquilibration.SphericalIntrinsicChartKacRice
