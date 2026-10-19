-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCountIntegral
public import SlowEquilibration.RoundSphereChartIntegral

@[expose] public section

/-! Exact normalized-score intensity of the actual affine-latitude critical
point count, including the genuine round sphere area and gradient density. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.GaussianRegression
open SlowEquilibration.SphericalSequentialRegression SlowEquilibration.SphereHessian
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphericalKacRiceGluing SlowEquilibration.RoundSphereChartIntegral
open scoped Topology ENNReal RealInnerProductSpace
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitudeDeterminantMean_measurable (n : ℕ) (v q : ℝ) :
    Measurable (latitudeDeterminantMean n v q) := by
  have hm : Measurable (fun p : ℝ × Matrix (Fin n) (Fin n) ℝ =>
      ENNReal.ofReal |((latitudeScale n q)^2 • p.2-
        (p.1/((n+1 : ℕ) : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ )).det|) := by
    have hmat : Continuous (fun p : ℝ × Matrix (Fin n) (Fin n) ℝ =>
        (latitudeScale n q)^2 • p.2-(p.1/((n+1 : ℕ) : ℝ)) •
          (1 : Matrix (Fin n) (Fin n) ℝ)) :=
      by
        apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        change Continuous (fun p : ℝ × Matrix (Fin n) (Fin n) ℝ =>
          (latitudeScale n q)^2*p.2 i j-(p.1/((n+1 : ℕ) : ℝ))*(1 : Matrix (Fin n) (Fin n) ℝ) i j)
        fun_prop
    exact hmat.matrix_det.abs.measurable.ennreal_ofReal
  exact hm.lintegral_prod_right' (ν := goeLaw n (n+2) v)

theorem latitude_score_lintegral_normalize {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (hf : Measurable f) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ b, f b ∂observationLaw (latitudeScoreCLM c w e q y)) =
      ∫⁻ b, latitudePhysicalScorePdf n c q b*f (((n+2 : ℕ) : ℝ) • b) := by
  dsimp only
  rw [lintegral_observationLaw_rescale _ ((n+2 : ℕ) : ℝ) (by positivity) f hf,
    observationLaw_eq_explicit_density _ (scaled_observation_surjective _
      (center_latitudeScoreCLM_surjective μ hQ w hw e he hq0 hq1 y hy) ((n+2 : ℕ) : ℝ) (by positivity))]
  have hm : Measurable (fun b : EuclideanSpace ℝ (Fin 2) => f (((n+2 : ℕ) : ℝ) • b)) :=
    hf.comp (by fun_prop)
  apply (lintegral_withDensity_eq_lintegral_mul volume (observationPdf_measurable _) hm).trans
  apply lintegral_congr
  intro b
  dsimp only [Pi.mul_apply]
  rw [normalized_latitudeScorePdf_eq μ hQ w hw e he hq0 hq1 y hy b]

def latitudeGradientDensity {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (GaussianDensity.normalizer (EuclideanSpace ℝ (Fin n)) /
    Real.sqrt (((latitudeScale n q)^2*firstCovariance c 1)^n))

theorem latitude_chart_density_metric_cancel {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hfirst : 0 < firstCovariance c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| < 1) {u : Vector n} (hu : ‖u‖ < 2) :
    observationPdf (affineChartGamma c w e q u) 0 * ENNReal.ofReal (manuscriptChartGram n u).det =
      latitudeGradientDensity n c q * ENNReal.ofReal (Real.sqrt (manuscriptChartGram n u).det) := by
  rw [observationPdf_zero, affineChart_gram_det c hc w hw e he hq.le hu]
  have hs : 0 < latitudeScale n q := by
    apply Real.sqrt_pos.mpr
    have ht : 0 < 1-q^2 := by nlinarith [(abs_lt.mp hq).1, (abs_lt.mp hq).2]
    exact mul_pos (div_pos (by positivity) (by positivity)) ht
  have ha : 0 < ((latitudeScale n q)^2*firstCovariance c 1)^n :=
    pow_pos (mul_pos (sq_pos_of_pos hs) hfirst) n
  have hd := manuscriptChartGram_det_pos hu
  have hsa := Real.sqrt_pos.mpr ha
  have hsd := Real.sqrt_pos.mpr hd
  unfold latitudeGradientDensity
  rw [← ENNReal.ofReal_mul (div_nonneg GaussianDensity.normalizer_pos.le (Real.sqrt_nonneg _)),
    ← ENNReal.ofReal_mul (div_nonneg GaussianDensity.normalizer_pos.le (Real.sqrt_nonneg _))]
  congr 1
  rw [Real.sqrt_mul ha.le]
  field_simp
  rw [Real.sq_sqrt hd.le]

/-- True normalized value and section-radial derivative of the original
random tensor field at a latitude point. -/
def actualLatitudeScore {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (J : Disorder (n+2) P) (y : Vector (n+1)) : EuclideanSpace ℝ (Fin 2) :=
  (((n+2 : ℕ) : ℝ)⁻¹) • latitudeScoreCLM c w e q y (euclideanDisorder J)

/-- Exact marked critical count intensity. The score density, determinant
mean and geometric prefactor all arise from the literal affine tensor field. -/
theorem actual_latitude_normalized_count_intensity {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (hf : Measurable f) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualLatitudeSphereCount c w e q (fun J y => f (actualLatitudeScore c w e q J y)) J
        ∂disorderLaw (n+2) μ.maxDegree) =
      latitudeGradientDensity n c q * manuscriptRoundVolume n univ *
        ∫⁻ b, latitudePhysicalScorePdf n c q b *
          latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (((n+2 : ℕ) : ℝ)*b 1) * f b := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let g : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun b => f ((((n+2 : ℕ) : ℝ)⁻¹) • b)
  have hg : Measurable g := hf.comp (by fun_prop)
  let I := ∫⁻ b, latitudePhysicalScorePdf n c q b *
    latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (((n+2 : ℕ) : ℝ)*b 1)*f b
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hfirst : 0 < firstCovariance c 1 := by
    rw [firstCovariance_center, firstCovariance_mixture]
    exact mul_pos hQ (mixture_xi1_pos μ hQ)
  have hM : Measurable (fun b : EuclideanSpace ℝ (Fin 2) =>
      latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (b 1)*g b) :=
    ((latitudeDeterminantMean_measurable _ _ _).comp (by fun_prop)).mul hg
  have hnorm (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
      (∫⁻ b, latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (b 1)*g b
        ∂observationLaw (latitudeScoreCLM c w e q y))=I := by
    rw [latitude_score_lintegral_normalize μ hQ w hw e he hq0 hq1 y hy _ hM]
    apply lintegral_congr
    intro b
    have hN : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [g, PiLp.smul_apply, smul_eq_mul, smul_smul, inv_mul_cancel₀ hN, one_smul]
    exact (mul_assoc _ _ _).symm
  have hk := actual_latitude_score_marked_count_integral hn μ hQ w hw e he hq0 hq1 g hg
  change _ = latitudeGradientDensity n c q * manuscriptRoundVolume n univ * I
  calc
    _ = ∫⁻ u in ball 0 2, latitudeGradientDensity n c q *
        ENNReal.ofReal (Real.sqrt (manuscriptChartGram n u).det) * I := by
      apply hk.trans
      apply setLIntegral_congr_fun isOpen_ball.measurableSet
      intro u hu
      have huu : ‖u‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hu
      change observationPdf (affineChartGamma c w e q u) 0 *
        ENNReal.ofReal (manuscriptChartGram n u).det *
          (∫⁻ b, latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (b 1)*g b
            ∂observationLaw (latitudeScoreCLM c w e q (manuscriptChart n u))) = _
      rw [latitude_chart_density_metric_cancel c hc hfirst w hw e he hq1 huu,
        hnorm _ (manuscriptChart_norm_sq huu)]
    _ = _ := by
      simp_rw [mul_assoc]
      rw [lintegral_const_mul' _ _ (show latitudeGradientDensity n c q ≠ ⊤ from ENNReal.ofReal_ne_top)]
      have hr := manuscriptRoundVolume_lintegral_chart n (fun _ => I)
      rw [manuscriptRoundVolume_restrict_full_chart n hn, lintegral_const] at hr
      rw [← hr]
      ac_rfl

end
end SlowEquilibration.SphericalLatitudeChartKacRice
