-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudePosteriorDeterminant
public import SlowEquilibration.SphericalLatitudeScoreDensity

@[expose] public section

/-! Literal affine-latitude critical-point counts expressed through their
actual Gaussian score law and actual GOE absolute-determinant expectation. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.GaussianRegression
open SlowEquilibration.SphericalSequentialRegression SlowEquilibration.SphereHessian
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open scoped Topology ENNReal RealInnerProductSpace
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem directionalJet_jointContinuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (fun p : Disorder N P × (Vector N × Vector N) =>
      jet c 1 p.2.1 (fun _ => p.2.2) p.1) := by
  have hc (p : Degree P) (I : SphericalAging.FiniteModel.TensorIndex N p.val.val) :
      Continuous (fun z : Disorder N P × (Vector N × Vector N) =>
        SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative 1 I z.2.1 (fun _ => z.2.2)) := by
    simp only [SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative, iteratedFDeriv_one_apply]
    have hd := ((SphericalAging.HamiltonianDerivativeCovariance.coefficient_contDiff I).fderiv_right
      (m := ⊤) (by simp)).continuous
    exact (hd.comp continuous_snd.fst).clm_apply continuous_snd.snd
  simp_rw [← jetCLM_apply]
  simp only [jetCLM, pureJetCLM, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  fun_prop

theorem latitudeScore_jointContinuous {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) :
    Continuous (fun p : Disorder (n+2) P × Vector (n+1) =>
      latitudeScoreCLM c w e q p.2 (euclideanDisorder p.1)) := by
  change Continuous ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm ∘
    (fun p : Disorder (n+2) P × Vector (n+1) => fun i => latitudeScoreCLM c w e q p.2 (euclideanDisorder p.1) i))
  apply Continuous.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Disorder (n+2) P × Vector (n+1) =>
      latitudeScoreCLM c w e q p.2 (euclideanDisorder p.1) 0)
    simp only [latitudeScoreCLM_apply_zero, unpack_euclideanDisorder, jet, iteratedFDeriv_zero_apply]
    have hp : Continuous (fun p : Disorder (n+2) P × Vector (n+1) =>
        (p.1, latitudeMap w e q p.2)) := by
      unfold latitudeMap
      fun_prop
    exact (field_jointContinuous c).comp hp
  · change Continuous (fun p : Disorder (n+2) P × Vector (n+1) =>
      latitudeScoreCLM c w e q p.2 (euclideanDisorder p.1) 1)
    simp only [latitudeScoreCLM_apply_one, unpack_euclideanDisorder]
    have hp : Continuous (fun p : Disorder (n+2) P × Vector (n+1) =>
        (p.1, (latitudeMap w e q p.2, latitudeRadialVector e q p.2))) := by
      unfold latitudeMap latitudeRadialVector
      fun_prop
    have h := (directionalJet_jointContinuous (N := n+2) c).comp hp
    simpa only [Function.comp_def] using h

/-- Literal expected number (or Borel score-weighted number) of all critical
points of the actual affine field, with an explicit GOE determinant integral.
Neither a Gaussian replacement field nor a conditional-law premise occurs. -/
theorem actual_latitude_score_marked_count_integral {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (hf : Measurable f) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualLatitudeSphereCount c w e q
      (fun J y => f (latitudeScoreCLM c w e q y (euclideanDisorder J))) J
        ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ u in ball 0 2, observationPdf (affineChartGamma c w e q u) 0 *
        ENNReal.ofReal (manuscriptChartGram n u).det *
          ∫⁻ b, latitudeDeterminantMean n (Q^2*μ.xi2 Q) q (b 1)*f b
            ∂observationLaw (latitudeScoreCLM c w e q (manuscriptChart n u)) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hfirst : 0 < firstCovariance c 1 := by
    rw [firstCovariance_center, firstCovariance_mixture]
    exact mul_pos hQ (mixture_xi1_pos μ hQ)
  have hmark := hf.comp (latitudeScore_jointContinuous c w e q).measurable
  have hk := actual_latitude_sphere_marked_kacRice hn c hc hfirst w hw e he hq1
    (fun J y => f (latitudeScoreCLM c w e q y (euclideanDisorder J))) hmark
  apply hk.2.trans
  apply setLIntegral_congr_fun isOpen_ball.measurableSet
  intro u hu
  dsimp only
  congr 1
  have huu : ‖u‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hu
  exact latitude_chart_marked_det_integral μ hQ w hw e he hq0 hq1 _
    (manuscriptChart_norm_sq huu) huu rfl f hf

end
end SlowEquilibration.SphericalLatitudeChartKacRice
