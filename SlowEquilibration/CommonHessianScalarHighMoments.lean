-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianTranslatedQuadraticHighMoments
public import SlowEquilibration.CommonHessianActualCornerMeanSquare

/-! Sharp all-real-q scalar Gaussian moments, and the actual centered
corner under the original coefficient posterior. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianCovarianceRepresentation
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem centered_gaussian_scalar_high_moment (μ:Measure ℝ) [IsGaussian μ]
    (hmean:∫ x,x ∂μ=0) {σ:ℝ} (hσ:0<σ)
    (hcov:∀ x:ℝ,covarianceBilin μ x x ≤ σ^2*‖x‖^2) (q:ℝ) (hq:0 ≤ q) :
    Integrable (fun x:ℝ=>|x|^q) μ ∧
      (∫ x:ℝ,|x|^q ∂μ) ≤ gaussianNormRealMomentConstant q 1 1*σ^q:=by
  obtain ⟨W,hW,hLaw⟩:=exists_fixed_bounded_gaussian_realization μ hmean hσ.le hcov
  have hstd:SYK.standardGaussianMeasureOnEuclidean (Fin (Module.finrank ℝ ℝ))=
      stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ ℝ))):=map_pi_eq_stdGaussian
  rw [hstd] at hLaw
  let P:=stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ ℝ)))
  have hStdCov (g:EuclideanSpace ℝ (Fin (Module.finrank ℝ ℝ))):
      covarianceBilin P g g ≤ (1:ℝ)^2*‖g‖^2:=by
    rw [covarianceBilin_stdGaussian]
    change inner ℝ g g ≤ (1:ℝ)^2*‖g‖^2
    simp only [real_inner_self_eq_norm_sq,one_pow,one_mul]
    exact le_rfl
  have hNormInt:=GaussianVectorPolynomialMoments.centered_gaussian_norm_moments P
    integral_id_stdGaussian (by norm_num : (0:ℝ)<1) hStdCov
    (show (1:ℝ)*Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ ℝ))):ℝ) ≤ 1 by simp)
    (Nat.ceil q)
  have hNorm:=NonnegativeRealMoment.real_moment_of_integer P (fun g=>‖g‖) continuous_norm.measurable
    (fun _=>norm_nonneg _) hq (Nat.ceil q) (Nat.le_ceil q) hNormInt.1
  have hNormBound:(∫ g,‖g‖^q ∂P) ≤ gaussianNormRealMomentConstant q 1 1:=
    hNorm.2.trans (add_le_add le_rfl hNormInt.2)
  have hp (g:EuclideanSpace ℝ (Fin (Module.finrank ℝ ℝ))):|W g|^q ≤ σ^q*‖g‖^q:=by
    have hh:‖W g‖ ≤ σ*‖g‖:=(W.le_opNorm _).trans (mul_le_mul_of_nonneg_right hW (norm_nonneg _))
    have hhq:=Real.rpow_le_rpow (norm_nonneg _) hh hq
    simpa only [Real.norm_eq_abs,Real.mul_rpow hσ.le (norm_nonneg _)] using hhq
  have hWI:Integrable (fun g=>|W g|^q) P:=(hNorm.1.const_mul (σ^q)).mono'
    (W.continuous.measurable.abs.pow_const q).aestronglyMeasurable
    (ae_of_all _ (fun g=>by rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)];exact hp g))
  have hMeas:Measurable (fun x:ℝ=>|x|^q):=measurable_id.abs.pow_const q
  rw [←hLaw]
  refine ⟨(integrable_map_measure hMeas.aestronglyMeasurable W.continuous.measurable.aemeasurable).mpr hWI,?_⟩
  rw [integral_map W.continuous.measurable.aemeasurable hMeas.aestronglyMeasurable]
  have hh:=integral_mono hWI (hNorm.1.const_mul (σ^q)) hp
  rw [integral_const_mul] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hNormBound (by positivity)).trans_eq (by ring))

end
end SlowEquilibration.GaussianQuadraticVariance

namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance GaussianQuadraticVariance
open SphericalConditionalMatrices
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {F:Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The actual centered corner on the original posterior has sharp
N^(-q/2) moments at every target, including singular residual laws. -/
theorem actual_conditional_centered_corner_q_moment {N P:ℕ} (hN:0<N)
    (c:Degree P→ℝ) (hc:∀ p,0 ≤ c p) (hb:0<secondCovariance c 1)
    (x:Vector N) (hx:‖x‖^2=(N:ℝ)) (v:Vector N) (hv:‖v‖=1) (hvtan:inner ℝ v x=0)
    (A:EuclideanDisorder N P→L[ℝ]F) (hA:Surjective A) (w:F) (q:ℝ) (hq:0 ≤ q) :
    Integrable (fun J:Disorder N P=>|actualObservation (cornerCLM c x v) J-cornerCLM c x v (lift A w)|^q)
      (coefficientKernel A w) ∧
    (∫ J,|actualObservation (cornerCLM c x v) J-cornerCLM c x v (lift A w)|^q ∂coefficientKernel A w) ≤
      gaussianNormRealMomentConstant q 1 1*(Real.sqrt (2*secondCovariance c 1/(N:ℝ)))^q:=by
  let μ:=centeredLaw A (cornerCLM c x v)
  let τ:=2*secondCovariance c 1/(N:ℝ)
  have hτ:0<τ:=div_pos (mul_pos (by norm_num) hb) (Nat.cast_pos.mpr hN)
  have hcov (u:ℝ):covarianceBilin μ u u ≤ (Real.sqrt τ)^2*‖u‖^2:=by
    have hh:=centeredLaw_covariance_le_gram A hA (cornerCLM c x v) u
    rw [cornerCLM_gram hN c hc x hx v hv hvtan] at hh
    simpa only [smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,
      real_inner_self_eq_norm_sq,Real.sq_sqrt hτ.le] using hh
  have hMom:=centered_gaussian_scalar_high_moment μ (centeredLaw_mean A _)
    (Real.sqrt_pos.mpr hτ) hcov q hq
  have hLaw:=centered_actualObservation_hasLaw A (cornerCLM c x v) w
  refine ⟨hLaw.integrable_fun_comp hMom.1,?_⟩
  exact (hLaw.integral_comp (measurable_id.abs.pow_const q).aestronglyMeasurable).trans_le hMom.2

end
end SlowEquilibration.SphericalCommonHessianRegression
