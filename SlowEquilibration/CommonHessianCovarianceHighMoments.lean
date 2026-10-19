-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianOperatorHighMoments
public import SlowEquilibration.GaussianCovarianceQuadraticVariance

/-! Dimension-sharp ordinary high moments under the actual bounded-
covariance Gaussian law, including singular Gaussian laws. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianCovarianceRepresentation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The true centered quadratic form has every real moment at the sharp
scale `σ² L sqrt(dim E)`. Covariance bounds, rather than a supplied moment
estimate, are the only Gaussian input. -/
theorem centered_gaussian_quadratic_high_moment (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x,x ∂μ=0) {σ L : ℝ} (hσ : 0 < σ) (hL : 0 < L)
    (hcov : ∀ x:E,covarianceBilin μ x x ≤ σ^2*‖x‖^2)
    (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric) (hSL : ‖S‖ ≤ L)
    (hm : 0 < Module.finrank ℝ E) (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x:E=>|inner ℝ x (S x)-(∫ y,inner ℝ y (S y) ∂μ)|^q) μ ∧
      (∫ x:E,|inner ℝ x (S x)-(∫ y,inner ℝ y (S y) ∂μ)|^q ∂μ) ≤
        quadraticMomentConstant q*(quadraticFluctuationScale (Module.finrank ℝ E) (σ^2*L))^q := by
  obtain ⟨W,hW,hLaw⟩:=exists_fixed_bounded_gaussian_realization μ hmean hσ.le hcov
  have hstd : SYK.standardGaussianMeasureOnEuclidean (Fin (Module.finrank ℝ E))=
      stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := map_pi_eq_stdGaussian
  rw [hstd] at hLaw
  let T:=W.adjoint.comp (S.comp W)
  have hT : T.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (W.adjoint (S (W x))) y=inner ℝ x (W.adjoint (S (W y)))
    rw [W.adjoint_inner_left,W.adjoint_inner_right]
    exact hS (W x) (W y)
  have hTL : ‖T‖ ≤ σ^2*L := by
    calc
      _ ≤ ‖W.adjoint‖*‖S.comp W‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖W‖*(‖S‖*‖W‖) := by
        rw [LinearIsometryEquiv.norm_map]
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ σ*(L*σ) := by gcongr
      _=_ := by ring
  have hDim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))=
      Module.finrank ℝ E := by simp only [finrank_euclideanSpace,Fintype.card_fin]
  have hMoment:=standard_gaussian_quadratic_high_moment T hT
    (show 0 < σ^2*L by positivity) hTL (by rw [hDim];exact hm) q hq
  have hVariance:=standard_gaussian_quadratic_variance T hT
  let c:=quadraticMean T hT
  have heq (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
      inner ℝ (W x) (S (W x))-c=centeredQuadratic T hT x := by
    unfold centeredQuadratic
    change inner ℝ (W x) (S (W x))-c=inner ℝ x (W.adjoint (S (W x)))-c
    rw [W.adjoint_inner_right]
  have hmeas : Measurable (fun x:E=>inner ℝ x (S x)) :=
    (continuous_id.inner S.continuous).measurable
  have hLp : MemLp (fun x:E=>inner ℝ x (S x)-c) 2 μ := by
    rw [← hLaw]
    exact (memLp_map_measure_iff (hmeas.sub_const c).aestronglyMeasurable W.continuous.measurable.aemeasurable).mpr
      (by simpa only [Function.comp_def,heq] using hVariance.1)
  have hLpQ : MemLp (fun x:E=>inner ℝ x (S x)) 2 μ := by
    have hh:=hLp.add (memLp_const c)
    convert hh using 1
    funext x
    exact (sub_add_cancel (inner ℝ x (S x)) c).symm
  have hC : (∫ x,inner ℝ x (S x) ∂μ)=c := by
    have hh : (∫ x,inner ℝ x (S x)-c ∂μ)=0 := by
      rw [← hLaw,integral_map W.continuous.measurable.aemeasurable (hmeas.sub_const c).aestronglyMeasurable]
      simpa only [heq] using hVariance.2.1
    rw [integral_sub (hLpQ.integrable (by norm_num)) (integrable_const c),integral_const] at hh
    simpa only [probReal_univ,one_smul] using sub_eq_zero.mp hh
  have hMeas : Measurable (fun x:E=>|inner ℝ x (S x)-c|^q) :=
    (hmeas.sub_const c).abs.pow_const q
  rw [hC]
  refine ⟨?_,?_⟩
  · rw [←hLaw]
    exact (integrable_map_measure hMeas.aestronglyMeasurable W.continuous.measurable.aemeasurable).mpr
      (by simpa only [Function.comp_def,heq] using hMoment.1)
  · rw [←hLaw,integral_map W.continuous.measurable.aemeasurable hMeas.aestronglyMeasurable]
    simp only [heq]
    simpa only [hDim] using hMoment.2

end
end SlowEquilibration.GaussianQuadraticVariance
