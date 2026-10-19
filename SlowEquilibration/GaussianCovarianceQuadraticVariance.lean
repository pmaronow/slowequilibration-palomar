-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuadraticVariance
public import SlowEquilibration.GaussianCovarianceRepresentation

/-! Actual quadratic-form variance for every centered finite Gaussian law
with bounded covariance, including singular laws and fixed target dimension. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianCovarianceRepresentation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The actual ordinary centered second moment is controlled by the
covariance norm on the object's own target space, without an ambient
coefficient dimension factor or a supplied quadratic variance estimate. -/
theorem centered_gaussian_quadratic_variance (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x,x ∂μ=0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcov : ∀ x : E,covarianceBilin μ x x ≤ σ^2*‖x‖^2)
    (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric) :
    MemLp (fun x:E=>inner ℝ x (S x)) 2 μ ∧
      (∫ x,(inner ℝ x (S x)-(∫ y,inner ℝ y (S y) ∂μ))^2 ∂μ) ≤
        2*(Module.finrank ℝ E:ℝ)*σ^4*‖S‖^2 := by
  obtain ⟨W,hW,hLaw⟩:=exists_fixed_bounded_gaussian_realization μ hmean hσ hcov
  have hstd : SYK.standardGaussianMeasureOnEuclidean (Fin (Module.finrank ℝ E))=
      stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := map_pi_eq_stdGaussian
  rw [hstd] at hLaw
  let T:=W.adjoint.comp (S.comp W)
  have hT : T.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (W.adjoint (S (W x))) y=inner ℝ x (W.adjoint (S (W y)))
    rw [W.adjoint_inner_left,W.adjoint_inner_right]
    exact hS (W x) (W y)
  have h:=standard_gaussian_quadratic_variance T hT
  let c:=quadraticMean T hT
  have heq (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
      inner ℝ (W x) (S (W x))-c=centeredQuadratic T hT x := by
    unfold centeredQuadratic
    change inner ℝ (W x) (S (W x))-c=inner ℝ x (W.adjoint (S (W x)))-c
    rw [W.adjoint_inner_right]
  have hmeas : Measurable (fun x:E=>inner ℝ x (S x)) := (continuous_id.inner S.continuous).measurable
  have hLp : MemLp (fun x:E=>inner ℝ x (S x)-c) 2 μ := by
    rw [← hLaw]
    exact (memLp_map_measure_iff (hmeas.sub_const c).aestronglyMeasurable W.continuous.measurable.aemeasurable).mpr
      (by simpa only [Function.comp_def,heq] using h.1)
  have hLpQ : MemLp (fun x:E=>inner ℝ x (S x)) 2 μ := by
    have hh:=hLp.add (memLp_const c)
    convert hh using 1
    funext x
    exact (sub_add_cancel (inner ℝ x (S x)) c).symm
  have hC : (∫ x,inner ℝ x (S x) ∂μ)=c := by
    have hh : (∫ x,inner ℝ x (S x)-c ∂μ)=0 := by
      rw [← hLaw,integral_map W.continuous.measurable.aemeasurable (hmeas.sub_const c).aestronglyMeasurable]
      simpa only [heq] using h.2.1
    rw [integral_sub (hLpQ.integrable (by norm_num)) (integrable_const c),integral_const] at hh
    simpa only [probReal_univ,one_smul] using sub_eq_zero.mp hh
  refine ⟨hLpQ,?_⟩
  rw [hC,← hLaw,integral_map W.continuous.measurable.aemeasurable
    (((hmeas.sub_const c).pow_const 2).aestronglyMeasurable)]
  simp only [heq]
  have hn : ‖T‖ ≤ σ^2*‖S‖ := by
    calc
      _ ≤ ‖W.adjoint‖*‖S.comp W‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖W‖*(‖S‖*‖W‖) := by rw [LinearIsometryEquiv.norm_map];gcongr;exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ σ*(‖S‖*σ) := by gcongr
      _=_ := by ring
  have hquad:=h.2.2.2
  simp only [finrank_euclideanSpace,Fintype.card_fin] at hquad
  calc
    _ ≤ 2*(Module.finrank ℝ E:ℝ)*‖T‖^2 := hquad
    _ ≤ 2*(Module.finrank ℝ E:ℝ)*(σ^2*‖S‖)^2 := by
      apply mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn) (by positivity)
    _=_ := by ring

end
end SlowEquilibration.GaussianQuadraticVariance
