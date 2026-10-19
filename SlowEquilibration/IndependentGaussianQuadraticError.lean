-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuadraticUniformBound
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.HasLaw

/-! Actual independent Gaussian row integration for a measurable bounded
operator field. Genuine covariance inputs imply the quadratic L² bound;
no conditional row estimate is supplied as a conclusion-shaped premise. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {E X Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace X] [MeasurableSpace Ω]

omit [MeasurableSpace E] [BorelSpace E] in
lemma clm_trace_continuous :
    Continuous (fun S:E→L[ℝ]E=>LinearMap.trace ℝ E S.toLinearMap) := by
  have heq : (fun S:E→L[ℝ]E=>LinearMap.trace ℝ E S.toLinearMap)=
      (fun S=>∑ i,inner ℝ (stdOrthonormalBasis ℝ E i) (S (stdOrthonormalBasis ℝ E i))) :=
    funext (clm_trace_eq_sum_inner (stdOrthonormalBasis ℝ E))
  rw [heq]
  fun_prop

/-- Genuine Fubini estimate over the product of a bulk law and a centered
Gaussian row law. The operator field can be the actual clipped inverse. -/
theorem gaussian_product_quadratic_mean_square (ν : Measure X) [IsProbabilityMeasure ν]
    (μ : Measure E) [IsGaussian μ] (hmean : ∫ u,u ∂μ=0) {σ K M L τ : ℝ}
    (hσ : 0 ≤ σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hcov : ∀ u:E,covarianceBilin μ u u ≤ σ^2*‖u‖^2)
    (hCovErr : ‖covarianceOperator μ-τ • ContinuousLinearMap.id ℝ E‖ ≤ K)
    (v : E) (hv : ‖v‖ ≤ M) (S : X → (E→L[ℝ]E)) (hSM : Measurable S)
    (hSS : ∀ x,(S x).toLinearMap.IsSymmetric) (hSL : ∀ x,‖S x‖ ≤ L) :
    Integrable (fun p:X×E=>
      (inner ℝ (p.2+v) (S p.1 (p.2+v))-τ*LinearMap.trace ℝ E (S p.1).toLinearMap)^2) (ν.prod μ) ∧
    (∫ p:X×E,(inner ℝ (p.2+v) (S p.1 (p.2+v))-τ*LinearMap.trace ℝ E (S p.1).toLinearMap)^2 ∂ν.prod μ) ≤
      quadraticErrorBound (Module.finrank ℝ E) σ K M L := by
  let F:=fun p:X×E=>(inner ℝ (p.2+v) (S p.1 (p.2+v))-τ*LinearMap.trace ℝ E (S p.1).toLinearMap)^2
  let C:=quadraticErrorBound (Module.finrank ℝ E) σ K M L
  have hT : Measurable (fun x=>LinearMap.trace ℝ E (S x).toLinearMap) :=
    clm_trace_continuous.measurable.comp hSM
  have hEval : Measurable (fun p:(E→L[ℝ]E)×E=>p.1 p.2) :=
    (show Continuous (fun p:(E→L[ℝ]E)×E=>p.1 p.2) from by fun_prop).measurable
  have hSX : Measurable (fun p:X×E=>S p.1 (p.2+v)) :=
    hEval.comp ((hSM.comp measurable_fst).prodMk (measurable_snd.add_const v))
  have hF : Measurable F :=
    (((measurable_snd.add_const v).inner hSX).sub (measurable_const.mul (hT.comp measurable_fst))).pow_const 2
  have hRow (x:X) : Integrable (fun u=>F (x,u)) μ ∧ (∫ u,F (x,u) ∂μ) ≤ C :=
    gaussian_quadratic_uniform_mean_square μ hmean hσ hK hM hL hcov hCovErr v hv (S x) (hSS x) (hSL x)
  have hNorm (x:X) (u:E) : ‖F (x,u)‖=F (x,u):=Real.norm_of_nonneg (sq_nonneg _)
  have hCI : Integrable (fun x=>∫ u,‖F (x,u)‖ ∂μ) ν := by
    apply Integrable.of_bound hF.aestronglyMeasurable.norm.integral_prod_right' C
    filter_upwards with x
    rw [Real.norm_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
    simp only [hNorm]
    exact (hRow x).2
  have hProd : Integrable F (ν.prod μ):=(integrable_prod_iff hF.aestronglyMeasurable).mpr
    ⟨ae_of_all _ (fun x=>(hRow x).1),hCI⟩
  refine ⟨hProd,?_⟩
  rw [integral_prod F hProd]
  have hh:=integral_mono_ae hProd.integral_prod_left (integrable_const C)
    (ae_of_all _ (fun x=>(hRow x).2))
  simpa only [integral_const,probReal_univ,one_smul] using hh

/-- True independent observations on an arbitrary original probability
space inherit the same actual Gaussian quadratic estimate. -/
theorem independent_gaussian_quadratic_mean_square (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → X) (U : Ω → E) (ν : Measure X) [IsProbabilityMeasure ν] (μ : Measure E) [IsGaussian μ]
    (hW : HasLaw W ν P) (hU : HasLaw U μ P) (hWU : IndepFun W U P) (hmean : ∫ u,u ∂μ=0)
    {σ K M L τ : ℝ} (hσ : 0 ≤ σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hcov : ∀ u:E,covarianceBilin μ u u ≤ σ^2*‖u‖^2)
    (hCovErr : ‖covarianceOperator μ-τ • ContinuousLinearMap.id ℝ E‖ ≤ K)
    (v : E) (hv : ‖v‖ ≤ M) (S : X → (E→L[ℝ]E)) (hSM : Measurable S)
    (hSS : ∀ x,(S x).toLinearMap.IsSymmetric) (hSL : ∀ x,‖S x‖ ≤ L) :
    Integrable (fun ω=>(inner ℝ (U ω+v) (S (W ω) (U ω+v))-τ*LinearMap.trace ℝ E (S (W ω)).toLinearMap)^2) P ∧
    (∫ ω,(inner ℝ (U ω+v) (S (W ω) (U ω+v))-τ*LinearMap.trace ℝ E (S (W ω)).toLinearMap)^2 ∂P) ≤
      quadraticErrorBound (Module.finrank ℝ E) σ K M L := by
  let F:=fun p:X×E=>(inner ℝ (p.2+v) (S p.1 (p.2+v))-τ*LinearMap.trace ℝ E (S p.1).toLinearMap)^2
  have hProd:=gaussian_product_quadratic_mean_square ν μ hmean hσ hK hM hL hcov hCovErr v hv S hSM hSS hSL
  have hLaw:=hWU.hasLaw_prod hW hU
  refine ⟨?_,?_⟩
  · exact hLaw.integrable_comp (f:=F) hProd.1
  · have hi:=hLaw.integral_comp (f:=F) hProd.1.aestronglyMeasurable
    simp only [Function.comp_def,F] at hi
    rw [hi]
    exact hProd.2

end
end SlowEquilibration.GaussianQuadraticVariance

