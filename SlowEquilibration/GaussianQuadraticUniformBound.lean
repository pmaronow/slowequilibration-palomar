-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianNormSecondMoment
public import SlowEquilibration.GaussianCovarianceQuadraticVariance
public import SlowEquilibration.GaussianQuadraticTranslation
public import SlowEquilibration.QuadraticPerturbation

/-! Actual Gaussian quadratic-error estimate uniform over bounded
symmetric operators, including singular covariance and genuine mean shifts. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory BoundedQuadraticConvergence
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def quadraticErrorBound (d : ℕ) (σ K M L : ℝ) : ℝ :=
  L^2*(8*(d:ℝ)*σ^4+4*(d:ℝ)^2*K^2+16*(d:ℝ)*σ^2*M^2+4*M^4)

/-- True finite Gaussian L² estimate from literal covariance domination
and covariance-operator perturbation. Neither a quadratic mean nor variance
bound is assumed. All constants use the row's own target dimension. -/
theorem gaussian_quadratic_uniform_mean_square (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x,x ∂μ=0) {σ K M L τ : ℝ} (hσ : 0 ≤ σ) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hcov : ∀ x:E,covarianceBilin μ x x ≤ σ^2*‖x‖^2)
    (hCovErr : ‖covarianceOperator μ-τ • ContinuousLinearMap.id ℝ E‖ ≤ K)
    (v : E) (hv : ‖v‖ ≤ M) (S : E →L[ℝ] E)
    (hS : S.toLinearMap.IsSymmetric) (hSL : ‖S‖ ≤ L) :
    Integrable (fun u=>(inner ℝ (u+v) (S (u+v))-τ*LinearMap.trace ℝ E S.toLinearMap)^2) μ ∧
      (∫ u,(inner ℝ (u+v) (S (u+v))-τ*LinearMap.trace ℝ E S.toLinearMap)^2 ∂μ) ≤
        quadraticErrorBound (Module.finrank ℝ E) σ K M L := by
  let d:=Module.finrank ℝ E
  let Q:=fun u:E=>inner ℝ u (S u)
  let t:=τ*LinearMap.trace ℝ E S.toLinearMap
  let ε:=(d:ℝ)*‖S‖*‖covarianceOperator μ-τ • ContinuousLinearMap.id ℝ E‖
  have hVar:=centered_gaussian_quadratic_variance μ hmean hσ hcov S hS
  have hF : Integrable (fun u=>(Q u-t)^2) μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp (hVar.1.sub (memLp_const t))
  have hG : Integrable (fun u=>(Q u-(∫ z,Q z ∂μ))^2) μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp (hVar.1.sub (memLp_const _))
  have hME : |(∫ z,Q z ∂μ)-t| ≤ ε := by
    rw [quadratic_integral_eq_trace μ IsGaussian.memLp_two_id]
    have heq : LinearMap.trace ℝ E (S.comp (covarianceOperator μ)).toLinearMap-
        τ*LinearMap.trace ℝ E S.toLinearMap=
      LinearMap.trace ℝ E (S.comp (covarianceOperator μ-τ • ContinuousLinearMap.id ℝ E)).toLinearMap := by
      rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_id]
      simp only [ContinuousLinearMap.toLinearMap_sub,ContinuousLinearMap.toLinearMap_smul,map_sub,map_smul,smul_eq_mul]
    change |LinearMap.trace ℝ E (S.comp (covarianceOperator μ)).toLinearMap-t| ≤ _
    rw [heq]
    exact abs_trace_comp_le_dimension_norm S _
  have hMS : (∫ u,(Q u-t)^2 ∂μ) ≤ 4*(d:ℝ)*σ^4*‖S‖^2+2*ε^2 := by
    have hh:=integral_square_perturbation_bound μ (fun u=>Q u-t) (fun u=>Q u-(∫ z,Q z ∂μ))
      hF hG (show 0 ≤ ε by positivity) (fun u=>by
        have heq : (Q u-t)-(Q u-(∫ z,Q z ∂μ))=(∫ z,Q z ∂μ)-t:=by ring
        rw [heq];exact hME)
    exact hh.trans (by nlinarith [hVar.2])
  have hNorm:=centered_gaussian_norm_second_moment μ hmean (σ^2) hcov
  have hTrans:=quadratic_translation_mean_square μ S v hM hv t hF hNorm.1
  refine ⟨hTrans.1,?_⟩
  calc
    _ ≤ 2*(4*(d:ℝ)*σ^4*‖S‖^2+2*ε^2)+16*‖S‖^2*M^2*((d:ℝ)*σ^2)+4*‖S‖^2*M^4 :=
      hTrans.2.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hMS (by norm_num))
        (mul_le_mul_of_nonneg_left hNorm.2 (by positivity))) le_rfl)
    _ ≤ 2*(4*(d:ℝ)*σ^4*L^2+2*((d:ℝ)*L*K)^2)+16*L^2*M^2*((d:ℝ)*σ^2)+4*L^2*M^4 := by
      have hε : ε ≤ (d:ℝ)*L*K := mul_le_mul
        (mul_le_mul_of_nonneg_left hSL (Nat.cast_nonneg _)) hCovErr (norm_nonneg _) (by positivity)
      have hεsq : ε^2 ≤ ((d:ℝ)*L*K)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hε
      have hSq : ‖S‖^2 ≤ L^2 := (sq_le_sq₀ (norm_nonneg _) hL).mpr hSL
      gcongr
    _=_:=by unfold quadraticErrorBound;ring

end
end SlowEquilibration.GaussianQuadraticVariance

