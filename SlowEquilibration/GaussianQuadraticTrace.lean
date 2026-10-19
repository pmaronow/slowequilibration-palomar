-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuadraticVariance
public import Mathlib.Probability.Moments.CovarianceBilin

/-! Actual quadratic expectation equals the true covariance-operator
trace; finite trace perturbations have a dimension-explicit norm bound. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma clm_trace_eq_sum_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : OrthonormalBasis ι ℝ E) (S : E →L[ℝ] E) :
    LinearMap.trace ℝ E S.toLinearMap=∑ i,inner ℝ (B i) (S (B i)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ B.toBasis]
  simp only [Matrix.trace,Matrix.diag_apply,LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis,OrthonormalBasis.repr_apply_apply]
  rfl

/-- Genuine ordinary quadratic expectation identity for any law with a
finite second moment. covarianceOperator is the actual uncentered second-
moment operator; for the actual centered Gaussian row it is its covariance. -/
theorem quadratic_integral_eq_trace (μ : Measure E) (hμ : MemLp id 2 μ) (S : E →L[ℝ] E) :
    (∫ x,inner ℝ x (S x) ∂μ)=LinearMap.trace ℝ E (S.comp (covarianceOperator μ)).toLinearMap := by
  let B:=stdOrthonormalBasis ℝ E
  have hpoint (x:E) : inner ℝ x (S x)=∑ i,inner ℝ x (B i)*inner ℝ (B i) (S x) :=
    (B.sum_inner_mul_inner x (S x)).symm
  have hint (i : Fin (Module.finrank ℝ E)) : Integrable (fun x:E=>inner ℝ x (B i)*inner ℝ (B i) (S x)) μ := by
    have h1 : MemLp (fun x:E=>inner ℝ x (B i)) 2 μ := by
      simpa only [id_eq] using hμ.inner_const (B i)
    have h2 : MemLp (fun x:E=>inner ℝ (S.adjoint (B i)) x) 2 μ := by
      simpa only [id_eq] using hμ.const_inner (S.adjoint (B i))
    convert h1.integrable_mul h2 using 1
    ext x
    change inner ℝ x (B i)*inner ℝ (B i) (S x)=inner ℝ x (B i)*inner ℝ (S.adjoint (B i)) x
    rw [S.adjoint_inner_left]
  rw [show (fun x:E=>inner ℝ x (S x))=(fun x=>∑ i,inner ℝ x (B i)*inner ℝ (B i) (S x)) from funext hpoint,
    integral_finsetSum _ (fun i _=>hint i),clm_trace_eq_sum_inner B]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ContinuousLinearMap.comp_apply,← S.adjoint_inner_left,real_inner_comm]
  rw [covarianceOperator_inner hμ]
  apply integral_congr_ae
  exact ae_of_all _ (fun x=>by
    change inner ℝ x (B i)*inner ℝ (B i) (S x)=inner ℝ (B i) x*inner ℝ (S.adjoint (B i)) x
    rw [real_inner_comm x (B i),S.adjoint_inner_left])

omit [MeasurableSpace E] [BorelSpace E] in
/-- Actual finite trace product norm bound, without a spectral or
positive-semidefinite premise or an assumed trace comparison. -/
theorem abs_trace_comp_le_dimension_norm (S T : E →L[ℝ] E) :
    |LinearMap.trace ℝ E (S.comp T).toLinearMap| ≤ (Module.finrank ℝ E:ℝ)*‖S‖*‖T‖ := by
  let B:=stdOrthonormalBasis ℝ E
  rw [clm_trace_eq_sum_inner B]
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℝ E),|inner ℝ (B i) (S (T (B i)))|:=Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E),‖S‖*‖T‖:=Finset.sum_le_sum (fun i _=>by
      calc
        _ ≤ ‖B i‖*‖S (T (B i))‖:=abs_real_inner_le_norm _ _
        _ ≤ ‖B i‖*(‖S‖*‖T (B i)‖):=mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖B i‖*(‖S‖*(‖T‖*‖B i‖)):=mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)) (norm_nonneg _)
        _=_:=by rw [B.norm_eq_one i];ring)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end
end SlowEquilibration.GaussianQuadraticVariance
