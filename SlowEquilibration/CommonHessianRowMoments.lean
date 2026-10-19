-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianRowQuadraticVariance
public import SlowEquilibration.GaussianVectorPolynomialMoments

/-! Actual dimension-uniform Gaussian common-row norm moments derived
from its true covariance b/N, rather than supplied row-moment hypotheses. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance GaussianVectorPolynomialMoments
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Actual posterior centered common rows have uniformly bounded ordinary
norm moments in every integer degree, including dimension zero. -/
theorem conditional_common_row_norm_moments {N P m : ℕ} (hN : 0 < N) (hmN : m ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i,inner ℝ (e i) x=0)
    (v : Vector N) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (hve : ∀ i,inner ℝ (e i) v=0)
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A) :
    ∀ r:ℕ,Integrable (fun u:EuclideanSpace ℝ (Fin m)=>‖u‖^r) (centeredLaw A (commonRowCLM c x e v)) ∧
      (∫ u,‖u‖^r ∂centeredLaw A (commonRowCLM c x e v)) ≤
        (r.factorial:ℝ)*Real.exp (Real.sqrt (secondCovariance c 1)+secondCovariance c 1/2) := by
  let τ:=secondCovariance c 1/(N:ℝ)
  have hτ : 0 < τ:=div_pos hb (Nat.cast_pos.mpr hN)
  have hcov (u:EuclideanSpace ℝ (Fin m)) :
      covarianceBilin (centeredLaw A (commonRowCLM c x e v)) u u ≤ (Real.sqrt τ)^2*‖u‖^2 := by
    have hh:=centeredLaw_covariance_le_gram A hA (commonRowCLM c x e v) u
    rw [commonRowCLM_gram hN c hc x hx e he htan v hv hvtan hve] at hh
    simpa only [smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,
      real_inner_self_eq_norm_sq,Real.sq_sqrt hτ.le] using hh
  have hscale : Real.sqrt τ*Real.sqrt (m:ℝ) ≤ Real.sqrt (secondCovariance c 1) := by
    rw [← Real.sqrt_mul hτ.le]
    apply Real.sqrt_le_sqrt
    change (secondCovariance c 1/(N:ℝ))*(m:ℝ) ≤ secondCovariance c 1
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmN) hb.le
  have hτbound : τ ≤ secondCovariance c 1 := by
    change secondCovariance c 1/(N:ℝ) ≤ secondCovariance c 1
    exact div_le_self hb.le (by exact_mod_cast hN)
  intro r
  have hh:=centered_gaussian_norm_moments (centeredLaw A (commonRowCLM c x e v)) (centeredLaw_mean A _)
    (Real.sqrt_pos.mpr hτ) hcov (by simpa only [finrank_euclideanSpace,Fintype.card_fin] using hscale) r
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  rw [Real.sq_sqrt hτ.le]
  linarith

end
end SlowEquilibration.SphericalCommonHessianRegression
