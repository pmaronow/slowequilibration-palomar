-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianRowGram
public import SlowEquilibration.GaussianCovarianceQuadraticVariance
public import SlowEquilibration.GaussianRegressionSchur

/-! Actual conditional common border-row quadratic variance on its own
m-dimensional Gaussian target; no coefficient dimension enters the bound. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegressionCovariance
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace F] [BorelSpace F] in
lemma centeredLaw_covariance_le_gram (A : E →L[ℝ] F) (hA : Surjective A) (B : E →L[ℝ] G) (u : G) :
    covarianceBilin (centeredLaw A B) u u ≤ inner ℝ u (gram B u) := by
  rw [centeredLaw,covarianceBilin_map IsGaussian.memLp_two_id,covarianceBilin_stdGaussian,
    innerSL_apply_apply,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,residual_adjoint A hA,
    real_inner_self_eq_norm_sq]
  have hright : inner ℝ u (gram B u)=‖B.adjoint u‖^2 := by
    change inner ℝ u (B (B.adjoint u))=‖B.adjoint u‖^2
    rw [← B.adjoint_inner_left,real_inner_self_eq_norm_sq]
  rw [hright]
  have hR : ‖residual A‖ ≤ 1 := by
    rw [residual_eq_starProjection A hA]
    exact A.ker.starProjection_norm_le
  have hnorm : ‖residual A (B.adjoint u)‖ ≤ ‖B.adjoint u‖ :=
    ((residual A).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hR)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm

end
end SlowEquilibration.GaussianRegressionCovariance

namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance GaussianQuadraticVariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
/-- True posterior row variance is O(m/N²) for a uniformly bounded
symmetric resolvent test. Every covariance input is derived from the actual
tensor row and canonical Gaussian regression, including singular rows. -/
theorem conditional_common_row_quadratic_variance {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hb : 0 ≤ secondCovariance c 1) (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i,inner ℝ (e i) x=0)
    (v : Vector N) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (hve : ∀ i,inner ℝ (e i) v=0)
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A)
    (S : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hS : S.toLinearMap.IsSymmetric) :
    let μ:=centeredLaw A (commonRowCLM c x e v)
    MemLp (fun u=>inner ℝ u (S u)) 2 μ ∧
      (∫ u,(inner ℝ u (S u)-(∫ z,inner ℝ z (S z) ∂μ))^2 ∂μ) ≤
        2*(m:ℝ)*(secondCovariance c 1/(N:ℝ))^2*‖S‖^2 := by
  dsimp only
  let τ:=secondCovariance c 1/(N:ℝ)
  have hτ : 0 ≤ τ:=div_nonneg hb (Nat.cast_nonneg N)
  have hcov (u : EuclideanSpace ℝ (Fin m)) :
      covarianceBilin (centeredLaw A (commonRowCLM c x e v)) u u ≤ (Real.sqrt τ)^2*‖u‖^2 := by
    have hh:=centeredLaw_covariance_le_gram A hA (commonRowCLM c x e v) u
    rw [commonRowCLM_gram hN c hc x hx e he htan v hv hvtan hve] at hh
    simpa only [smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,
      real_inner_self_eq_norm_sq,Real.sq_sqrt hτ] using hh
  have hh:=centered_gaussian_quadratic_variance (centeredLaw A (commonRowCLM c x e v))
    (centeredLaw_mean A _) (Real.sqrt_nonneg τ) hcov S hS
  have hfour : (Real.sqrt τ)^4=τ^2 := by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,Real.sq_sqrt hτ]
  simpa only [finrank_euclideanSpace,Fintype.card_fin,hfour,τ] using hh

end
end SlowEquilibration.SphericalCommonHessianRegression
