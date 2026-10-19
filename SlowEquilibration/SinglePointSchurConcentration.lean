-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SinglePointBulkBorderLaw
public import SlowEquilibration.IndependentGaussianQuadraticError
public import SlowEquilibration.CommonHessianActualSchurMeanSquare
public import SlowEquilibration.GOEPhysicalCovarianceTraceIntegrability

/-! Genuine single-point original-posterior Schur concentration. All
regression means and covariance perturbations vanish by proved own-point
orthogonality; the clipped inverse remains the actual GOE bulk inverse. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance SphericalConditionalMatrices
open NormalizedPairObservations GaussianObservationCoercivity GaussianQuadraticVariance
open GOEClippedResolvent GOEScaling CanonicalGOERealization BoundedQuadraticConvergence
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

/-- Exact own-point covariance and mean yield a genuine L² estimate for
any bounded symmetric operator depending on the actual common GOE bulk. -/
theorem actual_single_row_mixed_bulk_operator_mse {N P m ℓ : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i,inner ℝ (e i) x=0)
    (hve : ∀ i,inner ℝ (e i) v=0) (f : Fin ℓ → Vector N)
    (hA : Surjective (singleMixedObservation c x f)) (w : MixedObservationSpace ℓ)
    {L : ℝ} (hL : 0 ≤ L)
    (S : Matrix (Fin m) (Fin m) ℝ → (EuclideanSpace ℝ (Fin m)→L[ℝ]EuclideanSpace ℝ (Fin m)))
    (hSM : Measurable S) (hSS : ∀ W,(S W).toLinearMap.IsSymmetric) (hSL : ∀ W,‖S W‖ ≤ L) :
    let A:=singleMixedObservation c x f
    let B:=commonRowCLM c x e v
    let τ:=secondCovariance c 1/(N:ℝ)
    Integrable (fun J=>(inner ℝ (actualObservation B J) (S (hessianMatrix c x e J) (actualObservation B J))-
      τ*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin m)) (S (hessianMatrix c x e J)).toLinearMap)^2) (coefficientKernel A w) ∧
    (∫ J,(inner ℝ (actualObservation B J) (S (hessianMatrix c x e J) (actualObservation B J))-
      τ*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin m)) (S (hessianMatrix c x e J)).toLinearMap)^2 ∂coefficientKernel A w) ≤
      8*(m:ℝ)*(secondCovariance c 1/(N:ℝ))^2*L^2 := by
  dsimp only
  let A:=singleMixedObservation c x f
  let B:=commonRowCLM c x e v
  let μ:=centeredLaw A B
  let τ:=secondCovariance c 1/(N:ℝ)
  let η:=coefficientKernel A w
  let W:=hessianMatrix c x e
  let U:=actualObservation B
  have hCross:=single_common_row_mixed_cross_zero hN c hc hdeg x v hvtan e htan f
  have hMean : B (lift A w)=0:=lift_map_eq_zero_of_cross_zero A B hCross w
  have hResidual : B.comp (residual A)=B:=residual_map_eq_of_cross_zero A B hCross
  have hGram:=commonRowCLM_gram hN c hc x hx e he htan v hv hvtan hve
  have hCov : covarianceOperator μ=τ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) := by
    rw [centeredLaw_covarianceOperator,hResidual,hGram]
  have hτ : 0 ≤ τ:=div_nonneg hb.le (Nat.cast_nonneg _)
  have hcov (u:EuclideanSpace ℝ (Fin m)) : covarianceBilin μ u u ≤ (Real.sqrt τ)^2*‖u‖^2 := by
    have hh:=centeredLaw_covariance_le_gram A hA B u
    rw [hGram] at hh
    simpa only [smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,
      real_inner_self_eq_norm_sq,Real.sq_sqrt hτ] using hh
  have hFull:=single_common_bulk_border_mixed_independent hN c hc hdeg x v e htan hve f w hA
  let R:=fun z:WithLp 2 (EuclideanSpace ℝ (Fin m)×ℝ)=>z.fst
  have hWU : IndepFun W U η := by
    have hh:=hFull.comp measurable_id (show Measurable R by fun_prop)
    have hE : R ∘ actualObservation (borderCLM c x e v)=U := by
      funext J
      rfl
    change IndepFun W (R ∘ actualObservation (borderCLM c x e v)) η at hh
    rwa [hE] at hh
  have hW:=single_common_matrix_mixed_hasLaw hN c hc hdeg x hx e he htan f w
  have hU : HasLaw U μ η := by
    have hh:=centered_actualObservation_hasLaw A B w
    simpa only [hMean,sub_zero] using hh
  have hh:=independent_gaussian_quadratic_mean_square η W U
    (goeLaw m N (secondCovariance c 1)) μ hW hU hWU (centeredLaw_mean A B)
    (σ:=Real.sqrt τ) (K:=0) (M:=0) (τ:=τ) (Real.sqrt_nonneg _) (by norm_num)
    (by norm_num) hL hcov (by rw [hCov,sub_self,norm_zero]) 0 (by simp) S hSM hSS hSL
  have hτ4 : (Real.sqrt τ)^4=τ^2 := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,Real.sq_sqrt hτ]
  simp only [add_zero,quadraticErrorBound,finrank_euclideanSpace,Fintype.card_fin,
    hτ4,zero_pow (by norm_num : (2:ℕ)≠0),zero_pow (by norm_num : (4:ℕ)≠0),mul_zero,zero_mul] at hh
  exact ⟨hh.1,hh.2.trans_eq (by dsimp only [τ];ring)⟩


/-- Exact own-point covariance and mean yield a genuine L² estimate for
any bounded symmetric operator depending on the actual common GOE bulk. -/
theorem actual_single_row_value_bulk_operator_mse {N P m ℓ : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i,inner ℝ (e i) x=0)
    (hve : ∀ i,inner ℝ (e i) v=0) (f : Fin ℓ → Vector N)
    (hA : Surjective (singleValueObservation c x f)) (w : ValueObservationSpace ℓ)
    {L : ℝ} (hL : 0 ≤ L)
    (S : Matrix (Fin m) (Fin m) ℝ → (EuclideanSpace ℝ (Fin m)→L[ℝ]EuclideanSpace ℝ (Fin m)))
    (hSM : Measurable S) (hSS : ∀ W,(S W).toLinearMap.IsSymmetric) (hSL : ∀ W,‖S W‖ ≤ L) :
    let A:=singleValueObservation c x f
    let B:=commonRowCLM c x e v
    let τ:=secondCovariance c 1/(N:ℝ)
    Integrable (fun J=>(inner ℝ (actualObservation B J) (S (hessianMatrix c x e J) (actualObservation B J))-
      τ*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin m)) (S (hessianMatrix c x e J)).toLinearMap)^2) (coefficientKernel A w) ∧
    (∫ J,(inner ℝ (actualObservation B J) (S (hessianMatrix c x e J) (actualObservation B J))-
      τ*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin m)) (S (hessianMatrix c x e J)).toLinearMap)^2 ∂coefficientKernel A w) ≤
      8*(m:ℝ)*(secondCovariance c 1/(N:ℝ))^2*L^2 := by
  dsimp only
  let A:=singleValueObservation c x f
  let B:=commonRowCLM c x e v
  let μ:=centeredLaw A B
  let τ:=secondCovariance c 1/(N:ℝ)
  let η:=coefficientKernel A w
  let W:=hessianMatrix c x e
  let U:=actualObservation B
  have hCross:=single_common_row_value_cross_zero hN c hc hdeg x v hvtan e htan f
  have hMean : B (lift A w)=0:=lift_map_eq_zero_of_cross_zero A B hCross w
  have hResidual : B.comp (residual A)=B:=residual_map_eq_of_cross_zero A B hCross
  have hGram:=commonRowCLM_gram hN c hc x hx e he htan v hv hvtan hve
  have hCov : covarianceOperator μ=τ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) := by
    rw [centeredLaw_covarianceOperator,hResidual,hGram]
  have hτ : 0 ≤ τ:=div_nonneg hb.le (Nat.cast_nonneg _)
  have hcov (u:EuclideanSpace ℝ (Fin m)) : covarianceBilin μ u u ≤ (Real.sqrt τ)^2*‖u‖^2 := by
    have hh:=centeredLaw_covariance_le_gram A hA B u
    rw [hGram] at hh
    simpa only [smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,
      real_inner_self_eq_norm_sq,Real.sq_sqrt hτ] using hh
  have hFull:=single_common_bulk_border_value_independent hN c hc hdeg x v e htan hve f w hA
  let R:=fun z:WithLp 2 (EuclideanSpace ℝ (Fin m)×ℝ)=>z.fst
  have hWU : IndepFun W U η := by
    have hh:=hFull.comp measurable_id (show Measurable R by fun_prop)
    have hE : R ∘ actualObservation (borderCLM c x e v)=U := by
      funext J
      rfl
    change IndepFun W (R ∘ actualObservation (borderCLM c x e v)) η at hh
    rwa [hE] at hh
  have hW:=single_common_matrix_value_hasLaw hN c hc hdeg x hx e he htan f w
  have hU : HasLaw U μ η := by
    have hh:=centered_actualObservation_hasLaw A B w
    simpa only [hMean,sub_zero] using hh
  have hh:=independent_gaussian_quadratic_mean_square η W U
    (goeLaw m N (secondCovariance c 1)) μ hW hU hWU (centeredLaw_mean A B)
    (σ:=Real.sqrt τ) (K:=0) (M:=0) (τ:=τ) (Real.sqrt_nonneg _) (by norm_num)
    (by norm_num) hL hcov (by rw [hCov,sub_self,norm_zero]) 0 (by simp) S hSM hSS hSL
  have hτ4 : (Real.sqrt τ)^4=τ^2 := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,Real.sq_sqrt hτ]
  simp only [add_zero,quadraticErrorBound,finrank_euclideanSpace,Fintype.card_fin,
    hτ4,zero_pow (by norm_num : (2:ℕ)≠0),zero_pow (by norm_num : (4:ℕ)≠0),mul_zero,zero_mul] at hh
  exact ⟨hh.1,hh.2.trans_eq (by dsimp only [τ];ring)⟩


end
end SlowEquilibration.SphericalCommonHessianRegression
