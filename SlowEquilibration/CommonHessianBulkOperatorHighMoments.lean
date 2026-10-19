-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianValueRowRegressionBounds
public import SlowEquilibration.CommonHessianPosteriorBorder
public import SlowEquilibration.GaussianPosteriorQuadraticMean
public import SlowEquilibration.CommonHessianIndependentHighMoments
public import SlowEquilibration.CommonHessianBulkOperatorMeanSquare

/-! Actual mixed/proper-value conditional every-real-q row quadratic estimate for an
operator depending on the full common bulk pair. Covariance, mean and
bulk-row independence are derived from the original tensor model. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance GaussianObservationCoercivity GaussianCovarianceRepresentation
open NormalizedPairObservations PairHessianMean PairObservationNormBounds GaussianQuadraticVariance
open CanonicalGOERealization SphericalConditionalMatrices
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- True mixed whole-disorder posterior estimate for a bulk-measurable
operator. No posterior row covariance, regression mean or independence
conclusion is assumed; all three follow from actual tensor derivatives. -/
theorem actual_common_row_mixed_bulk_operator_q_moment {N P m k : ℕ} (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1) {d : ℕ} (hd : 3 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y v v' : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hve : ∀ i,inner ℝ (e i) v=0) (hve' : ∀ i,inner ℝ (e i) v'=0)
    (f g : Fin k → Vector N) (hg : Orthonormal ℝ g) (hr : |overlap x y| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hA : Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)))
    (hinv : ‖(gram (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (MixedObservationSpace k×MixedObservationSpace k)) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 < L)
    (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ))
    (S : CommonBulkPairSpace m → (EuclideanSpace ℝ (Fin m)→L[ℝ]EuclideanSpace ℝ (Fin m)))
    (hSM : Measurable S) (hSS : ∀ z,(S z).toLinearMap.IsSymmetric) (hSL : ∀ z,‖S z‖ ≤ L) (q : ℝ) (hq : 0 ≤ q) :
    let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
    let B:=commonRowCLM c x e v
    let W:=actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e))
    let τ:=secondCovariance c 1/(N:ℝ)
    Integrable (fun J=>|inner ℝ (actualObservation B J) (S (W J) (actualObservation B J))-
      τ*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin m)) (S (W J)).toLinearMap|^q) (coefficientKernel A w) ∧
    (∫ J,|inner ℝ (actualObservation B J) (S (W J) (actualObservation B J))-
      τ*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin m)) (S (W J)).toLinearMap|^q ∂coefficientKernel A w) ≤
      quadraticHighMomentBound m (Real.sqrt τ)
        (profileBound c^2/((N:ℝ)*δ)*|overlap x y|^(2*(d-2)))
        ((profileBound c*M/δ)*|overlap x y|^(d-2)) L (Real.sqrt (secondCovariance c 1)) q := by
  dsimp only
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  let B:=commonRowCLM c x e v
  let W:=actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e))
  let η:=coefficientKernel A w
  let μ:=centeredLaw A B
  let τ:=secondCovariance c 1/(N:ℝ)
  let K:=profileBound c^2/((N:ℝ)*δ)*|overlap x y|^(2*(d-2))
  let M0:=(profileBound c*M/δ)*|overlap x y|^(d-2)
  let m0:=B (lift A w)
  let U:=fun J=>actualObservation B J-m0
  have hτpos : 0 < τ:=div_pos hb (Nat.cast_pos.mpr hN)
  have hτ : 0 ≤ τ:=hτpos.le
  have hGram:=commonRowCLM_gram hN c hc x hx e he htanx v hv hvtan hve
  have hcov (u:EuclideanSpace ℝ (Fin m)) : covarianceBilin μ u u ≤ (Real.sqrt τ)^2*‖u‖^2 := by
    have hh:=centeredLaw_covariance_le_gram A hA B u
    rw [hGram] at hh
    simpa only [smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,
      real_inner_self_eq_norm_sq,Real.sq_sqrt hτ] using hh
  have hCovErr : ‖covarianceOperator μ-τ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))‖ ≤ K := by
    rw [centeredLaw_covarianceOperator,← hGram]
    exact common_row_pair_residual_gram_norm hN c hc hd hdeg x y v hy hv hvtan e he htanx htany f g hg hr hδ hA hinv
  have hm0 : ‖m0‖ ≤ M0:=common_row_pair_mixed_lift_norm hN c hc hd hdeg x y v hy hv hvtan e he htanx htany f g hg hr hδ hM hinv w hw
  have hFull:=common_bulk_border_mixed_independent hN c hc (fun p hp=>le_trans hd (hdeg p hp)) x y v v' e htanx htany hve hve' f g w hA
  let R:=fun z:WithLp 2 (WithLp 2 (EuclideanSpace ℝ (Fin m)×ℝ)×WithLp 2 (EuclideanSpace ℝ (Fin m)×ℝ))=>z.fst.fst-m0
  have hRM : Measurable R:=by fun_prop
  have hWU : IndepFun W U η := by
    have hh:=hFull.comp measurable_id hRM
    have hE : R ∘ actualObservation (borderPairCLM c x y e v v')=U := by
      funext J
      rfl
    change IndepFun W (R ∘ actualObservation (borderPairCLM c x y e v v')) η at hh
    rwa [hE] at hh
  have hWM : Measurable W:=
    (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)).continuous.measurable.comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P=>ℝ)).symm.continuous.measurable.comp
        (flatDisorder_measurable N P))
  let ν:=η.map W
  have hW : HasLaw W ν η:=hasLaw_map hWM.aemeasurable
  have : IsProbabilityMeasure ν:=hW.isProbabilityMeasure_iff.mp inferInstance
  have hU : HasLaw U μ η:=centered_actualObservation_hasLaw A B w
  have hscale : Real.sqrt τ*Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)):ℝ) ≤ Real.sqrt (secondCovariance c 1) := by
    simp only [finrank_euclideanSpace,Fintype.card_fin]
    rw [← Real.sqrt_mul hτ]
    apply Real.sqrt_le_sqrt
    calc
      τ*(m:ℝ) ≤ τ*(N:ℝ):=mul_le_mul_of_nonneg_left (by exact_mod_cast hmN) hτ
      _=secondCovariance c 1:=by dsimp only [τ];field_simp
  have hh:=independent_gaussian_quadratic_high_moment η W U ν μ hW hU hWU (centeredLaw_mean A B)
    (Real.sqrt_pos.mpr hτpos) (show 0 ≤ K by positivity [profileBound_pos c])
    (show 0 ≤ M0 by positivity [profileBound_pos c]) hL hcov hCovErr hscale m0 hm0 S hSM hSS hSL
      (by simpa only [finrank_euclideanSpace,Fintype.card_fin] using hm) q hq
  simpa only [U,sub_add_cancel,μ,τ,K,M0,B,W,η,finrank_euclideanSpace,Fintype.card_fin] using hh

/-- True value whole-disorder posterior estimate for a bulk-measurable
operator. No posterior row covariance, regression mean or independence
conclusion is assumed; all three follow from actual tensor derivatives. -/
theorem actual_common_row_value_bulk_operator_q_moment {N P m k : ℕ} (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1) {d : ℕ} (hd : 3 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y v v' : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hve : ∀ i,inner ℝ (e i) v=0) (hve' : ∀ i,inner ℝ (e i) v'=0)
    (f g : Fin k → Vector N) (hg : Orthonormal ℝ g) (hr : |overlap x y| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hA : Surjective (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)))
    (hinv : ‖(gram (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (ValueObservationSpace k×ValueObservationSpace k)) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 < L)
    (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ))
    (S : CommonBulkPairSpace m → (EuclideanSpace ℝ (Fin m)→L[ℝ]EuclideanSpace ℝ (Fin m)))
    (hSM : Measurable S) (hSS : ∀ z,(S z).toLinearMap.IsSymmetric) (hSL : ∀ z,‖S z‖ ≤ L) (q : ℝ) (hq : 0 ≤ q) :
    let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
    let B:=commonRowCLM c x e v
    let W:=actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e))
    let τ:=secondCovariance c 1/(N:ℝ)
    Integrable (fun J=>|inner ℝ (actualObservation B J) (S (W J) (actualObservation B J))-
      τ*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin m)) (S (W J)).toLinearMap|^q) (coefficientKernel A w) ∧
    (∫ J,|inner ℝ (actualObservation B J) (S (W J) (actualObservation B J))-
      τ*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin m)) (S (W J)).toLinearMap|^q ∂coefficientKernel A w) ≤
      quadraticHighMomentBound m (Real.sqrt τ)
        (profileBound c^2/((N:ℝ)*δ)*|overlap x y|^(2*(d-2)))
        ((profileBound c*M/δ)*|overlap x y|^(d-2)) L (Real.sqrt (secondCovariance c 1)) q := by
  dsimp only
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let B:=commonRowCLM c x e v
  let W:=actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e))
  let η:=coefficientKernel A w
  let μ:=centeredLaw A B
  let τ:=secondCovariance c 1/(N:ℝ)
  let K:=profileBound c^2/((N:ℝ)*δ)*|overlap x y|^(2*(d-2))
  let M0:=(profileBound c*M/δ)*|overlap x y|^(d-2)
  let m0:=B (lift A w)
  let U:=fun J=>actualObservation B J-m0
  have hτpos : 0 < τ:=div_pos hb (Nat.cast_pos.mpr hN)
  have hτ : 0 ≤ τ:=hτpos.le
  have hGram:=commonRowCLM_gram hN c hc x hx e he htanx v hv hvtan hve
  have hcov (u:EuclideanSpace ℝ (Fin m)) : covarianceBilin μ u u ≤ (Real.sqrt τ)^2*‖u‖^2 := by
    have hh:=centeredLaw_covariance_le_gram A hA B u
    rw [hGram] at hh
    simpa only [smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,
      real_inner_self_eq_norm_sq,Real.sq_sqrt hτ] using hh
  have hCovErr : ‖covarianceOperator μ-τ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))‖ ≤ K := by
    rw [centeredLaw_covarianceOperator,← hGram]
    exact common_row_value_pair_residual_gram_norm hN c hc hd hdeg x y v hy hv hvtan e he htanx htany f g hg hr hδ hA hinv
  have hm0 : ‖m0‖ ≤ M0:=common_row_pair_value_lift_norm hN c hc hd hdeg x y v hy hv hvtan e he htanx htany f g hg hr hδ hM hinv w hw
  have hFull:=common_bulk_border_value_independent hN c hc (fun p hp=>le_trans hd (hdeg p hp)) x y v v' e htanx htany hve hve' f g w hA
  let R:=fun z:WithLp 2 (WithLp 2 (EuclideanSpace ℝ (Fin m)×ℝ)×WithLp 2 (EuclideanSpace ℝ (Fin m)×ℝ))=>z.fst.fst-m0
  have hRM : Measurable R:=by fun_prop
  have hWU : IndepFun W U η := by
    have hh:=hFull.comp measurable_id hRM
    have hE : R ∘ actualObservation (borderPairCLM c x y e v v')=U := by
      funext J
      rfl
    change IndepFun W (R ∘ actualObservation (borderPairCLM c x y e v v')) η at hh
    rwa [hE] at hh
  have hWM : Measurable W:=
    (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)).continuous.measurable.comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P=>ℝ)).symm.continuous.measurable.comp
        (flatDisorder_measurable N P))
  let ν:=η.map W
  have hW : HasLaw W ν η:=hasLaw_map hWM.aemeasurable
  have : IsProbabilityMeasure ν:=hW.isProbabilityMeasure_iff.mp inferInstance
  have hU : HasLaw U μ η:=centered_actualObservation_hasLaw A B w
  have hscale : Real.sqrt τ*Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)):ℝ) ≤ Real.sqrt (secondCovariance c 1) := by
    simp only [finrank_euclideanSpace,Fintype.card_fin]
    rw [← Real.sqrt_mul hτ]
    apply Real.sqrt_le_sqrt
    calc
      τ*(m:ℝ) ≤ τ*(N:ℝ):=mul_le_mul_of_nonneg_left (by exact_mod_cast hmN) hτ
      _=secondCovariance c 1:=by dsimp only [τ];field_simp
  have hh:=independent_gaussian_quadratic_high_moment η W U ν μ hW hU hWU (centeredLaw_mean A B)
    (Real.sqrt_pos.mpr hτpos) (show 0 ≤ K by positivity [profileBound_pos c])
    (show 0 ≤ M0 by positivity [profileBound_pos c]) hL hcov hCovErr hscale m0 hm0 S hSM hSS hSL
      (by simpa only [finrank_euclideanSpace,Fintype.card_fin] using hm) q hq
  simpa only [U,sub_add_cancel,μ,τ,K,M0,B,W,η,finrank_euclideanSpace,Fintype.card_fin] using hh

end
end SlowEquilibration.SphericalCommonHessianRegression
