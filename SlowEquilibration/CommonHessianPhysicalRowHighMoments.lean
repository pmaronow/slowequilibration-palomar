-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianClippedRowHighMoments
public import SlowEquilibration.CommonHessianPhysicalTraceHighMoments
public import SlowEquilibration.CommonHessianRealMomentDifference
public import SlowEquilibration.PosteriorCommonInverseTrace
public import SlowEquilibration.SchurDimensionRates
public import SlowEquilibration.SphericalLinearObservationMeasurable

/-! Actual original-posterior all-q row quadratic rate around the source
physical semicircle target. Both Gaussian row noise and the true trace rate
are derived and the exact overlap exponent is retained. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open GaussianObservationCoercivity NormalizedPairObservations PairObservationNormBounds
open SphericalConditionalMatrices
open GOEClippedResolvent GOEScaling GaussianQuadraticVariance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open scoped RealInnerProductSpace Topology

/-- Genuine original mixed posterior row approximation with every fixed
real q and sharp overlap power d−2, uniformly before dimension and targets. -/
theorem uniform_actual_common_physical_row_mixed_q_rate {P d:ℕ} (c:Degree P→ℝ)
    (hc:∀ p,0 ≤ c p) (hb:0<secondCovariance c 1) (hd:3 ≤ d)
    (hdeg:∀ p,c p≠0 → d ≤ p.val.val) {δ M ρ gap:ℝ}
    (hδ:0<δ) (hM:0 ≤ M) (hρ:0<ρ) (hgap:0<gap)
    (hρgap:ρ ≤ (gap/Real.sqrt (secondCovariance c 1))/2) (q:ℝ) (hq:0 ≤ q) :
    ∃ Cq:ℝ,0<Cq ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x y v:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ))
      (_hv:‖v‖=1) (_hvtan:inner ℝ v x=0) (e:Fin (n+1)→Vector (n+3))
      (_he:Orthonormal ℝ e) (_htanx:∀ i,inner ℝ (e i) x=0) (_htany:∀ i,inner ℝ (e i) y=0)
      (_hve:∀ i,inner ℝ (e i) v=0) (f g:Fin ℓ→Vector (n+3)) (_hg:Orthonormal ℝ g)
      (_hr:|overlap x y| ≤ 1)
      (_hA:Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)))
      (_hinv:‖(gram (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))).inverse‖ ≤ 1/δ)
      (w:WithLp 2 (MixedObservationSpace ℓ×MixedObservationSpace ℓ)) (_hw:‖w‖ ≤ M*Real.sqrt (n+3:ℕ))
      (k:ℝ),2*Real.sqrt (secondCovariance c 1)+gap ≤ k →
      let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
      let b:=secondCovariance c 1
      let κ:=scaleFactor n (n+3) b*ρ
      let F:=fun J=>inner ℝ (actualObservation (commonRowCLM c x e v) J)
        (clippedInverseOperator k κ (hessianMatrix c x e J) (actualObservation (commonRowCLM c x e v) J))-
          b*physicalResolvent b k
      Integrable (fun J=>|F J|^q) (coefficientKernel A w) ∧
      (∫ J,|F J|^q ∂coefficientKernel A w) ≤ Cq*(|overlap x y|^(d-2)+1/Real.sqrt (n+3:ℕ))^q:=by
  let b:=secondCovariance c 1
  let L:=(Real.sqrt (b/3)*ρ)⁻¹
  let C:=profileBound c^2/δ
  let D:=profileBound c*M/δ
  let Cr:=physicalQuadraticMomentConstant b C D L q
  have hLp:0<L:=by dsimp only [L,b];positivity
  have hC:0 ≤ C:=by dsimp only [C];positivity
  have hD:0 ≤ D:=by dsimp only [D];positivity [profileBound_pos c]
  have hQc:=quadraticMomentConstant_pos q
  have hNC:0<gaussianNormRealMomentConstant q (Real.sqrt b) (Real.sqrt b):=by
    unfold gaussianNormRealMomentConstant;positivity
  have hbp:0<b:=hb
  have hCr:0<Cr:=by
    dsimp only [Cr,physicalQuadraticMomentConstant]
    positivity
  obtain ⟨Ct,hCt,hTrace⟩:=physical_covariance_trace_uniform_q_rate 2 hb hgap hρ hρgap q hq
  refine ⟨(2:ℝ)^q*(Cr+Ct*(3:ℝ)^q),by positivity,?_⟩
  filter_upwards [hTrace] with n hn
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f g hg hr hA hinv w hw k hk
  dsimp only
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  let η:=coefficientKernel A w
  let κ:=scaleFactor n (n+3) b*ρ
  let T:=fun J=>clippedInverseOperator k κ (hessianMatrix c x e J)
  let Q:=fun J=>inner ℝ (actualObservation (commonRowCLM c x e v) J)
    (T J (actualObservation (commonRowCLM c x e v) J))
  let F:=fun J=>Q J-b*physicalResolvent b k
  let G:=fun J=>Q J-(b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1))) (T J).toLinearMap
  let Φ:=fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>|physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k|^q
  have hSpec:=hn k hk
  have hΦ:Measurable Φ:=((physicalCovarianceTrace_measurable n 2 b k ρ).sub_const _).abs.pow_const q
  have hLaw:=posterior_common_matrix_mixed_hasLaw (by omega : 0<n+3) c hc
    (fun p hp=>le_trans hd (hdeg p hp)) x y hx e he htanx htany f g w
  have hEq (J:Disorder (n+3) P):|F J-G J|^q=Φ (hessianMatrix c x e J):=by
    have heq:F J-G J=(b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1))) (T J).toLinearMap-b*physicalResolvent b k:=by
      dsimp only [F,G];ring
    rw [heq]
    dsimp only [Φ]
    rw [physicalCovarianceTrace_eq_operator_trace n 2 hb.le k ρ]
  have hDiff:Integrable (fun J=>|F J-G J|^q) η:=by
    simpa only [Function.comp_def,hEq] using hLaw.integrable_comp (f:=Φ) hSpec.1
  have hDI:(∫ J,|F J-G J|^q ∂η) ≤ Ct/(n+1:ℝ)^q:=by
    have hh:=hLaw.integral_comp (f:=Φ) hΦ.aestronglyMeasurable
    simp only [Function.comp_def,←hEq] at hh
    exact hh.trans_le hSpec.2
  have hRow:=actual_common_clipped_row_mixed_q_moment c hc hb hd hdeg x y v hx hy hv hvtan
    e he htanx htany hve f g hg hr hδ hM hρ hA hinv w hw k q hq
  have hκ:0<κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hRM:Measurable (actualObservation (commonRowCLM c x e v)):=actual_linearObservation_measurable _
  have hTM:Measurable T:=(clippedInverseOperator_measurable (n+1) k hκ).comp (tensor_hessianMatrix_measurable c x e)
  have hEval:Measurable (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2):=
    (show Continuous (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2) from by fun_prop).measurable
  have hF:Measurable F:=(hRM.inner (hEval.comp (hTM.prodMk hRM))).sub_const _
  have hFinal:=integral_absolute_moment_difference η F G hF q hq hRow.1 hDiff
  refine ⟨hFinal.1,hFinal.2.trans ?_⟩
  let ε:=|overlap x y|^(d-2)+1/Real.sqrt (n+3:ℕ)
  have hε:0 ≤ ε:=by dsimp only [ε];positivity
  have hN:(1/(n+1:ℝ)) ≤ 3*ε:=by
    have hh:=SchurDimensionRates.inverse_dimension_le_ambient_inverse_sqrt n (C:=1) (by norm_num)
    dsimp only [ε]
    simp only [mul_one,div_eq_mul_inv] at hh ⊢
    nlinarith [pow_nonneg (abs_nonneg (overlap x y)) (d-2)]
  have hNq:(1/(n+1:ℝ))^q ≤ (3:ℝ)^q*ε^q:=by
    simpa only [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hε] using
      Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/(n+1:ℝ)) hN hq
  have hTraceScale:Ct/(n+1:ℝ)^q ≤ Ct*(3:ℝ)^q*ε^q:=by
    rw [show Ct/(n+1:ℝ)^q=Ct*(1/(n+1:ℝ))^q by
      rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 1) (by positivity),Real.one_rpow];ring]
    exact (mul_le_mul_of_nonneg_left hNq hCt.le).trans_eq (by ring)
  have hRowBound:(∫ J,|G J|^q ∂η) ≤ Cr*ε^q:=hRow.2
  calc
    _ ≤ (2:ℝ)^q*(Cr*ε^q+Ct*(3:ℝ)^q*ε^q):=
      mul_le_mul_of_nonneg_left (add_le_add hRowBound (hDI.trans hTraceScale)) (by positivity)
    _=_:=by dsimp only [ε];ring

/-- Genuine original value posterior row approximation with every fixed
real q and sharp overlap power d−2, uniformly before dimension and targets. -/
theorem uniform_actual_common_physical_row_value_q_rate {P d:ℕ} (c:Degree P→ℝ)
    (hc:∀ p,0 ≤ c p) (hb:0<secondCovariance c 1) (hd:3 ≤ d)
    (hdeg:∀ p,c p≠0 → d ≤ p.val.val) {δ M ρ gap:ℝ}
    (hδ:0<δ) (hM:0 ≤ M) (hρ:0<ρ) (hgap:0<gap)
    (hρgap:ρ ≤ (gap/Real.sqrt (secondCovariance c 1))/2) (q:ℝ) (hq:0 ≤ q) :
    ∃ Cq:ℝ,0<Cq ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x y v:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ))
      (_hv:‖v‖=1) (_hvtan:inner ℝ v x=0) (e:Fin (n+1)→Vector (n+3))
      (_he:Orthonormal ℝ e) (_htanx:∀ i,inner ℝ (e i) x=0) (_htany:∀ i,inner ℝ (e i) y=0)
      (_hve:∀ i,inner ℝ (e i) v=0) (f g:Fin ℓ→Vector (n+3)) (_hg:Orthonormal ℝ g)
      (_hr:|overlap x y| ≤ 1)
      (_hA:Surjective (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)))
      (_hinv:‖(gram (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g))).inverse‖ ≤ 1/δ)
      (w:WithLp 2 (ValueObservationSpace ℓ×ValueObservationSpace ℓ)) (_hw:‖w‖ ≤ M*Real.sqrt (n+3:ℕ))
      (k:ℝ),2*Real.sqrt (secondCovariance c 1)+gap ≤ k →
      let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
      let b:=secondCovariance c 1
      let κ:=scaleFactor n (n+3) b*ρ
      let F:=fun J=>inner ℝ (actualObservation (commonRowCLM c x e v) J)
        (clippedInverseOperator k κ (hessianMatrix c x e J) (actualObservation (commonRowCLM c x e v) J))-
          b*physicalResolvent b k
      Integrable (fun J=>|F J|^q) (coefficientKernel A w) ∧
      (∫ J,|F J|^q ∂coefficientKernel A w) ≤ Cq*(|overlap x y|^(d-2)+1/Real.sqrt (n+3:ℕ))^q:=by
  let b:=secondCovariance c 1
  let L:=(Real.sqrt (b/3)*ρ)⁻¹
  let C:=profileBound c^2/δ
  let D:=profileBound c*M/δ
  let Cr:=physicalQuadraticMomentConstant b C D L q
  have hLp:0<L:=by dsimp only [L,b];positivity
  have hC:0 ≤ C:=by dsimp only [C];positivity
  have hD:0 ≤ D:=by dsimp only [D];positivity [profileBound_pos c]
  have hQc:=quadraticMomentConstant_pos q
  have hNC:0<gaussianNormRealMomentConstant q (Real.sqrt b) (Real.sqrt b):=by
    unfold gaussianNormRealMomentConstant;positivity
  have hbp:0<b:=hb
  have hCr:0<Cr:=by
    dsimp only [Cr,physicalQuadraticMomentConstant]
    positivity
  obtain ⟨Ct,hCt,hTrace⟩:=physical_covariance_trace_uniform_q_rate 2 hb hgap hρ hρgap q hq
  refine ⟨(2:ℝ)^q*(Cr+Ct*(3:ℝ)^q),by positivity,?_⟩
  filter_upwards [hTrace] with n hn
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f g hg hr hA hinv w hw k hk
  dsimp only
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let η:=coefficientKernel A w
  let κ:=scaleFactor n (n+3) b*ρ
  let T:=fun J=>clippedInverseOperator k κ (hessianMatrix c x e J)
  let Q:=fun J=>inner ℝ (actualObservation (commonRowCLM c x e v) J)
    (T J (actualObservation (commonRowCLM c x e v) J))
  let F:=fun J=>Q J-b*physicalResolvent b k
  let G:=fun J=>Q J-(b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1))) (T J).toLinearMap
  let Φ:=fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>|physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k|^q
  have hSpec:=hn k hk
  have hΦ:Measurable Φ:=((physicalCovarianceTrace_measurable n 2 b k ρ).sub_const _).abs.pow_const q
  have hLaw:=posterior_common_matrix_value_hasLaw (by omega : 0<n+3) c hc
    (fun p hp=>le_trans hd (hdeg p hp)) x y hx e he htanx htany f g w
  have hEq (J:Disorder (n+3) P):|F J-G J|^q=Φ (hessianMatrix c x e J):=by
    have heq:F J-G J=(b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1))) (T J).toLinearMap-b*physicalResolvent b k:=by
      dsimp only [F,G];ring
    rw [heq]
    dsimp only [Φ]
    rw [physicalCovarianceTrace_eq_operator_trace n 2 hb.le k ρ]
  have hDiff:Integrable (fun J=>|F J-G J|^q) η:=by
    simpa only [Function.comp_def,hEq] using hLaw.integrable_comp (f:=Φ) hSpec.1
  have hDI:(∫ J,|F J-G J|^q ∂η) ≤ Ct/(n+1:ℝ)^q:=by
    have hh:=hLaw.integral_comp (f:=Φ) hΦ.aestronglyMeasurable
    simp only [Function.comp_def,←hEq] at hh
    exact hh.trans_le hSpec.2
  have hRow:=actual_common_clipped_row_value_q_moment c hc hb hd hdeg x y v hx hy hv hvtan
    e he htanx htany hve f g hg hr hδ hM hρ hA hinv w hw k q hq
  have hκ:0<κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hRM:Measurable (actualObservation (commonRowCLM c x e v)):=actual_linearObservation_measurable _
  have hTM:Measurable T:=(clippedInverseOperator_measurable (n+1) k hκ).comp (tensor_hessianMatrix_measurable c x e)
  have hEval:Measurable (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2):=
    (show Continuous (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2) from by fun_prop).measurable
  have hF:Measurable F:=(hRM.inner (hEval.comp (hTM.prodMk hRM))).sub_const _
  have hFinal:=integral_absolute_moment_difference η F G hF q hq hRow.1 hDiff
  refine ⟨hFinal.1,hFinal.2.trans ?_⟩
  let ε:=|overlap x y|^(d-2)+1/Real.sqrt (n+3:ℕ)
  have hε:0 ≤ ε:=by dsimp only [ε];positivity
  have hN:(1/(n+1:ℝ)) ≤ 3*ε:=by
    have hh:=SchurDimensionRates.inverse_dimension_le_ambient_inverse_sqrt n (C:=1) (by norm_num)
    dsimp only [ε]
    simp only [mul_one,div_eq_mul_inv] at hh ⊢
    nlinarith [pow_nonneg (abs_nonneg (overlap x y)) (d-2)]
  have hNq:(1/(n+1:ℝ))^q ≤ (3:ℝ)^q*ε^q:=by
    simpa only [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hε] using
      Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/(n+1:ℝ)) hN hq
  have hTraceScale:Ct/(n+1:ℝ)^q ≤ Ct*(3:ℝ)^q*ε^q:=by
    rw [show Ct/(n+1:ℝ)^q=Ct*(1/(n+1:ℝ))^q by
      rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 1) (by positivity),Real.one_rpow];ring]
    exact (mul_le_mul_of_nonneg_left hNq hCt.le).trans_eq (by ring)
  have hRowBound:(∫ J,|G J|^q ∂η) ≤ Cr*ε^q:=hRow.2
  calc
    _ ≤ (2:ℝ)^q*(Cr*ε^q+Ct*(3:ℝ)^q*ε^q):=
      mul_le_mul_of_nonneg_left (add_le_add hRowBound (hDI.trans hTraceScale)) (by positivity)
    _=_:=by dsimp only [ε];ring

end
end SlowEquilibration.SphericalCommonHessianRegression
