-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianClippedRowMeanSquare
public import SlowEquilibration.PosteriorCommonInverseTrace
public import SlowEquilibration.QuadraticDifferenceMeanSquare
public import SlowEquilibration.SphericalLinearObservationMeasurable

/-! Actual original posterior row quadratic error around the literal
physical semicircle term b*m_b(k), with no supplied trace limit. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity NormalizedPairObservations
open PairObservationNormBounds GOEClippedResolvent GOEScaling BoundedQuadraticConvergence
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Actual mixed row error combines its proved covariance noise
with the exact genuine physical GOE inverse-trace error. -/
theorem actual_common_physical_row_mixed_mse {n P ℓ d : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1) (hd : 3 ≤ d)
    (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y v : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (hy : ‖y‖^2=(n+3:ℕ))
    (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (e : Fin (n+1) → Vector (n+3))
    (he : Orthonormal ℝ e) (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hve : ∀ i,inner ℝ (e i) v=0) (f g : Fin ℓ → Vector (n+3)) (hg : Orthonormal ℝ g)
    (hr : |overlap x y| ≤ 1) {δ M ρ : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hA : Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)))
    (hinv : ‖(gram (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (MixedObservationSpace ℓ×MixedObservationSpace ℓ)) (hw : ‖w‖ ≤ M*Real.sqrt (n+3:ℕ)) (t : ℝ) :
    let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
    let B:=commonRowCLM c x e v
    let b:=secondCovariance c 1
    let κ:=scaleFactor n (n+3) b*ρ
    let L:=(Real.sqrt (b/3)*ρ)⁻¹
    let C:=profileBound c^2/δ
    let D:=profileBound c*M/δ
    let F:=fun J=>(inner ℝ (actualObservation B J)
      (clippedInverseOperator t κ (hessianMatrix c x e J) (actualObservation B J))-b*physicalResolvent b t)^2
    Integrable F (coefficientKernel A w) ∧ (∫ J,F J ∂coefficientKernel A w) ≤
      2*L^2*(8*b^2/(n+3:ℕ)+(4*C^2+16*b*D^2+4*D^4)*|overlap x y|^2)+
        2*(∫ W,(physicalCovarianceTrace n 2 b t ρ W-b*physicalResolvent b t)^2 ∂goeLaw (n+1) (n+3) b) := by
  dsimp only
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  let B:=commonRowCLM c x e v
  let η:=coefficientKernel A w
  let b:=secondCovariance c 1
  let κ:=scaleFactor n (n+3) b*ρ
  let L:=(Real.sqrt (b/3)*ρ)⁻¹
  let C:=profileBound c^2/δ
  let D:=profileBound c*M/δ
  let T:=fun J=>clippedInverseOperator t κ (hessianMatrix c x e J)
  let Q:=fun J=>inner ℝ (actualObservation B J) (T J (actualObservation B J))
  let F:=fun J=>Q J-b*physicalResolvent b t
  let G:=fun J=>Q J-(b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1))) (T J).toLinearMap
  have hκ : 0 < κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hRowM : Measurable (actualObservation B):=actual_linearObservation_measurable B
  have hTM : Measurable T:=(clippedInverseOperator_measurable (n+1) t hκ).comp (tensor_hessianMatrix_measurable c x e)
  have hEval : Measurable (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2) :=
    (show Continuous (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2) from by fun_prop).measurable
  have hF : Measurable F:=(hRowM.inner (hEval.comp (hTM.prodMk hRowM))).sub_const _
  have hRow:=actual_common_clipped_row_mixed_mse c hc hb hd hdeg x y v hx hy hv hvtan e he htanx htany hve f g hg hr hδ hM hρ hA hinv w hw t
  have hTrace:=posterior_covariance_trace_error_mixed c hc hb (fun p hp=>le_trans hd (hdeg p hp)) x y hx e he htanx htany f g w t hρ
  have hEqD (J:Disorder (n+3) P) : (F J-G J)^2=
      ((b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1))) (T J).toLinearMap-b*physicalResolvent b t)^2 := by
    dsimp only [F,G]
    ring
  have hDI : Integrable (fun J=>(F J-G J)^2) η:=by
    simpa only [hEqD] using hTrace.1
  have hFinal:=integral_square_difference_bound η F G hF hRow.1 hDI
  refine ⟨hFinal.1,?_⟩
  have hDE : (∫ J,(F J-G J)^2 ∂η)=
      (∫ W,(physicalCovarianceTrace n 2 b t ρ W-b*physicalResolvent b t)^2 ∂goeLaw (n+1) (n+3) b) := by
    simpa only [hEqD] using hTrace.2
  rw [hDE] at hFinal
  have hR : (∫ J,G J^2 ∂η) ≤ L^2*(8*b^2/(n+3:ℕ)+(4*C^2+16*b*D^2+4*D^4)*|overlap x y|^2):=hRow.2
  apply hFinal.2.trans
  exact add_le_add (by convert mul_le_mul_of_nonneg_left hR (by norm_num : (0:ℝ)≤2) using 1; ring) le_rfl

/-- Actual value row error combines its proved covariance noise
with the exact genuine physical GOE inverse-trace error. -/
theorem actual_common_physical_row_value_mse {n P ℓ d : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1) (hd : 3 ≤ d)
    (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y v : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (hy : ‖y‖^2=(n+3:ℕ))
    (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (e : Fin (n+1) → Vector (n+3))
    (he : Orthonormal ℝ e) (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hve : ∀ i,inner ℝ (e i) v=0) (f g : Fin ℓ → Vector (n+3)) (hg : Orthonormal ℝ g)
    (hr : |overlap x y| ≤ 1) {δ M ρ : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hA : Surjective (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)))
    (hinv : ‖(gram (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (ValueObservationSpace ℓ×ValueObservationSpace ℓ)) (hw : ‖w‖ ≤ M*Real.sqrt (n+3:ℕ)) (t : ℝ) :
    let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
    let B:=commonRowCLM c x e v
    let b:=secondCovariance c 1
    let κ:=scaleFactor n (n+3) b*ρ
    let L:=(Real.sqrt (b/3)*ρ)⁻¹
    let C:=profileBound c^2/δ
    let D:=profileBound c*M/δ
    let F:=fun J=>(inner ℝ (actualObservation B J)
      (clippedInverseOperator t κ (hessianMatrix c x e J) (actualObservation B J))-b*physicalResolvent b t)^2
    Integrable F (coefficientKernel A w) ∧ (∫ J,F J ∂coefficientKernel A w) ≤
      2*L^2*(8*b^2/(n+3:ℕ)+(4*C^2+16*b*D^2+4*D^4)*|overlap x y|^2)+
        2*(∫ W,(physicalCovarianceTrace n 2 b t ρ W-b*physicalResolvent b t)^2 ∂goeLaw (n+1) (n+3) b) := by
  dsimp only
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let B:=commonRowCLM c x e v
  let η:=coefficientKernel A w
  let b:=secondCovariance c 1
  let κ:=scaleFactor n (n+3) b*ρ
  let L:=(Real.sqrt (b/3)*ρ)⁻¹
  let C:=profileBound c^2/δ
  let D:=profileBound c*M/δ
  let T:=fun J=>clippedInverseOperator t κ (hessianMatrix c x e J)
  let Q:=fun J=>inner ℝ (actualObservation B J) (T J (actualObservation B J))
  let F:=fun J=>Q J-b*physicalResolvent b t
  let G:=fun J=>Q J-(b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1))) (T J).toLinearMap
  have hκ : 0 < κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hRowM : Measurable (actualObservation B):=actual_linearObservation_measurable B
  have hTM : Measurable T:=(clippedInverseOperator_measurable (n+1) t hκ).comp (tensor_hessianMatrix_measurable c x e)
  have hEval : Measurable (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2) :=
    (show Continuous (fun p:(EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))=>p.1 p.2) from by fun_prop).measurable
  have hF : Measurable F:=(hRowM.inner (hEval.comp (hTM.prodMk hRowM))).sub_const _
  have hRow:=actual_common_clipped_row_value_mse c hc hb hd hdeg x y v hx hy hv hvtan e he htanx htany hve f g hg hr hδ hM hρ hA hinv w hw t
  have hTrace:=posterior_covariance_trace_error_value c hc hb (fun p hp=>le_trans hd (hdeg p hp)) x y hx e he htanx htany f g w t hρ
  have hEqD (J:Disorder (n+3) P) : (F J-G J)^2=
      ((b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1))) (T J).toLinearMap-b*physicalResolvent b t)^2 := by
    dsimp only [F,G]
    ring
  have hDI : Integrable (fun J=>(F J-G J)^2) η:=by
    simpa only [hEqD] using hTrace.1
  have hFinal:=integral_square_difference_bound η F G hF hRow.1 hDI
  refine ⟨hFinal.1,?_⟩
  have hDE : (∫ J,(F J-G J)^2 ∂η)=
      (∫ W,(physicalCovarianceTrace n 2 b t ρ W-b*physicalResolvent b t)^2 ∂goeLaw (n+1) (n+3) b) := by
    simpa only [hEqD] using hTrace.2
  rw [hDE] at hFinal
  have hR : (∫ J,G J^2 ∂η) ≤ L^2*(8*b^2/(n+3:ℕ)+(4*C^2+16*b*D^2+4*D^4)*|overlap x y|^2):=hRow.2
  apply hFinal.2.trans
  exact add_le_add (by convert mul_le_mul_of_nonneg_left hR (by norm_num : (0:ℝ)≤2) using 1; ring) le_rfl

end
end SlowEquilibration.SphericalCommonHessianRegression
