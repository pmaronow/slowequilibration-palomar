-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianPhysicalRowMeanSquare
public import SlowEquilibration.CommonHessianActualCornerMeanSquare
public import SlowEquilibration.PhysicalSchurMultiplier
public import SlowEquilibration.QuadraticDifferenceMeanSquare

/-! Genuine actual one-border clipped Schur concentration. The original
tensor-posterior corner and row estimates are combined with the proved
physical GOE covariance-trace error; no Schur concentration is assumed. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance GaussianObservationCoercivity
open NormalizedPairObservations PairHessianMean PairObservationNormBounds GaussianQuadraticVariance
open GOEClippedResolvent GOEScaling CanonicalGOERealization BoundedQuadraticConvergence
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- The literal clipped Schur complement of the actual common Hessian
bordered by the chosen unit tangent direction. -/
def actualClippedSchurFactor {N P m : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin m → Vector N) (v : Vector N) (k κ : ℝ) (J : Disorder N P) : ℝ :=
  k-actualObservation (cornerCLM c x v) J-
    inner ℝ (actualObservation (commonRowCLM c x e v) J)
      (clippedInverseOperator k κ (hessianMatrix c x e J) (actualObservation (commonRowCLM c x e v) J))

lemma actualClippedSchurFactor_measurable {N P m : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin m → Vector N) (v : Vector N) (k : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Measurable (actualClippedSchurFactor c x e v k κ) := by
  have hW : Measurable (hessianMatrix c x e):=tensor_hessianMatrix_measurable c x e
  have hS:=(clippedInverseOperator_measurable m k hκ).comp hW
  have hR:=actual_linearObservation_measurable (commonRowCLM c x e v)
  have hC:=actual_linearObservation_measurable (cornerCLM c x v)
  have hEval : Measurable (fun p:(EuclideanSpace ℝ (Fin m)→L[ℝ]EuclideanSpace ℝ (Fin m))×EuclideanSpace ℝ (Fin m)=>p.1 p.2) :=
    (show Continuous (fun p:(EuclideanSpace ℝ (Fin m)→L[ℝ]EuclideanSpace ℝ (Fin m))×EuclideanSpace ℝ (Fin m)=>p.1 p.2) from by fun_prop).measurable
  exact (measurable_const.sub hC).sub (hR.inner (hEval.comp (hS.prodMk hR)))

/-- Actual full coefficient mixed-pair Schur L² bound. All constants are
fixed before N; the final term is an actual GOE error with proved compact
L² convergence, rather than an asymptotic hypothesis. -/
theorem actual_common_clipped_schur_mixed_mse {n P ℓ d : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1) (hd : 4 ≤ d)
    (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y v : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (hy : ‖y‖^2=(n+3:ℕ))
    (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (e : Fin (n+1) → Vector (n+3))
    (he : Orthonormal ℝ e) (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hve : ∀ i,inner ℝ (e i) v=0) (f g : Fin ℓ → Vector (n+3)) (hg : Orthonormal ℝ g)
    (hr : |overlap x y| ≤ 1) {δ M ρ : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hA : Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)))
    (hinv : ‖(gram (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (MixedObservationSpace ℓ×MixedObservationSpace ℓ)) (hw : ‖w‖ ≤ M*Real.sqrt (n+3:ℕ)) (k : ℝ) :
    let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
    let b:=secondCovariance c 1
    let κ:=scaleFactor n (n+3) b*ρ
    let L:=(Real.sqrt (b/3)*ρ)⁻¹
    let C:=profileBound c^2/δ
    let D:=profileBound c*M/δ
    let F:=fun J=>actualClippedSchurFactor c x e v k κ J-physicalSchurMultiplier b k
    Integrable (fun J=>F J^2) (coefficientKernel A w) ∧
      (∫ J,F J^2 ∂coefficientKernel A w) ≤
        2*(2*b/(n+3:ℕ)+(7*D)^2*|overlap x y|^2)+
          4*L^2*(8*b^2/(n+3:ℕ)+(4*C^2+16*b*D^2+4*D^4)*|overlap x y|^2)+
          4*(∫ W,(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2
            ∂goeLaw (n+1) (n+3) b) := by
  dsimp only
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  let b:=secondCovariance c 1
  let κ:=scaleFactor n (n+3) b*ρ
  let μ:=coefficientKernel A w
  let F:=fun J=>actualClippedSchurFactor c x e v k κ J-physicalSchurMultiplier b k
  let G:=fun J:Disorder (n+3) P=>-actualObservation (cornerCLM c x v) J
  let R:=fun J:Disorder (n+3) P=>inner ℝ (actualObservation (commonRowCLM c x e v) J)
      (clippedInverseOperator k κ (hessianMatrix c x e J) (actualObservation (commonRowCLM c x e v) J))-b*physicalResolvent b k
  have hCorner:=actual_common_corner_mixed_mse (by omega : 0 < n+3) c hc
    (fun p hp=>le_trans hd (hdeg p hp)) x y v hx hy hv hvtan f g hg hr hδ hM hA hinv w hw
  have hRow:=actual_common_physical_row_mixed_mse c hc hb (by omega : 3 ≤ d) hdeg
    x y v hx hy hv hvtan e he htanx htany hve f g hg hr hδ hM hρ hA hinv w hw k
  have hκ : 0 < κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hF : Measurable F:=(actualClippedSchurFactor_measurable c x e v k hκ).sub_const _
  have hG : Integrable (fun J=>G J^2) μ:=by simpa only [G,neg_sq] using hCorner.1
  have heq (J) : (F J-G J)^2=R J^2 := by
    dsimp only [F,G,R,actualClippedSchurFactor,physicalSchurMultiplier]
    ring
  have hDiff : Integrable (fun J=>(F J-G J)^2) μ:=by simpa only [heq] using hRow.1
  have hh:=integral_square_difference_bound μ F G hF hG hDiff
  refine ⟨hh.1,?_⟩
  have hCorner' : (∫ J,(actualObservation (cornerCLM c x v) J)^2 ∂μ) ≤
      2*b/(n+3:ℕ)+(7*(profileBound c*M/δ))^2*|overlap x y|^2 := by
    convert hCorner.2 using 1;ring
  calc
    _ ≤ 2*(∫ J,(actualObservation (cornerCLM c x v) J)^2 ∂μ)+2*(∫ J,R J^2 ∂μ) := by
      simpa only [heq,G,neg_sq] using hh.2
    _ ≤ 2*(2*b/(n+3:ℕ)+(7*(profileBound c*M/δ))^2*|overlap x y|^2)+
      2*(2*(Real.sqrt (b/3)*ρ)⁻¹^2*(8*b^2/(n+3:ℕ)+
        (4*(profileBound c^2/δ)^2+16*b*(profileBound c*M/δ)^2+4*(profileBound c*M/δ)^4)*|overlap x y|^2)+
          2*(∫ W,(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2 ∂goeLaw (n+1) (n+3) b)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hCorner' (by norm_num))
        (mul_le_mul_of_nonneg_left hRow.2 (by norm_num))
    _=_:=by ring

/-- Proper value-only posterior companion for the same literal Schur
factor, retaining the same actual physical GOE covariance-trace error. -/
theorem actual_common_clipped_schur_value_mse {n P ℓ d : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1) (hd : 4 ≤ d)
    (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y v : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (hy : ‖y‖^2=(n+3:ℕ))
    (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (e : Fin (n+1) → Vector (n+3))
    (he : Orthonormal ℝ e) (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hve : ∀ i,inner ℝ (e i) v=0) (f g : Fin ℓ → Vector (n+3)) (hg : Orthonormal ℝ g)
    (hr : |overlap x y| ≤ 1) {δ M ρ : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hA : Surjective (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)))
    (hinv : ‖(gram (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (ValueObservationSpace ℓ×ValueObservationSpace ℓ)) (hw : ‖w‖ ≤ M*Real.sqrt (n+3:ℕ)) (k : ℝ) :
    let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
    let b:=secondCovariance c 1
    let κ:=scaleFactor n (n+3) b*ρ
    let L:=(Real.sqrt (b/3)*ρ)⁻¹
    let C:=profileBound c^2/δ
    let D:=profileBound c*M/δ
    let F:=fun J=>actualClippedSchurFactor c x e v k κ J-physicalSchurMultiplier b k
    Integrable (fun J=>F J^2) (coefficientKernel A w) ∧
      (∫ J,F J^2 ∂coefficientKernel A w) ≤
        2*(2*b/(n+3:ℕ)+(7*D)^2*|overlap x y|^2)+
          4*L^2*(8*b^2/(n+3:ℕ)+(4*C^2+16*b*D^2+4*D^4)*|overlap x y|^2)+
          4*(∫ W,(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2
            ∂goeLaw (n+1) (n+3) b) := by
  dsimp only
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let b:=secondCovariance c 1
  let κ:=scaleFactor n (n+3) b*ρ
  let μ:=coefficientKernel A w
  let F:=fun J=>actualClippedSchurFactor c x e v k κ J-physicalSchurMultiplier b k
  let G:=fun J:Disorder (n+3) P=>-actualObservation (cornerCLM c x v) J
  let R:=fun J:Disorder (n+3) P=>inner ℝ (actualObservation (commonRowCLM c x e v) J)
      (clippedInverseOperator k κ (hessianMatrix c x e J) (actualObservation (commonRowCLM c x e v) J))-b*physicalResolvent b k
  have hCorner:=actual_common_corner_value_mse (by omega : 0 < n+3) c hc
    (fun p hp=>le_trans hd (hdeg p hp)) x y v hx hy hv hvtan f g hg hr hδ hM hA hinv w hw
  have hRow:=actual_common_physical_row_value_mse c hc hb (by omega : 3 ≤ d) hdeg
    x y v hx hy hv hvtan e he htanx htany hve f g hg hr hδ hM hρ hA hinv w hw k
  have hκ : 0 < κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hF : Measurable F:=(actualClippedSchurFactor_measurable c x e v k hκ).sub_const _
  have hG : Integrable (fun J=>G J^2) μ:=by simpa only [G,neg_sq] using hCorner.1
  have heq (J) : (F J-G J)^2=R J^2 := by
    dsimp only [F,G,R,actualClippedSchurFactor,physicalSchurMultiplier]
    ring
  have hDiff : Integrable (fun J=>(F J-G J)^2) μ:=by simpa only [heq] using hRow.1
  have hh:=integral_square_difference_bound μ F G hF hG hDiff
  refine ⟨hh.1,?_⟩
  have hCorner' : (∫ J,(actualObservation (cornerCLM c x v) J)^2 ∂μ) ≤
      2*b/(n+3:ℕ)+(7*(profileBound c*M/δ))^2*|overlap x y|^2 := by
    convert hCorner.2 using 1;ring
  calc
    _ ≤ 2*(∫ J,(actualObservation (cornerCLM c x v) J)^2 ∂μ)+2*(∫ J,R J^2 ∂μ) := by
      simpa only [heq,G,neg_sq] using hh.2
    _ ≤ 2*(2*b/(n+3:ℕ)+(7*(profileBound c*M/δ))^2*|overlap x y|^2)+
      2*(2*(Real.sqrt (b/3)*ρ)⁻¹^2*(8*b^2/(n+3:ℕ)+
        (4*(profileBound c^2/δ)^2+16*b*(profileBound c*M/δ)^2+4*(profileBound c*M/δ)^4)*|overlap x y|^2)+
          2*(∫ W,(physicalCovarianceTrace n 2 b k ρ W-b*physicalResolvent b k)^2 ∂goeLaw (n+1) (n+3) b)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hCorner' (by norm_num))
        (mul_le_mul_of_nonneg_left hRow.2 (by norm_num))
    _=_:=by ring

end
end SlowEquilibration.SphericalCommonHessianRegression
