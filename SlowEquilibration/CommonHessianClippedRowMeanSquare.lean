-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianClippedInverseField
public import SlowEquilibration.GaussianQuadraticPhysicalError

/-! Actual mixed/proper-value common-row quadratic L² error for the
literal clipped common Hessian inverse, with fixed constants before N. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance GaussianObservationCoercivity
open NormalizedPairObservations PairHessianMean PairObservationNormBounds GaussianQuadraticVariance
open GOEClippedResolvent GOEScaling CanonicalGOERealization
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Literal original tensor-posterior mixed row error for the actual
clipped common Hessian inverse. Constants depend only on c,δ,M,rho;
there is no covariance, independence or quadratic estimate premise. -/
theorem actual_common_clipped_row_mixed_mse {n P ℓ d : ℕ} (c : Degree P → ℝ)
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
      (clippedInverseOperator t κ (hessianMatrix c x e J) (actualObservation B J))-
        (b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1)))
          (clippedInverseOperator t κ (hessianMatrix c x e J)).toLinearMap)^2
    Integrable F (coefficientKernel A w) ∧ (∫ J,F J ∂coefficientKernel A w) ≤
      L^2*(8*b^2/(n+3:ℕ)+(4*C^2+16*b*D^2+4*D^4)*|overlap x y|^2) := by
  dsimp only
  let b:=secondCovariance c 1
  let κ:=scaleFactor n (n+3) b*ρ
  let L:=(Real.sqrt (b/3)*ρ)⁻¹
  let S:=commonClippedInverseField (m:=n+1) t κ
  have hκ : 0 < κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hL : 0 ≤ L:=by positivity
  have hSN (z:CommonBulkPairSpace (n+1)) : ‖S z‖ ≤ L:=by
    simpa only [S,κ,L,b,Nat.cast_ofNat,show (2+1:ℝ)=3 by norm_num] using physical_commonClippedInverseField_norm_le n 2 hb hρ t z
  have hT:=actual_common_row_mixed_bulk_operator_mse (by omega : 0 < n+3) c hc hb hd hdeg
    x y v v hx hy hv hvtan e he htanx htany hve hve f g hg hr hδ hA hinv w hM hL hw S
    (commonClippedInverseField_measurable (n+1) t hκ) (fun z=>commonClippedInverseField_symmetric t κ z) hSN
  simp only [S,commonClippedInverseField_actual] at hT
  refine ⟨hT.1,hT.2.trans ?_⟩
  have hCoef : profileBound c^2/((n+3:ℕ)*δ)=(profileBound c^2/δ)/(n+3:ℕ) := by ring
  rw [hCoef]
  exact quadraticErrorBound_small_overlap (by omega : 0 < n+3) (by omega : n+1 ≤ n+3) hd hb.le
    (by positivity : 0 ≤ profileBound c^2/δ) (by positivity [profileBound_pos c] : 0 ≤ profileBound c*M/δ)
    hL (abs_nonneg _) hr

/-- Literal original tensor-posterior value row error for the actual
clipped common Hessian inverse. Constants depend only on c,δ,M,rho;
there is no covariance, independence or quadratic estimate premise. -/
theorem actual_common_clipped_row_value_mse {n P ℓ d : ℕ} (c : Degree P → ℝ)
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
      (clippedInverseOperator t κ (hessianMatrix c x e J) (actualObservation B J))-
        (b/(n+3:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1)))
          (clippedInverseOperator t κ (hessianMatrix c x e J)).toLinearMap)^2
    Integrable F (coefficientKernel A w) ∧ (∫ J,F J ∂coefficientKernel A w) ≤
      L^2*(8*b^2/(n+3:ℕ)+(4*C^2+16*b*D^2+4*D^4)*|overlap x y|^2) := by
  dsimp only
  let b:=secondCovariance c 1
  let κ:=scaleFactor n (n+3) b*ρ
  let L:=(Real.sqrt (b/3)*ρ)⁻¹
  let S:=commonClippedInverseField (m:=n+1) t κ
  have hκ : 0 < κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hL : 0 ≤ L:=by positivity
  have hSN (z:CommonBulkPairSpace (n+1)) : ‖S z‖ ≤ L:=by
    simpa only [S,κ,L,b,Nat.cast_ofNat,show (2+1:ℝ)=3 by norm_num] using physical_commonClippedInverseField_norm_le n 2 hb hρ t z
  have hT:=actual_common_row_value_bulk_operator_mse (by omega : 0 < n+3) c hc hb hd hdeg
    x y v v hx hy hv hvtan e he htanx htany hve hve f g hg hr hδ hA hinv w hM hL hw S
    (commonClippedInverseField_measurable (n+1) t hκ) (fun z=>commonClippedInverseField_symmetric t κ z) hSN
  simp only [S,commonClippedInverseField_actual] at hT
  refine ⟨hT.1,hT.2.trans ?_⟩
  have hCoef : profileBound c^2/((n+3:ℕ)*δ)=(profileBound c^2/δ)/(n+3:ℕ) := by ring
  rw [hCoef]
  exact quadraticErrorBound_small_overlap (by omega : 0 < n+3) (by omega : n+1 ≤ n+3) hd hb.le
    (by positivity : 0 ≤ profileBound c^2/δ) (by positivity [profileBound_pos c] : 0 ≤ profileBound c*M/δ)
    hL (abs_nonneg _) hr

end
end SlowEquilibration.SphericalCommonHessianRegression
