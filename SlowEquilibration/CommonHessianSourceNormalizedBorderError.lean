-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianWeightedErrorTransfer

/-! Exact source all-q determinant approximation in the Schur-weighted
bulk normalization w(k)*mu_{N-2,N}. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open GaussianObservationCoercivity
open NormalizedPairObservations PairObservationTargets PairObservationSmallOverlap
open GOEClippedResolvent GOEPhysicalPotential GOERawMoments GaussianQuadraticVariance
open PhysicalCommonBorderMoments
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

/-- Literal source mixed determinant approximation, with the actual physical normalizer. -/
theorem source_mixed_normalized_border_q_error (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap)
    (q:ℝ) (hq:1 ≤ q) :
    ∃ η Cq:ℝ,0<η ∧ 0<Cq ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x y v:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ))
      (_hv:‖v‖=1) (_hvtan:inner ℝ v x=0) (e:Fin (n+1)→Vector (n+3))
      (_he:Orthonormal ℝ e) (_htanx:∀ i,inner ℝ (e i) x=0) (_htany:∀ i,inner ℝ (e i) y=0)
      (_hve:∀ i,inner ℝ (e i) v=0)
      (f g:Fin ℓ→Vector (n+3)) (_hf:Orthonormal ℝ f) (_hg:Orthonormal ℝ g)
      (_hftan:∀ i,inner ℝ (f i) x=0) (_hgtan:∀ i,inner ℝ (g i) y=0)
      (h1 k1 h2 k2:ℝ), |h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1)+gap ≤ k1 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
      let w:=mixedPairTarget (n+3) ℓ h1 k1 h2 k2
      let b:=secondCovariance c 1
      let m:=physicalMean n (n+3) b k1
      let s:=physicalSchurMultiplier b k1
      let D:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v))
        (actualObservation (commonRowCLM c x e v)) J/(s*m)
      let B:=fun J=>matrixAbsoluteDet n k1 (hessianMatrix c x e J)/m
      Integrable (fun J=>|D J-B J|^q) (coefficientKernel A w) ∧
      (∫ J,|D J-B J|^q ∂coefficientKernel A w) ≤ Cq*(|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ))^q :=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=secondCovariance c 1
  have hb:0<b:=by
    dsimp only [b,c]
    rw [secondCovariance_center,secondCovariance_mixture]
    exact mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨η,C,hη,hC,hAll⟩:=source_mixed_full_border_q_error μ hQ hnp hd hM hgap q hq
  refine ⟨η,C/(Real.sqrt b)^q,hη,by positivity,?_⟩
  filter_upwards [hAll] with n hn
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f g hf hg hftan hgtan h1 k1 h2 k2 hh1 hk1 hh2 hk2 hr hk
  dsimp only
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  let w:=mixedPairTarget (n+3) ℓ h1 k1 h2 k2
  let P:=coefficientKernel A w
  let m:=physicalMean n (n+3) b k1
  let s:=physicalSchurMultiplier b k1
  let D:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v))
    (actualObservation (commonRowCLM c x e v)) J/m
  let B:=fun J=>matrixAbsoluteDet n k1 (hessianMatrix c x e J)/m
  let ε:=|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hs:0<s:=physicalSchurMultiplier_pos hb (by linarith)
  have hst:Real.sqrt b ≤ s:=by
    have hh:=(physicalSchurMultiplier_bounds hb (by linarith : 2*Real.sqrt b<k1)).1
    dsimp only [s]
    linarith
  have hE:=hn ℓ x y v hx hy hv hvtan e he htanx htany hve f g hf hg hftan hgtan h1 k1 h2 k2 hh1 hk1 hh2 hk2 hr hk
  have hRate:=weighted_error_q_transfer P D B hs (Real.sqrt_pos.mpr hb) hst
    (by linarith : 0 ≤ q) hC.le (by positivity) hE.1 hE.2
  have hEq (J):D J/s=fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v))
      (actualObservation (commonRowCLM c x e v)) J/(s*m):=by
    dsimp only [D]
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  simpa only [hEq] using hRate

/-- Literal source value determinant approximation, with the actual physical normalizer. -/
theorem source_value_normalized_border_q_error (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap)
    (q:ℝ) (hq:1 ≤ q) :
    ∃ η Cq:ℝ,0<η ∧ 0<Cq ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x y v:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ))
      (_hv:‖v‖=1) (_hvtan:inner ℝ v x=0) (e:Fin (n+1)→Vector (n+3))
      (_he:Orthonormal ℝ e) (_htanx:∀ i,inner ℝ (e i) x=0) (_htany:∀ i,inner ℝ (e i) y=0)
      (_hve:∀ i,inner ℝ (e i) v=0)
      (f g:Fin ℓ→Vector (n+3)) (_hf:Orthonormal ℝ f) (_hg:Orthonormal ℝ g)
      (_hftan:∀ i,inner ℝ (f i) x=0) (_hgtan:∀ i,inner ℝ (g i) y=0)
      (h1 h2 k1:ℝ), |h1| ≤ M → |h2| ≤ M → |k1| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1)+gap ≤ k1 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
      let w:=valuePairTarget (n+3) ℓ h1 h2
      let b:=secondCovariance c 1
      let m:=physicalMean n (n+3) b k1
      let s:=physicalSchurMultiplier b k1
      let D:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v))
        (actualObservation (commonRowCLM c x e v)) J/(s*m)
      let B:=fun J=>matrixAbsoluteDet n k1 (hessianMatrix c x e J)/m
      Integrable (fun J=>|D J-B J|^q) (coefficientKernel A w) ∧
      (∫ J,|D J-B J|^q ∂coefficientKernel A w) ≤ Cq*(|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ))^q :=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=secondCovariance c 1
  have hb:0<b:=by
    dsimp only [b,c]
    rw [secondCovariance_center,secondCovariance_mixture]
    exact mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨η,C,hη,hC,hAll⟩:=source_value_full_border_q_error μ hQ hd hM hgap q hq
  refine ⟨η,C/(Real.sqrt b)^q,hη,by positivity,?_⟩
  filter_upwards [hAll] with n hn
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f g hf hg hftan hgtan h1 h2 k1 hh1 hh2 hk1 hr hk
  dsimp only
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let w:=valuePairTarget (n+3) ℓ h1 h2
  let P:=coefficientKernel A w
  let m:=physicalMean n (n+3) b k1
  let s:=physicalSchurMultiplier b k1
  let D:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v))
    (actualObservation (commonRowCLM c x e v)) J/m
  let B:=fun J=>matrixAbsoluteDet n k1 (hessianMatrix c x e J)/m
  let ε:=|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hs:0<s:=physicalSchurMultiplier_pos hb (by linarith)
  have hst:Real.sqrt b ≤ s:=by
    have hh:=(physicalSchurMultiplier_bounds hb (by linarith : 2*Real.sqrt b<k1)).1
    dsimp only [s]
    linarith
  have hE:=hn ℓ x y v hx hy hv hvtan e he htanx htany hve f g hf hg hftan hgtan h1 h2 k1 hh1 hh2 hk1 hr hk
  have hRate:=weighted_error_q_transfer P D B hs (Real.sqrt_pos.mpr hb) hst
    (by linarith : 0 ≤ q) hC.le (by positivity) hE.1 hE.2
  have hEq (J):D J/s=fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v))
      (actualObservation (commonRowCLM c x e v)) J/(s*m):=by
    dsimp only [D]
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  simpa only [hEq] using hRate

end
end SlowEquilibration.SphericalCommonHessianRegression
