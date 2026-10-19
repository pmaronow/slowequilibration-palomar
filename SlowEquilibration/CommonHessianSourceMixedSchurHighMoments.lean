-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianPhysicalRowHighMoments
public import SlowEquilibration.CommonHessianScalarHighMoments
public import SlowEquilibration.PhysicalZeroGradientCornerSource
public import SlowEquilibration.CommonHessianActualSchurMeanSquare

/-! Sharp source mixed-pair all-q Schur rate under literal physical marks
and simultaneous zero tangent-gradient targets. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open GaussianObservationCoercivity NormalizedPairObservations PairObservationNormBounds
open PairObservationTargets PairObservationSmallOverlap PhysicalZeroGradientCorner
open GaussianQuadraticVariance GOEClippedResolvent GOEScaling
open scoped RealInnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- All-q source clipped Schur approximation with constants fixed before
N, the actual pair, all deterministic tangent frames, and physical marks. -/
theorem source_mixed_clipped_schur_q_rate (μ:FiniteMixture) {Q M gap ρ:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M)
    (hgap:0<gap) (hρ:0<ρ)
    (hρgap:ρ ≤ (gap/Real.sqrt (secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1))/2)
    (q:ℝ) (hq:0 ≤ q) :
    ∃ η Cq:ℝ,0<η ∧ 0<Cq ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x y v:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ))
      (_hv:‖v‖=1) (_hvtan:inner ℝ v x=0) (e:Fin (n+1)→Vector (n+3))
      (_he:Orthonormal ℝ e) (_htanx:∀ i,inner ℝ (e i) x=0) (_htany:∀ i,inner ℝ (e i) y=0)
      (_hve:∀ i,inner ℝ (e i) v=0)
      (f g:Fin ℓ→Vector (n+3)) (_hf:Orthonormal ℝ f) (_hg:Orthonormal ℝ g)
      (_hftan:∀ i,inner ℝ (f i) x=0) (_hgtan:∀ i,inner ℝ (g i) y=0)
      (h1 k1 h2 k2:ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1)+gap ≤ k1 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
      let w:=mixedPairTarget (n+3) ℓ h1 k1 h2 k2
      let b:=secondCovariance c 1
      let κ:=scaleFactor n (n+3) b*ρ
      let F:=fun J=>actualClippedSchurFactor c x e v k1 κ J-physicalSchurMultiplier b k1
      Integrable (fun J=>|F J|^q) (coefficientKernel A w) ∧
      (∫ J,|F J|^q ∂coefficientKernel A w) ≤ Cq*(|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ))^q:=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=secondCovariance c 1
  have hc:∀ p,0 ≤ c p:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hdeg:∀ p,c p≠0 → μ.minDegree ≤ p.val.val:=center_degree_min μ Q
  have hb:0<b:=by
    dsimp only [b,c]
    rw [secondCovariance_center,secondCovariance_mixture]
    exact mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨η0,δ,hη0,hδ,hObs⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hd
  obtain ⟨η1,Cm,hη1,hCm,hMean⟩:=source_mixed_corner_mean μ hQ hnp hd hM
  obtain ⟨Cr,hCr,hRow⟩:=uniform_actual_common_physical_row_mixed_q_rate c hc hb (by omega) hdeg
    hδ (show 0 ≤ 4*M by positivity) hρ hgap hρgap q hq
  have hNC:0<gaussianNormRealMomentConstant q 1 1:=by unfold gaussianNormRealMomentConstant;positivity
  let Cc:=(2:ℝ)^q*(gaussianNormRealMomentConstant q 1 1*(Real.sqrt (2*b))^q+Cm^q)
  have hCc:0<Cc:=by dsimp only [Cc];positivity
  refine ⟨min η0 (min η1 1),(2:ℝ)^q*(Cr+Cc),lt_min hη0 (lt_min hη1 (by norm_num)),by positivity,?_⟩
  filter_upwards [hRow] with n hn
  intro ℓ x y v hx hy hv hvtan e he htanx htany hve f g hf hg hftan hgtan h1 k1 h2 k2 hh1 hk1 hh2 hk2 hr hk
  dsimp only
  have hr0:|overlap x y| ≤ η0:=hr.trans (min_le_left _ _)
  have hr1:|overlap x y| ≤ η1:=hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrOne:|overlap x y| ≤ 1:=hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hObs0:=hObs (n+3) ℓ (by omega) x y hx hy f g hf hg hftan hgtan hr0
  have hA:=hObs0.2.1
  have hinv:=hObs0.2.2
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  let w:=mixedPairTarget (n+3) ℓ h1 k1 h2 k2
  let P:=coefficientKernel A w
  let κ:=scaleFactor n (n+3) b*ρ
  let m0:=cornerCLM c x v (lift A w)
  let C:=fun J=>actualObservation (cornerCLM c x v) J
  let C0:=fun J=>C J-m0
  let R:=fun J=>inner ℝ (actualObservation (commonRowCLM c x e v) J)
    (clippedInverseOperator k1 κ (hessianMatrix c x e J) (actualObservation (commonRowCLM c x e v) J))-b*physicalResolvent b k1
  let F:=fun J=>actualClippedSchurFactor c x e v k1 κ J-physicalSchurMultiplier b k1
  let G:=fun J=>-R J
  let ε:=|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hε:0 ≤ ε:=by dsimp only [ε];positivity
  have hCm0:|m0| ≤ Cm*|overlap x y|^(μ.minDegree-2):=by
    exact hMean (n+3) ℓ (by omega) x y v v hx hy hv hv hvtan hvtan f g hf hg hftan hgtan
      h1 k1 h2 k2 hh1 hk1 hh2 hk2 hr1
  have hCorner:=actual_conditional_centered_corner_q_moment (by omega) c hc hb x hx v hv hvtan A hA w q hq
  have hCMeas:Measurable C:=actual_linearObservation_measurable _
  have hCmom:=integral_absolute_moment_perturbation P C C0 hCMeas q hq hCorner.1
    (show 0 ≤ Cm*|overlap x y|^(μ.minDegree-2) by positivity)
    (fun J=>by rw [show C J-C0 J=m0 by dsimp only [C0];ring];exact hCm0)
  have hScale:(Real.sqrt (2*b/(n+3:ℕ))) ≤ Real.sqrt (2*b)*ε:=by
    rw [Real.sqrt_div (by positivity : 0 ≤ 2*b)]
    calc
      _=Real.sqrt (2*b)*(1/Real.sqrt (n+3:ℕ)):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg (abs_nonneg _) _)) (by positivity)
  have hMeanScale:Cm*|overlap x y|^(μ.minDegree-2) ≤ Cm*ε:=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hCm.le
  have hScaleq:=Real.rpow_le_rpow (by positivity : 0 ≤ Real.sqrt (2*b/(n+3:ℕ))) hScale hq
  have hMeanq:=Real.rpow_le_rpow (by positivity : 0 ≤ Cm*|overlap x y|^(μ.minDegree-2)) hMeanScale hq
  rw [Real.mul_rpow (by positivity) hε] at hScaleq hMeanq
  have hCornerBound:(∫ J,|C J|^q ∂P) ≤ Cc*ε^q:=by
    exact (hCmom.2.trans (mul_le_mul_of_nonneg_left (add_le_add
      (hCorner.2.trans (mul_le_mul_of_nonneg_left hScaleq (by unfold gaussianNormRealMomentConstant;positivity))) hMeanq)
      (by positivity))).trans_eq (by dsimp only [Cc];ring)
  have hW:‖w‖ ≤ (4*M)*Real.sqrt (n+3:ℕ):=mixedPairTarget_norm_le _ _ hh1 hk1 hh2 hk2
  have hRmom:=hn ℓ x y v hx hy hv hvtan e he htanx htany hve f g hg hrOne hA hinv w hW k1 hk
  have hGmom:Integrable (fun J=>|G J|^q) P:=by simpa only [G,abs_neg] using hRmom.1
  have hDiff (J):|F J-G J|^q=|C J|^q:=by
    have heq:F J-G J=-C J:=by dsimp only [F,G,R,C,actualClippedSchurFactor,physicalSchurMultiplier];ring
    rw [heq,abs_neg]
  have hDiffI:Integrable (fun J=>|F J-G J|^q) P:=by simpa only [hDiff] using hCmom.1
  have hκ:0<κ:=mul_pos (scaleFactor_pos n (by omega) hb) hρ
  have hFMeas:Measurable F:=(actualClippedSchurFactor_measurable c x e v k1 hκ).sub_const _
  have hFinal:=integral_absolute_moment_difference P F G hFMeas q hq hGmom hDiffI
  refine ⟨hFinal.1,hFinal.2.trans ?_⟩
  have hGI:(∫ J,|G J|^q ∂P) ≤ Cr*ε^q:=by simpa only [G,abs_neg] using hRmom.2
  have hDI:(∫ J,|F J-G J|^q ∂P) ≤ Cc*ε^q:=by simpa only [hDiff] using hCornerBound
  exact (mul_le_mul_of_nonneg_left (add_le_add hGI hDI) (by positivity)).trans_eq (by dsimp only [ε];ring)

end
end SlowEquilibration.SphericalCommonHessianRegression
