-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianSourceNormalizedBorderError
public import SlowEquilibration.SphericalPosteriorCommonRightMarginal
public import SlowEquilibration.PosteriorBulkDeterminantFactorization
public import SlowEquilibration.PairPosteriorSymmetry
public import SlowEquilibration.PairDependentProductComparison

/-! Actual source complete dependent bordered determinant factorization
in the Schur-weighted bulk means. Only the common bulk is compared by
Gebelein; actual same-space L2 full/bulk errors control both borders. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open GaussianObservationCoercivity NormalizedPairObservations PairObservationNormBounds
open PairObservationTargets PairObservationSmallOverlap PairConditionalDeterminantMoments
open GOEClippedResolvent GOEPhysicalPotential GOERawMoments GOEScaling
open PhysicalCommonBorderMoments PairSchurExpectation BorderSchurExpectation BoundedQuadraticConvergence
open SphericalTwoPointCovariance GaussianQuadraticVariance
open scoped RealInnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

lemma flatNormalizedProduct_actual_common {N P n:ℕ} (c:Degree P→ℝ) (x y:Vector N)
    (e:Fin (n+1)→Vector N) (k1 k2:ℝ) (J:Disorder N P) :
    flatNormalizedProduct n N (secondCovariance c 1) k1 k2
      (actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)) J)=
    (GOERawMoments.matrixAbsoluteDet n k1 (hessianMatrix c x e J)/physicalMean n N (secondCovariance c 1) k1)*
      (GOERawMoments.matrixAbsoluteDet n k2 (hessianMatrix c y e J)/physicalMean n N (secondCovariance c 1) k2):=by
  change (GOERawMoments.matrixAbsoluteDet n k1 (unflattenMatrix (n+1) (actualObservation (flatHessianCLM c x e) J))/_)*
    (GOERawMoments.matrixAbsoluteDet n k2 (unflattenMatrix (n+1) (actualObservation (flatHessianCLM c y e) J))/_)=_
  rw [unflattenMatrix_actual_hessian,unflattenMatrix_actual_hessian]

/-- True source mixed product error. Constants precede dimension, pair,
all deterministic frames and physical marks; no full-product rate is a premise. -/
theorem source_mixed_Schur_normalized_product_factorization (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap) :
    ∃ η C:ℝ,0<η ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x y v1 v2:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ))
      (_hv1:‖v1‖=1) (_hv2:‖v2‖=1) (_hv1tan:inner ℝ v1 x=0) (_hv2tan:inner ℝ v2 y=0)
      (e:Fin (n+1)→Vector (n+3)) (_he:Orthonormal ℝ e)
      (_htanx:∀ i,inner ℝ (e i) x=0) (_htany:∀ i,inner ℝ (e i) y=0)
      (_hve1:∀ i,inner ℝ (e i) v1=0) (_hve2:∀ i,inner ℝ (e i) v2=0)
      (f g:Fin ℓ→Vector (n+3)) (_hf:Orthonormal ℝ f) (_hg:Orthonormal ℝ g)
      (_hftan:∀ i,inner ℝ (f i) x=0) (_hgtan:∀ i,inner ℝ (g i) y=0)
      (h1 k1 h2 k2:ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1)+gap ≤ k1 →
      2*Real.sqrt (secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1)+gap ≤ k2 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
      let w:=mixedPairTarget (n+3) ℓ h1 k1 h2 k2
      let b:=secondCovariance c 1
      let F1:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v1))
        (actualObservation (commonRowCLM c x e v1)) J/(physicalSchurMultiplier b k1*physicalMean n (n+3) b k1)
      let F2:=fun J=>fullBorder (hessianMatrix c y e) k2 (actualObservation (cornerCLM c y v2))
        (actualObservation (commonRowCLM c y e v2)) J/(physicalSchurMultiplier b k2*physicalMean n (n+3) b k2)
      Integrable (fun J=>F1 J*F2 J) (coefficientKernel A w) ∧
        |(∫ J,F1 J*F2 J ∂coefficientKernel A w)-1| ≤ C*(|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)):=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=secondCovariance c 1
  have hc:∀ p,0 ≤ c p:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hdeg:∀ p,c p≠0 → μ.minDegree ≤ p.val.val:=center_degree_min μ Q
  have hdeg3:∀ p,c p≠0 → 3 ≤ p.val.val:=fun p hp=>le_trans (by omega) (hdeg p hp)
  have hb:0<b:=by dsimp only [b,c];rw [secondCovariance_center,secondCovariance_mixture];exact mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨η0,δ,hη0,hδ,hObs⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hd
  obtain ⟨ηe,Ke,hηe,hKe,hError⟩:=source_mixed_normalized_border_q_error μ hQ hnp hd hM hgap (2:ℝ) (by norm_num)
  obtain ⟨Kb,hKb,hBulk⟩:=posterior_bulk_product_mixed_factorization (Z:=M) c hc hdeg3 hb hgap 2
  let KB:=(2:ℝ)^2*Real.exp (16*b/gap^2)
  let KF:=2*KB+8*Ke
  let K:=Real.sqrt Ke*Real.sqrt KF+Real.sqrt KB*Real.sqrt Ke+Kb*profileBound c/b
  have hKB:0<KB:=by dsimp only [KB];positivity
  have hKF:0<KF:=by dsimp only [KF];positivity
  have hK:0 ≤ K:=by dsimp only [K];positivity [profileBound_pos c]
  refine ⟨min η0 (min ηe 1),1+K,lt_min hη0 (lt_min hηe (by norm_num)),by positivity,?_⟩
  filter_upwards [hError,GOESharpMoments.goe_determinant_moments_eventually hb hgap] with n hn hRaw
  intro ℓ x y v1 v2 hx hy hv1 hv2 hv1tan hv2tan e he htanx htany hve1 hve2 f g hf hg hftan hgtan h1 k1 h2 k2 hh1 hk1M hh2 hk2M hr hk1 hk2
  dsimp only
  have hr0:|overlap x y| ≤ η0:=hr.trans (min_le_left _ _)
  have hre:|overlap x y| ≤ ηe:=hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrOne:|overlap x y| ≤ 1:=hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hObs0:=hObs (n+3) ℓ (by omega) x y hx hy f g hf hg hftan hgtan hr0
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  let w:=mixedPairTarget (n+3) ℓ h1 k1 h2 k2
  let P:=coefficientKernel A w
  let m1:=physicalMean n (n+3) b k1
  let m2:=physicalMean n (n+3) b k2
  let s1:=physicalSchurMultiplier b k1
  let s2:=physicalSchurMultiplier b k2
  let F1:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v1))
    (actualObservation (commonRowCLM c x e v1)) J/(s1*m1)
  let F2:=fun J=>fullBorder (hessianMatrix c y e) k2 (actualObservation (cornerCLM c y v2))
    (actualObservation (commonRowCLM c y e v2)) J/(s2*m2)
  let B1:=fun J=>GOERawMoments.matrixAbsoluteDet n k1 (hessianMatrix c x e J)/m1
  let B2:=fun J=>GOERawMoments.matrixAbsoluteDet n k2 (hessianMatrix c y e J)/m2
  let ε:=|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hε:0 ≤ ε:=by dsimp only [ε];positivity
  have hεTwo:ε ≤ 2:=by
    have hp:|overlap x y|^(μ.minDegree-2) ≤ 1:=pow_le_one₀ (abs_nonneg _) hrOne
    have hi:1/Real.sqrt (n+3:ℕ) ≤ 1:=by
      apply (div_le_one (by positivity : 0<Real.sqrt (n+3:ℕ))).mpr
      exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_cast;omega)
    dsimp only [ε]
    linarith
  have hSwap:=coefficientKernel_pair_swap _ _ hObs0.2.1 w
  change coefficientKernel (pairHilbert (singleMixedObservation c y g) (singleMixedObservation c x f)) (mixedPairTarget (n+3) ℓ h2 k2 h1 k1)=P at hSwap
  have hErr1:=hn ℓ x y v1 hx hy hv1 hv1tan e he htanx htany hve1 f g hf hg hftan hgtan h1 k1 h2 k2 hh1 hk1M hh2 hk2M hre hk1
  have hErr2:=hn ℓ y x v2 hy hx hv2 hv2tan e he htany htanx hve2 g f hg hf hgtan hftan h2 k2 h1 k1 hh2 hk2M hh1 hk1M
    (by simpa only [overlap_comm] using hre) hk2
  dsimp only at hErr2
  rw [hSwap,overlap_comm x y] at hErr2
  have hEI1:Integrable (fun J=>(F1 J-B1 J)^2) P:=by simpa only [Real.rpow_two,sq_abs] using hErr1.1
  have hEI2:Integrable (fun J=>(F2 J-B2 J)^2) P:=by simpa only [Real.rpow_two,sq_abs] using hErr2.1
  have hEM1:(∫ J,(F1 J-B1 J)^2 ∂P) ≤ Ke*ε^2:=by simpa only [Real.rpow_two,sq_abs] using hErr1.2
  have hEM2:(∫ J,(F2 J-B2 J)^2 ∂P) ≤ Ke*ε^2:=by simpa only [Real.rpow_two,sq_abs] using hErr2.2
  have hkM1:k1 ≤ M:=(le_abs_self _).trans hk1M
  have hkM2:k2 ≤ M:=(le_abs_self _).trans hk2M
  have hLaw1:=posterior_common_matrix_mixed_hasLaw (by omega) c hc hdeg3 x y hx e he htanx htany f g w
  have hLaw2:=posterior_common_matrix_right_mixed_hasLaw (by omega) c hc hdeg3 x y hy e he htanx htany f g w
  have hRaw1:=(hRaw (n+3) (by omega) k1 hk1).2.2 (2:ℝ) (by norm_num)
  have hRaw2:=(hRaw (n+3) (by omega) k2 hk2).2.2 (2:ℝ) (by norm_num)
  have hBI1:Integrable (fun J=>B1 J^2) P:=by
    simpa only [Function.comp_def,B1,m1,b,physicalMean,Real.rpow_two,GOESharpMoments.matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet] using hLaw1.integrable_fun_comp hRaw1.1
  have hBI2:Integrable (fun J=>B2 J^2) P:=by
    simpa only [Function.comp_def,B2,m2,b,physicalMean,Real.rpow_two,GOESharpMoments.matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet] using hLaw2.integrable_fun_comp hRaw2.1
  have hBM1:(∫ J,B1 J^2 ∂P) ≤ KB:=by
    have hh:=hLaw1.integral_comp (((GOERawMoments.matrixAbsoluteDet_measurable n k1).div_const m1).pow_const (2:ℕ)).aestronglyMeasurable
    change (∫ J,B1 J^2 ∂P)=_ at hh
    rw [hh]
    simpa only [KB,m1,b,physicalMean,Real.rpow_two,GOESharpMoments.matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet,show 4*secondCovariance c 1*(2:ℝ)^2/gap^2=16*secondCovariance c 1/gap^2 by ring] using hRaw1.2
  have hBM2:(∫ J,B2 J^2 ∂P) ≤ KB:=by
    have hh:=hLaw2.integral_comp (((GOERawMoments.matrixAbsoluteDet_measurable n k2).div_const m2).pow_const (2:ℕ)).aestronglyMeasurable
    change (∫ J,B2 J^2 ∂P)=_ at hh
    rw [hh]
    simpa only [KB,m2,b,physicalMean,Real.rpow_two,GOESharpMoments.matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet,show 4*secondCovariance c 1*(2:ℝ)^2/gap^2=16*secondCovariance c 1/gap^2 by ring] using hRaw2.2
  have hFM1:Measurable F1:=(fullBorder_measurable (tensor_hessianMatrix_measurable c x e) k1
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)).div_const _
  have hFM2:Measurable F2:=(fullBorder_measurable (tensor_hessianMatrix_measurable c y e) k2
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)).div_const _
  have hBM1meas:Measurable B1:=((GOERawMoments.matrixAbsoluteDet_measurable n k1).comp (tensor_hessianMatrix_measurable c x e)).div_const _
  have hBM2meas:Measurable B2:=((GOERawMoments.matrixAbsoluteDet_measurable n k2).comp (tensor_hessianMatrix_measurable c y e)).div_const _
  have hFI1:Integrable (fun J=>F1 J^2) P:=(integral_square_difference_bound P F1 B1 hFM1 hBI1 hEI1).1
  have hFI2:Integrable (fun J=>F2 J^2) P:=(integral_square_difference_bound P F2 B2 hFM2 hBI2 hEI2).1
  have hFbound:(∫ J,F2 J^2 ∂P) ≤ KF:=by
    have hh:=(integral_square_difference_bound P F2 B2 hFM2 hBI2 hEI2).2
    exact hh.trans (by dsimp only [KF];nlinarith [hEM2,hBM2,mul_le_mul_of_nonneg_left (show ε^2 ≤ 4 by nlinarith) hKe.le])
  have hF1Lp:MemLp F1 2 P:=(memLp_two_iff_integrable_sq hFM1.aestronglyMeasurable).mpr hFI1
  have hF2Lp:MemLp F2 2 P:=(memLp_two_iff_integrable_sq hFM2.aestronglyMeasurable).mpr hFI2
  have hB1Lp:MemLp B1 2 P:=(memLp_two_iff_integrable_sq hBM1meas.aestronglyMeasurable).mpr hBI1
  have hB2Lp:MemLp B2 2 P:=(memLp_two_iff_integrable_sq hBM2meas.aestronglyMeasurable).mpr hBI2
  have hComp:=dependent_product_comparison P F1 F2 B1 B2 hF1Lp hF2Lp hB1Lp hB2Lp
  have hEroot1:Real.sqrt (∫ J,(F1 J-B1 J)^2 ∂P) ≤ Real.sqrt Ke*ε:=by
    have hh:=Real.sqrt_le_sqrt hEM1
    rw [Real.sqrt_mul hKe.le,Real.sqrt_sq hε] at hh
    exact hh
  have hEroot2:Real.sqrt (∫ J,(F2 J-B2 J)^2 ∂P) ≤ Real.sqrt Ke*ε:=by
    have hh:=Real.sqrt_le_sqrt hEM2
    rw [Real.sqrt_mul hKe.le,Real.sqrt_sq hε] at hh
    exact hh
  have hCompBound:(∫ J,|F1 J*F2 J-B1 J*B2 J| ∂P) ≤
      (Real.sqrt Ke*Real.sqrt KF+Real.sqrt KB*Real.sqrt Ke)*ε:=by
    refine hComp.2.trans ?_
    calc
      _ ≤ (Real.sqrt Ke*ε)*Real.sqrt KF+Real.sqrt KB*(Real.sqrt Ke*ε):=by gcongr
      _=_:=by ring
  have hBulkActual:=hBulk n ℓ x y hx hy e he htanx htany hrOne f g w hObs0.2.1 k1 k2 hk1 hkM1 hk2 hkM2
  simp only [flatNormalizedProduct_actual_common] at hBulkActual
  have hCorr:|hessianCorrelation c (overlap x y)| ≤ (profileBound c/b)*|overlap x y|^(μ.minDegree-2):=by
    rw [hessianCorrelation,abs_div,abs_of_pos hb]
    exact (div_le_div_of_nonneg_right (profile_order_common c μ.minDegree hdeg hrOne).2.2.1 hb.le).trans_eq (by ring)
  have hBulkBound:|(∫ J,B1 J*B2 J ∂P)-1| ≤ (Kb*profileBound c/b)*ε:=by
    have hh:=hBulkActual.2.trans (mul_le_mul_of_nonneg_left hCorr hKb.le)
    refine hh.trans ?_
    calc
      Kb*(profileBound c/b*|overlap x y|^(μ.minDegree-2)) = (Kb*profileBound c/b)*|overlap x y|^(μ.minDegree-2):=by ring
      _ ≤ (Kb*profileBound c/b)*ε:=mul_le_mul_of_nonneg_left
        (by dsimp only [ε];exact le_add_of_nonneg_right (by positivity)) (by positivity [profileBound_pos c])
  have hProdI:Integrable (fun J=>F1 J*F2 J) P:=memLp_one_iff_integrable.mp (hF1Lp.mul hF2Lp)
  have hBProdI:Integrable (fun J=>B1 J*B2 J) P:=memLp_one_iff_integrable.mp (hB1Lp.mul hB2Lp)
  have hNorm:=norm_integral_le_integral_norm (fun J=>F1 J*F2 J-B1 J*B2 J) (μ:=P)
  rw [integral_sub hProdI hBProdI,Real.norm_eq_abs] at hNorm
  have hDiff:|(∫ J,F1 J*F2 J ∂P)-(∫ J,B1 J*B2 J ∂P)| ≤
      (Real.sqrt Ke*Real.sqrt KF+Real.sqrt KB*Real.sqrt Ke)*ε:=by
    exact hNorm.trans (by simpa only [Real.norm_eq_abs] using hCompBound)
  refine ⟨hProdI,?_⟩
  have hh:=abs_add_le ((∫ J,F1 J*F2 J ∂P)-(∫ J,B1 J*B2 J ∂P)) ((∫ J,B1 J*B2 J ∂P)-1)
  rw [sub_add_sub_cancel] at hh
  exact (hh.trans (add_le_add hDiff hBulkBound)).trans
    (by dsimp only [K];nlinarith [hε])

/-- True source value product error. Constants precede dimension, pair,
all deterministic frames and physical marks; no full-product rate is a premise. -/
theorem source_value_Schur_normalized_product_factorization (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap) :
    ∃ η C:ℝ,0<η ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,∀ (ℓ:ℕ)
      (x y v1 v2:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ))
      (_hv1:‖v1‖=1) (_hv2:‖v2‖=1) (_hv1tan:inner ℝ v1 x=0) (_hv2tan:inner ℝ v2 y=0)
      (e:Fin (n+1)→Vector (n+3)) (_he:Orthonormal ℝ e)
      (_htanx:∀ i,inner ℝ (e i) x=0) (_htany:∀ i,inner ℝ (e i) y=0)
      (_hve1:∀ i,inner ℝ (e i) v1=0) (_hve2:∀ i,inner ℝ (e i) v2=0)
      (f g:Fin ℓ→Vector (n+3)) (_hf:Orthonormal ℝ f) (_hg:Orthonormal ℝ g)
      (_hftan:∀ i,inner ℝ (f i) x=0) (_hgtan:∀ i,inner ℝ (g i) y=0)
      (h1 h2 k1 k2:ℝ),|h1| ≤ M → |h2| ≤ M → |k1| ≤ M → |k2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1)+gap ≤ k1 →
      2*Real.sqrt (secondCovariance (centerCoefficients (mixtureCoefficients μ) Q) 1)+gap ≤ k2 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
      let w:=valuePairTarget (n+3) ℓ h1 h2
      let b:=secondCovariance c 1
      let F1:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v1))
        (actualObservation (commonRowCLM c x e v1)) J/(physicalSchurMultiplier b k1*physicalMean n (n+3) b k1)
      let F2:=fun J=>fullBorder (hessianMatrix c y e) k2 (actualObservation (cornerCLM c y v2))
        (actualObservation (commonRowCLM c y e v2)) J/(physicalSchurMultiplier b k2*physicalMean n (n+3) b k2)
      Integrable (fun J=>F1 J*F2 J) (coefficientKernel A w) ∧
        |(∫ J,F1 J*F2 J ∂coefficientKernel A w)-1| ≤ C*(|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)):=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let b:=secondCovariance c 1
  have hc:∀ p,0 ≤ c p:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hdeg:∀ p,c p≠0 → μ.minDegree ≤ p.val.val:=center_degree_min μ Q
  have hdeg3:∀ p,c p≠0 → 3 ≤ p.val.val:=fun p hp=>le_trans (by omega) (hdeg p hp)
  have hb:0<b:=by dsimp only [b,c];rw [secondCovariance_center,secondCovariance_mixture];exact mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨η0,δ,hη0,hδ,hObs⟩:=uniform_value_pair_nondegenerate μ hQ hd
  obtain ⟨ηe,Ke,hηe,hKe,hError⟩:=source_value_normalized_border_q_error μ hQ hd hM hgap (2:ℝ) (by norm_num)
  obtain ⟨Kb,hKb,hBulk⟩:=posterior_bulk_product_value_factorization (Z:=M) c hc hdeg3 hb hgap 2
  let KB:=(2:ℝ)^2*Real.exp (16*b/gap^2)
  let KF:=2*KB+8*Ke
  let K:=Real.sqrt Ke*Real.sqrt KF+Real.sqrt KB*Real.sqrt Ke+Kb*profileBound c/b
  have hKB:0<KB:=by dsimp only [KB];positivity
  have hKF:0<KF:=by dsimp only [KF];positivity
  have hK:0 ≤ K:=by dsimp only [K];positivity [profileBound_pos c]
  refine ⟨min η0 (min ηe 1),1+K,lt_min hη0 (lt_min hηe (by norm_num)),by positivity,?_⟩
  filter_upwards [hError,GOESharpMoments.goe_determinant_moments_eventually hb hgap] with n hn hRaw
  intro ℓ x y v1 v2 hx hy hv1 hv2 hv1tan hv2tan e he htanx htany hve1 hve2 f g hf hg hftan hgtan h1 h2 k1 k2 hh1 hh2 hk1M hk2M hr hk1 hk2
  dsimp only
  have hr0:|overlap x y| ≤ η0:=hr.trans (min_le_left _ _)
  have hre:|overlap x y| ≤ ηe:=hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrOne:|overlap x y| ≤ 1:=hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hObs0:=hObs (n+3) ℓ (by omega) x y hx hy f g hf hg hftan hgtan hr0
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let w:=valuePairTarget (n+3) ℓ h1 h2
  let P:=coefficientKernel A w
  let m1:=physicalMean n (n+3) b k1
  let m2:=physicalMean n (n+3) b k2
  let s1:=physicalSchurMultiplier b k1
  let s2:=physicalSchurMultiplier b k2
  let F1:=fun J=>fullBorder (hessianMatrix c x e) k1 (actualObservation (cornerCLM c x v1))
    (actualObservation (commonRowCLM c x e v1)) J/(s1*m1)
  let F2:=fun J=>fullBorder (hessianMatrix c y e) k2 (actualObservation (cornerCLM c y v2))
    (actualObservation (commonRowCLM c y e v2)) J/(s2*m2)
  let B1:=fun J=>GOERawMoments.matrixAbsoluteDet n k1 (hessianMatrix c x e J)/m1
  let B2:=fun J=>GOERawMoments.matrixAbsoluteDet n k2 (hessianMatrix c y e J)/m2
  let ε:=|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hε:0 ≤ ε:=by dsimp only [ε];positivity
  have hεTwo:ε ≤ 2:=by
    have hp:|overlap x y|^(μ.minDegree-2) ≤ 1:=pow_le_one₀ (abs_nonneg _) hrOne
    have hi:1/Real.sqrt (n+3:ℕ) ≤ 1:=by
      apply (div_le_one (by positivity : 0<Real.sqrt (n+3:ℕ))).mpr
      exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_cast;omega)
    dsimp only [ε]
    linarith
  have hSwap:=coefficientKernel_pair_swap _ _ hObs0.2.1 w
  change coefficientKernel (pairHilbert (singleValueObservation c y g) (singleValueObservation c x f)) (valuePairTarget (n+3) ℓ h2 h1)=P at hSwap
  have hErr1:=hn ℓ x y v1 hx hy hv1 hv1tan e he htanx htany hve1 f g hf hg hftan hgtan h1 h2 k1 hh1 hh2 hk1M hre hk1
  have hErr2:=hn ℓ y x v2 hy hx hv2 hv2tan e he htany htanx hve2 g f hg hf hgtan hftan h2 h1 k2 hh2 hh1 hk2M
    (by simpa only [overlap_comm] using hre) hk2
  dsimp only at hErr2
  rw [hSwap,overlap_comm x y] at hErr2
  have hEI1:Integrable (fun J=>(F1 J-B1 J)^2) P:=by simpa only [Real.rpow_two,sq_abs] using hErr1.1
  have hEI2:Integrable (fun J=>(F2 J-B2 J)^2) P:=by simpa only [Real.rpow_two,sq_abs] using hErr2.1
  have hEM1:(∫ J,(F1 J-B1 J)^2 ∂P) ≤ Ke*ε^2:=by simpa only [Real.rpow_two,sq_abs] using hErr1.2
  have hEM2:(∫ J,(F2 J-B2 J)^2 ∂P) ≤ Ke*ε^2:=by simpa only [Real.rpow_two,sq_abs] using hErr2.2
  have hkM1:k1 ≤ M:=(le_abs_self _).trans hk1M
  have hkM2:k2 ≤ M:=(le_abs_self _).trans hk2M
  have hLaw1:=posterior_common_matrix_value_hasLaw (by omega) c hc hdeg3 x y hx e he htanx htany f g w
  have hLaw2:=posterior_common_matrix_right_value_hasLaw (by omega) c hc hdeg3 x y hy e he htanx htany f g w
  have hRaw1:=(hRaw (n+3) (by omega) k1 hk1).2.2 (2:ℝ) (by norm_num)
  have hRaw2:=(hRaw (n+3) (by omega) k2 hk2).2.2 (2:ℝ) (by norm_num)
  have hBI1:Integrable (fun J=>B1 J^2) P:=by
    simpa only [Function.comp_def,B1,m1,b,physicalMean,Real.rpow_two,GOESharpMoments.matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet] using hLaw1.integrable_fun_comp hRaw1.1
  have hBI2:Integrable (fun J=>B2 J^2) P:=by
    simpa only [Function.comp_def,B2,m2,b,physicalMean,Real.rpow_two,GOESharpMoments.matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet] using hLaw2.integrable_fun_comp hRaw2.1
  have hBM1:(∫ J,B1 J^2 ∂P) ≤ KB:=by
    have hh:=hLaw1.integral_comp (((GOERawMoments.matrixAbsoluteDet_measurable n k1).div_const m1).pow_const (2:ℕ)).aestronglyMeasurable
    change (∫ J,B1 J^2 ∂P)=_ at hh
    rw [hh]
    simpa only [KB,m1,b,physicalMean,Real.rpow_two,GOESharpMoments.matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet,show 4*secondCovariance c 1*(2:ℝ)^2/gap^2=16*secondCovariance c 1/gap^2 by ring] using hRaw1.2
  have hBM2:(∫ J,B2 J^2 ∂P) ≤ KB:=by
    have hh:=hLaw2.integral_comp (((GOERawMoments.matrixAbsoluteDet_measurable n k2).div_const m2).pow_const (2:ℕ)).aestronglyMeasurable
    change (∫ J,B2 J^2 ∂P)=_ at hh
    rw [hh]
    simpa only [KB,m2,b,physicalMean,Real.rpow_two,GOESharpMoments.matrixAbsoluteDet,GOERawMoments.matrixAbsoluteDet,show 4*secondCovariance c 1*(2:ℝ)^2/gap^2=16*secondCovariance c 1/gap^2 by ring] using hRaw2.2
  have hFM1:Measurable F1:=(fullBorder_measurable (tensor_hessianMatrix_measurable c x e) k1
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)).div_const _
  have hFM2:Measurable F2:=(fullBorder_measurable (tensor_hessianMatrix_measurable c y e) k2
    (actual_linearObservation_measurable _) (actual_linearObservation_measurable _)).div_const _
  have hBM1meas:Measurable B1:=((GOERawMoments.matrixAbsoluteDet_measurable n k1).comp (tensor_hessianMatrix_measurable c x e)).div_const _
  have hBM2meas:Measurable B2:=((GOERawMoments.matrixAbsoluteDet_measurable n k2).comp (tensor_hessianMatrix_measurable c y e)).div_const _
  have hFI1:Integrable (fun J=>F1 J^2) P:=(integral_square_difference_bound P F1 B1 hFM1 hBI1 hEI1).1
  have hFI2:Integrable (fun J=>F2 J^2) P:=(integral_square_difference_bound P F2 B2 hFM2 hBI2 hEI2).1
  have hFbound:(∫ J,F2 J^2 ∂P) ≤ KF:=by
    have hh:=(integral_square_difference_bound P F2 B2 hFM2 hBI2 hEI2).2
    exact hh.trans (by dsimp only [KF];nlinarith [hEM2,hBM2,mul_le_mul_of_nonneg_left (show ε^2 ≤ 4 by nlinarith) hKe.le])
  have hF1Lp:MemLp F1 2 P:=(memLp_two_iff_integrable_sq hFM1.aestronglyMeasurable).mpr hFI1
  have hF2Lp:MemLp F2 2 P:=(memLp_two_iff_integrable_sq hFM2.aestronglyMeasurable).mpr hFI2
  have hB1Lp:MemLp B1 2 P:=(memLp_two_iff_integrable_sq hBM1meas.aestronglyMeasurable).mpr hBI1
  have hB2Lp:MemLp B2 2 P:=(memLp_two_iff_integrable_sq hBM2meas.aestronglyMeasurable).mpr hBI2
  have hComp:=dependent_product_comparison P F1 F2 B1 B2 hF1Lp hF2Lp hB1Lp hB2Lp
  have hEroot1:Real.sqrt (∫ J,(F1 J-B1 J)^2 ∂P) ≤ Real.sqrt Ke*ε:=by
    have hh:=Real.sqrt_le_sqrt hEM1
    rw [Real.sqrt_mul hKe.le,Real.sqrt_sq hε] at hh
    exact hh
  have hEroot2:Real.sqrt (∫ J,(F2 J-B2 J)^2 ∂P) ≤ Real.sqrt Ke*ε:=by
    have hh:=Real.sqrt_le_sqrt hEM2
    rw [Real.sqrt_mul hKe.le,Real.sqrt_sq hε] at hh
    exact hh
  have hCompBound:(∫ J,|F1 J*F2 J-B1 J*B2 J| ∂P) ≤
      (Real.sqrt Ke*Real.sqrt KF+Real.sqrt KB*Real.sqrt Ke)*ε:=by
    refine hComp.2.trans ?_
    calc
      _ ≤ (Real.sqrt Ke*ε)*Real.sqrt KF+Real.sqrt KB*(Real.sqrt Ke*ε):=by gcongr
      _=_:=by ring
  have hBulkActual:=hBulk n ℓ x y hx hy e he htanx htany hrOne f g w hObs0.2.1 k1 k2 hk1 hkM1 hk2 hkM2
  simp only [flatNormalizedProduct_actual_common] at hBulkActual
  have hCorr:|hessianCorrelation c (overlap x y)| ≤ (profileBound c/b)*|overlap x y|^(μ.minDegree-2):=by
    rw [hessianCorrelation,abs_div,abs_of_pos hb]
    exact (div_le_div_of_nonneg_right (profile_order_common c μ.minDegree hdeg hrOne).2.2.1 hb.le).trans_eq (by ring)
  have hBulkBound:|(∫ J,B1 J*B2 J ∂P)-1| ≤ (Kb*profileBound c/b)*ε:=by
    have hh:=hBulkActual.2.trans (mul_le_mul_of_nonneg_left hCorr hKb.le)
    refine hh.trans ?_
    calc
      Kb*(profileBound c/b*|overlap x y|^(μ.minDegree-2)) = (Kb*profileBound c/b)*|overlap x y|^(μ.minDegree-2):=by ring
      _ ≤ (Kb*profileBound c/b)*ε:=mul_le_mul_of_nonneg_left
        (by dsimp only [ε];exact le_add_of_nonneg_right (by positivity)) (by positivity [profileBound_pos c])
  have hProdI:Integrable (fun J=>F1 J*F2 J) P:=memLp_one_iff_integrable.mp (hF1Lp.mul hF2Lp)
  have hBProdI:Integrable (fun J=>B1 J*B2 J) P:=memLp_one_iff_integrable.mp (hB1Lp.mul hB2Lp)
  have hNorm:=norm_integral_le_integral_norm (fun J=>F1 J*F2 J-B1 J*B2 J) (μ:=P)
  rw [integral_sub hProdI hBProdI,Real.norm_eq_abs] at hNorm
  have hDiff:|(∫ J,F1 J*F2 J ∂P)-(∫ J,B1 J*B2 J ∂P)| ≤
      (Real.sqrt Ke*Real.sqrt KF+Real.sqrt KB*Real.sqrt Ke)*ε:=by
    exact hNorm.trans (by simpa only [Real.norm_eq_abs] using hCompBound)
  refine ⟨hProdI,?_⟩
  have hh:=abs_add_le ((∫ J,F1 J*F2 J ∂P)-(∫ J,B1 J*B2 J ∂P)) ((∫ J,B1 J*B2 J ∂P)-1)
  rw [sub_add_sub_cancel] at hh
  exact (hh.trans (add_le_add hDiff hBulkBound)).trans
    (by dsimp only [K];nlinarith [hε])

end
end SlowEquilibration.SphericalCommonHessianRegression
